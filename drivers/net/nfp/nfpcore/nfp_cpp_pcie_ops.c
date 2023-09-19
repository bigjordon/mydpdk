/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2018 Netronome Systems, Inc.
 * All rights reserved.
 */

/*
 * nfp_cpp_pcie_ops.c
 * Authors: Vinayak Tammineedi <vinayak.tammineedi@netronome.com>
 *
 * Multiplexes the NFP BARs between NFP internal resources and
 * implements the PCIe specific interface for generic CPP bus access.
 *
 * The BARs are managed and allocated if they are available.
 * The generic CPP bus abstraction builds upon this BAR interface.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include <fcntl.h>
#include <string.h>
#include <errno.h>
#include <dirent.h>
#include <libgen.h>

#include <sys/mman.h>
#include <sys/file.h>
#include <sys/stat.h>

#include <ethdev_pci.h>

#include "nfp_cpp.h"
#include "nfp_logs.h"
#include "nfp6000/nfp6000.h"
#include "../nfp_logs.h"

#define NFP_PCIE_BAR(_pf)        (0x30000 + ((_pf) & 7) * 0xc0)

#define NFP_PCIE_BAR_PCIE2CPP_ACTION_BASEADDRESS(_x)  (((_x) & 0x1f) << 16)
#define NFP_PCIE_BAR_PCIE2CPP_BASEADDRESS(_x)         (((_x) & 0xffff) << 0)
#define NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT(_x)        (((_x) & 0x3) << 27)
#define NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_32BIT    0
#define NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_64BIT    1
#define NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_0BYTE    3
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE(_x)             (((_x) & 0x7) << 29)
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_OF(_x)          (((_x) >> 29) & 0x7)
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_FIXED         0
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_BULK          1
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_TARGET        2
#define NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_GENERAL       3
#define NFP_PCIE_BAR_PCIE2CPP_TARGET_BASEADDRESS(_x)  (((_x) & 0xf) << 23)
#define NFP_PCIE_BAR_PCIE2CPP_TOKEN_BASEADDRESS(_x)   (((_x) & 0x3) << 21)

/*
 * Minimal size of the PCIe cfg memory we depend on being mapped,
 * queue controller and DMA controller don't have to be covered.
 */
#define NFP_PCI_MIN_MAP_SIZE        0x080000        /* 512K */

#define NFP_PCIE_P2C_FIXED_SIZE(bar)               (1 << (bar)->bitsize)
#define NFP_PCIE_P2C_BULK_SIZE(bar)                (1 << (bar)->bitsize)
#define NFP_PCIE_P2C_GENERAL_TARGET_OFFSET(bar, x) ((x) << ((bar)->bitsize - 2))
#define NFP_PCIE_P2C_GENERAL_TOKEN_OFFSET(bar, x) ((x) << ((bar)->bitsize - 4))
#define NFP_PCIE_P2C_GENERAL_SIZE(bar)             (1 << ((bar)->bitsize - 4))

#define NFP_PCIE_CFG_BAR_PCIETOCPPEXPBAR(id, bar, slot) \
	(NFP_PCIE_BAR(id) + ((bar) * 8 + (slot)) * 4)

#define NFP_PCIE_CPP_BAR_PCIETOCPPEXPBAR(bar, slot) \
	(((bar) * 8 + (slot)) * 4)

struct nfp_pcie_user;
struct nfp6000_area_priv;

/* Describes BAR configuration and usage */
#define NFP_BAR_MIN 1
#define NFP_BAR_MID 5
#define NFP_BAR_MAX 7

struct nfp_bar {
	struct nfp_pcie_user *nfp;    /**< Backlink to owner */
	uint32_t barcfg;     /**< BAR config CSR */
	uint64_t base;       /**< Base CPP offset */
	uint64_t mask;       /**< Mask of the BAR aperture (read only) */
	uint32_t bitsize;    /**< Bit size of the BAR aperture (read only) */
	uint32_t index;      /**< Index of the BAR */
	int lock;            /**< If the BAR has been locked */

	char *csr;
	char *iomem;         /**< mapped IO memory */
};

#define BUSDEV_SZ    13
struct nfp_pcie_user {
	struct nfp_bar bar[NFP_BAR_MAX];

	int device;
	int lock;
	char busdev[BUSDEV_SZ];
	int barsz;
	int dev_id;
	char *cfg;
};

static uint32_t
nfp_bar_maptype(struct nfp_bar *bar)
{
	return NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_OF(bar->barcfg);
}

#define TARGET_WIDTH_32    4
#define TARGET_WIDTH_64    8

static int
nfp_compute_bar(const struct nfp_bar *bar,
		uint32_t *bar_config,
		uint64_t *bar_base,
		int target,
		int action,
		int token,
		uint64_t offset,
		size_t size,
		int width)
{
	uint64_t mask;
	uint32_t newcfg;
	uint32_t bitsize;

	if (target >= 16)
		return -EINVAL;

	switch (width) {
	case 8:
		newcfg = NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT
				(NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_64BIT);
		break;
	case 4:
		newcfg = NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT
				(NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_32BIT);
		break;
	case 0:
		newcfg = NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT
				(NFP_PCIE_BAR_PCIE2CPP_LENGTHSELECT_0BYTE);
		break;
	default:
		return -EINVAL;
	}

	if (action != NFP_CPP_ACTION_RW && action != 0) {
		/* Fixed CPP mapping with specific action */
		mask = ~(NFP_PCIE_P2C_FIXED_SIZE(bar) - 1);

		newcfg |= NFP_PCIE_BAR_PCIE2CPP_MAPTYPE
				(NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_FIXED);
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_TARGET_BASEADDRESS(target);
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_ACTION_BASEADDRESS(action);
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_TOKEN_BASEADDRESS(token);

		if ((offset & mask) != ((offset + size - 1) & mask))
			return -EINVAL;

		offset &= mask;
		bitsize = 40 - 16;
	} else {
		mask = ~(NFP_PCIE_P2C_BULK_SIZE(bar) - 1);

		/* Bulk mapping */
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_MAPTYPE
				(NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_BULK);
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_TARGET_BASEADDRESS(target);
		newcfg |= NFP_PCIE_BAR_PCIE2CPP_TOKEN_BASEADDRESS(token);

		if ((offset & mask) != ((offset + size - 1) & mask))
			return -EINVAL;

		offset &= mask;
		bitsize = 40 - 21;
	}

	if (bar->bitsize < bitsize)
		return -EINVAL;

	newcfg |= offset >> bitsize;

	if (bar_base != NULL)
		*bar_base = offset;

	if (bar_config != NULL)
		*bar_config = newcfg;

	return 0;
}

static int
nfp_bar_write(struct nfp_pcie_user *nfp,
		struct nfp_bar *bar,
		uint32_t newcfg)
{
	int base;
	int slot;

	base = bar->index >> 3;
	slot = bar->index & 7;

	if (nfp->cfg == NULL)
		return (-ENOMEM);

	bar->csr = nfp->cfg +
			NFP_PCIE_CFG_BAR_PCIETOCPPEXPBAR(nfp->dev_id, base, slot);

	*(uint32_t *)(bar->csr) = newcfg;

	bar->barcfg = newcfg;

	return 0;
}

static int
nfp_reconfigure_bar(struct nfp_pcie_user *nfp,
		struct nfp_bar *bar,
		int target,
		int action,
		int token,
		uint64_t offset,
		size_t size,
		int width)
{
	int err;
	uint32_t newcfg;
	uint64_t newbase;

	err = nfp_compute_bar(bar, &newcfg, &newbase, target, action,
			token, offset, size, width);
	if (err != 0)
		return err;

	bar->base = newbase;

	return nfp_bar_write(nfp, bar, newcfg);
}

/*
 * Map all PCI bars. We assume that the BAR with the PCIe config block is
 * already mapped.
 *
 * BAR0.0: Reserved for General Mapping (for MSI-X access to PCIe SRAM)
 *
 *         Halving PCItoCPPBars for primary and secondary processes.
 *         For CoreNIC firmware:
 *         NFP PMD just requires two fixed slots, one for configuration BAR,
 *         and another for accessing the hw queues. Another slot is needed
 *         for setting the link up or down. Secondary processes do not need
 *         to map the first two slots again, but it requires one slot for
 *         accessing the link, even if it is not likely the secondary process
 *         starting the port.
 *         For Flower firmware:
 *         NFP PMD need another fixed slots, used as the configureation BAR
 *         for ctrl vNIC.
 */
static int
nfp_enable_bars(struct nfp_pcie_user *nfp)
{
	int x;
	int end;
	int start;
	struct nfp_bar *bar;

	if (rte_eal_process_type() == RTE_PROC_PRIMARY) {
		start = NFP_BAR_MID;
		end = NFP_BAR_MIN;
	} else {
		start = NFP_BAR_MAX;
		end = NFP_BAR_MID;
	}

	for (x = start; x > end; x--) {
		bar = &nfp->bar[x - 1];
		bar->barcfg = 0;
		bar->nfp = nfp;
		bar->index = x;
		bar->mask = (1 << (nfp->barsz - 3)) - 1;
		bar->bitsize = nfp->barsz - 3;
		bar->base = 0;
		bar->iomem = NULL;
		bar->lock = 0;
		bar->csr = nfp->cfg + NFP_PCIE_CFG_BAR_PCIETOCPPEXPBAR(nfp->dev_id,
				bar->index >> 3, bar->index & 7);
		bar->iomem = nfp->cfg + (bar->index << bar->bitsize);
	}
	return 0;
}

static struct nfp_bar *
nfp_alloc_bar(struct nfp_pcie_user *nfp)
{
	int x;
	int end;
	int start;
	struct nfp_bar *bar;

	if (rte_eal_process_type() == RTE_PROC_PRIMARY) {
		start = NFP_BAR_MID;
		end = NFP_BAR_MIN;
	} else {
		start = NFP_BAR_MAX;
		end = NFP_BAR_MID;
	}

	for (x = start; x > end; x--) {
		bar = &nfp->bar[x - 1];
		if (bar->lock == 0) {
			bar->lock = 1;
			return bar;
		}
	}

	return NULL;
}

static void
nfp_disable_bars(struct nfp_pcie_user *nfp)
{
	int x;
	int end;
	int start;
	struct nfp_bar *bar;

	if (rte_eal_process_type() == RTE_PROC_PRIMARY) {
		start = NFP_BAR_MID;
		end = NFP_BAR_MIN;
	} else {
		start = NFP_BAR_MAX;
		end = NFP_BAR_MID;
	}

	for (x = start; x > end; x--) {
		bar = &nfp->bar[x - 1];
		if (bar->iomem) {
			bar->iomem = NULL;
			bar->lock = 0;
		}
	}
}

/* Generic CPP bus access interface. */
struct nfp6000_area_priv {
	struct nfp_bar *bar;
	uint32_t bar_offset;

	uint32_t target;
	uint32_t action;
	uint32_t token;
	uint64_t offset;
	struct {
		int read;
		int write;
		int bar;
	} width;
	size_t size;
	char *iomem;
};

static int
nfp6000_area_init(struct nfp_cpp_area *area,
		uint32_t dest,
		uint64_t address,
		size_t size)
{
	int pp;
	int ret = 0;
	uint32_t token = NFP_CPP_ID_TOKEN_of(dest);
	uint32_t target = NFP_CPP_ID_TARGET_of(dest);
	uint32_t action = NFP_CPP_ID_ACTION_of(dest);
	struct nfp6000_area_priv *priv = nfp_cpp_area_priv(area);
	struct nfp_pcie_user *nfp = nfp_cpp_priv(nfp_cpp_area_cpp(area));

	pp = nfp_target_pushpull(NFP_CPP_ID(target, action, token), address);
	if (pp < 0)
		return pp;

	priv->width.read = PUSH_WIDTH(pp);
	priv->width.write = PULL_WIDTH(pp);

	if (priv->width.read > 0 &&
			priv->width.write > 0 &&
			priv->width.read != priv->width.write)
		return -EINVAL;

	if (priv->width.read > 0)
		priv->width.bar = priv->width.read;
	else
		priv->width.bar = priv->width.write;

	priv->bar = nfp_alloc_bar(nfp);
	if (priv->bar == NULL)
		return -ENOMEM;

	priv->target = target;
	priv->action = action;
	priv->token = token;
	priv->offset = address;
	priv->size = size;

	ret = nfp_reconfigure_bar(nfp, priv->bar, priv->target, priv->action,
			priv->token, priv->offset, priv->size,
			priv->width.bar);

	return ret;
}

static int
nfp6000_area_acquire(struct nfp_cpp_area *area)
{
	struct nfp6000_area_priv *priv = nfp_cpp_area_priv(area);

	/* Calculate offset into BAR. */
	if (nfp_bar_maptype(priv->bar) ==
			NFP_PCIE_BAR_PCIE2CPP_MAPTYPE_GENERAL) {
		priv->bar_offset = priv->offset &
				(NFP_PCIE_P2C_GENERAL_SIZE(priv->bar) - 1);
		priv->bar_offset += NFP_PCIE_P2C_GENERAL_TARGET_OFFSET(priv->bar,
				priv->target);
		priv->bar_offset += NFP_PCIE_P2C_GENERAL_TOKEN_OFFSET(priv->bar,
				priv->token);
	} else {
		priv->bar_offset = priv->offset & priv->bar->mask;
	}

	/* Must have been too big. Sub-allocate. */
	if (priv->bar->iomem == NULL)
		return (-ENOMEM);

	priv->iomem = priv->bar->iomem + priv->bar_offset;

	return 0;
}

static void
nfp6000_area_release(struct nfp_cpp_area *area)
{
	struct nfp6000_area_priv *priv = nfp_cpp_area_priv(area);

	priv->bar->lock = 0;
	priv->bar = NULL;
	priv->iomem = NULL;
}

static void *
nfp6000_area_iomem(struct nfp_cpp_area *area)
{
	struct nfp6000_area_priv *priv = nfp_cpp_area_priv(area);
	return priv->iomem;
}

static int
nfp6000_area_read(struct nfp_cpp_area *area,
		void *address,
		uint32_t offset,
		size_t length)
{
	size_t n;
	int width;
	bool is_64;
	uint32_t *wrptr32 = address;
	uint64_t *wrptr64 = address;
	struct nfp6000_area_priv *priv;
	const volatile uint32_t *rdptr32;
	const volatile uint64_t *rdptr64;

	priv = nfp_cpp_area_priv(area);
	rdptr64 = (uint64_t *)(priv->iomem + offset);
	rdptr32 = (uint32_t *)(priv->iomem + offset);

	if (offset + length > priv->size)
		return -EFAULT;

	width = priv->width.read;
	if (width <= 0)
		return -EINVAL;

	/* Unaligned? Translate to an explicit access */
	if (((priv->offset + offset) & (width - 1)) != 0) {
		PMD_DRV_LOG(ERR, "aread_read unaligned!!!");
		return -EINVAL;
	}

	is_64 = width == TARGET_WIDTH_64;

	/* MU reads via a PCIe2CPP BAR supports 32bit (and other) lengths */
	if (priv->target == (NFP_CPP_TARGET_ID_MASK & NFP_CPP_TARGET_MU) &&
			priv->action == NFP_CPP_ACTION_RW) {
		is_64 = false;
	}

	if (is_64) {
		if (offset % sizeof(uint64_t) != 0 ||
				length % sizeof(uint64_t) != 0)
			return -EINVAL;
	} else {
		if (offset % sizeof(uint32_t) != 0 ||
				length % sizeof(uint32_t) != 0)
			return -EINVAL;
	}

	if (priv->bar == NULL)
		return -EFAULT;

	if (is_64)
		for (n = 0; n < length; n += sizeof(uint64_t)) {
			*wrptr64 = *rdptr64;
			wrptr64++;
			rdptr64++;
		}
	else
		for (n = 0; n < length; n += sizeof(uint32_t)) {
			*wrptr32 = *rdptr32;
			wrptr32++;
			rdptr32++;
		}

	return n;
}

static int
nfp6000_area_write(struct nfp_cpp_area *area,
		const void *address,
		uint32_t offset,
		size_t length)
{
	size_t n;
	int width;
	bool is_64;
	uint32_t *wrptr32;
	uint64_t *wrptr64;
	struct nfp6000_area_priv *priv;
	const uint32_t *rdptr32 = address;
	const uint64_t *rdptr64 = address;

	priv = nfp_cpp_area_priv(area);
	wrptr64 = (uint64_t *)(priv->iomem + offset);
	wrptr32 = (uint32_t *)(priv->iomem + offset);

	if (offset + length > priv->size)
		return -EFAULT;

	width = priv->width.write;
	if (width <= 0)
		return -EINVAL;

	/* Unaligned? Translate to an explicit access */
	if (((priv->offset + offset) & (width - 1)) != 0)
		return -EINVAL;

	is_64 = width == TARGET_WIDTH_64;

	/* MU writes via a PCIe2CPP BAR supports 32bit (and other) lengths */
	if (priv->target == (NFP_CPP_TARGET_ID_MASK & NFP_CPP_TARGET_MU) &&
			priv->action == NFP_CPP_ACTION_RW)
		is_64 = false;

	if (is_64) {
		if (offset % sizeof(uint64_t) != 0 ||
				length % sizeof(uint64_t) != 0)
			return -EINVAL;
	} else {
		if (offset % sizeof(uint32_t) != 0 ||
				length % sizeof(uint32_t) != 0)
			return -EINVAL;
	}

	if (priv->bar == NULL)
		return -EFAULT;

	if (is_64)
		for (n = 0; n < length; n += sizeof(uint64_t)) {
			*wrptr64 = *rdptr64;
			wrptr64++;
			rdptr64++;
		}
	else
		for (n = 0; n < length; n += sizeof(uint32_t)) {
			*wrptr32 = *rdptr32;
			wrptr32++;
			rdptr32++;
		}

	return n;
}

#define PCI_DEVICES "/sys/bus/pci/devices"

static int
nfp_acquire_process_lock(struct nfp_pcie_user *desc)
{
	int rc;
	struct flock lock;
	char lockname[30];

	memset(&lock, 0, sizeof(lock));

	snprintf(lockname, sizeof(lockname), "/var/lock/nfp_%s", desc->busdev);
	desc->lock = open(lockname, O_RDWR | O_CREAT, 0666);
	if (desc->lock < 0)
		return desc->lock;

	lock.l_type = F_WRLCK;
	lock.l_whence = SEEK_SET;
	rc = -1;
	while (rc != 0) {
		rc = fcntl(desc->lock, F_SETLKW, &lock);
		if (rc < 0) {
			if (errno != EAGAIN && errno != EACCES) {
				close(desc->lock);
				return rc;
			}
		}
	}

	return 0;
}

static int
nfp6000_set_model(struct rte_pci_device *dev,
		struct nfp_cpp *cpp)
{
	uint32_t model;

	if (rte_pci_read_config(dev, &model, 4, 0x2e) < 0) {
		PMD_DRV_LOG(ERR, "nfp set model failed");
		return -1;
	}

	model  = model << 16;
	nfp_cpp_model_set(cpp, model);

	return 0;
}

static int
nfp6000_set_interface(struct rte_pci_device *dev,
		struct nfp_cpp *cpp)
{
	uint16_t interface;

	if (rte_pci_read_config(dev, &interface, 2, 0x154) < 0) {
		PMD_DRV_LOG(ERR, "nfp set interface failed");
		return -1;
	}

	nfp_cpp_interface_set(cpp, interface);

	return 0;
}

static int
nfp6000_set_serial(struct rte_pci_device *dev,
		struct nfp_cpp *cpp)
{
	off_t pos;
	uint16_t tmp;
	uint8_t serial[6];
	int serial_len = 6;

	pos = rte_pci_find_ext_capability(dev, RTE_PCI_EXT_CAP_ID_DSN);
	if (pos <= 0) {
		PMD_DRV_LOG(ERR, "PCI_EXT_CAP_ID_DSN not found. nfp set serial failed");
		return -1;
	} else {
		pos += 6;
	}

	if (rte_pci_read_config(dev, &tmp, 2, pos) < 0) {
		PMD_DRV_LOG(ERR, "nfp set serial failed");
		return -1;
	}

	serial[4] = (uint8_t)((tmp >> 8) & 0xff);
	serial[5] = (uint8_t)(tmp & 0xff);

	pos += 2;
	if (rte_pci_read_config(dev, &tmp, 2, pos) < 0) {
		PMD_DRV_LOG(ERR, "nfp set serial failed");
		return -1;
	}

	serial[2] = (uint8_t)((tmp >> 8) & 0xff);
	serial[3] = (uint8_t)(tmp & 0xff);

	pos += 2;
	if (rte_pci_read_config(dev, &tmp, 2, pos) < 0) {
		PMD_DRV_LOG(ERR, "nfp set serial failed");
		return -1;
	}

	serial[0] = (uint8_t)((tmp >> 8) & 0xff);
	serial[1] = (uint8_t)(tmp & 0xff);

	nfp_cpp_serial_set(cpp, serial, serial_len);

	return 0;
}

static int
nfp6000_set_barsz(struct rte_pci_device *dev,
		struct nfp_pcie_user *desc)
{
	int i = 0;
	uint64_t tmp;

	tmp = dev->mem_resource[0].len;

	while (tmp >>= 1)
		i++;

	desc->barsz = i;

	return 0;
}

static int
nfp6000_init(struct nfp_cpp *cpp,
		struct rte_pci_device *dev)
{
	int ret = 0;
	struct nfp_pcie_user *desc;

	desc = malloc(sizeof(*desc));
	if (desc == NULL)
		return -1;


	memset(desc->busdev, 0, BUSDEV_SZ);
	strlcpy(desc->busdev, dev->device.name, sizeof(desc->busdev));

	if (rte_eal_process_type() == RTE_PROC_PRIMARY &&
			cpp->driver_lock_needed) {
		ret = nfp_acquire_process_lock(desc);
		if (ret != 0)
			goto error;
	}

	if (nfp6000_set_model(dev, cpp) < 0)
		goto error;
	if (nfp6000_set_interface(dev, cpp) < 0)
		goto error;
	if (nfp6000_set_serial(dev, cpp) < 0)
		goto error;
	if (nfp6000_set_barsz(dev, desc) < 0)
		goto error;

	desc->cfg = dev->mem_resource[0].addr;
	desc->dev_id = dev->addr.function & 0x7;

	ret = nfp_enable_bars(desc);
	if (ret != 0) {
		PMD_DRV_LOG(ERR, "Enable bars failed");
		return -1;
	}

	nfp_cpp_priv_set(cpp, desc);

	return 0;

error:
	free(desc);
	return -1;
}

static void
nfp6000_free(struct nfp_cpp *cpp)
{
	struct nfp_pcie_user *desc = nfp_cpp_priv(cpp);

	nfp_disable_bars(desc);
	if (cpp->driver_lock_needed)
		close(desc->lock);
	close(desc->device);
	free(desc);
}

static const struct nfp_cpp_operations nfp6000_pcie_ops = {
	.init = nfp6000_init,
	.free = nfp6000_free,

	.area_priv_size = sizeof(struct nfp6000_area_priv),
	.area_init = nfp6000_area_init,
	.area_acquire = nfp6000_area_acquire,
	.area_release = nfp6000_area_release,
	.area_read = nfp6000_area_read,
	.area_write = nfp6000_area_write,
	.area_iomem = nfp6000_area_iomem,
};

const struct
nfp_cpp_operations *nfp_cpp_transport_operations(void)
{
	return &nfp6000_pcie_ops;
}
