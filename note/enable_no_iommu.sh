#!/bin/sh
# must be root
# You have to enable unsafe mode to bind via VFIO-pci if there is no IOMMU available on the system, VFIO can still be used, but it has to be loaded with an additional module parameter
echo 1 > /sys/module/vfio/parameters/enable_unsafe_noiommu_mode
