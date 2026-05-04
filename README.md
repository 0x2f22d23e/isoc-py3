# isoc-py3
TempleOS RedSea FUSE implementation for Python 3

# Commands

`isoc-mount [--rw] <filename.ISO.C> <mount_point>` will mount an ISO.C image on `mount_point`

Specify `--rw` to commit writes to ISO.C file, otherwise discarded on unmount.

# Prerequisites

- FUSE
- fusepy
