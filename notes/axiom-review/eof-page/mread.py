#!/usr/bin/env python3
# Print, through a read-only shared mapping, N bytes of FILE's page cache at OFF, hex: the bytes of
# the page holding EOF past the size included (a mapping shows them; read(2) stops at the size).
# OFF..OFF+N must lie in one page that holds a byte below the size.
# Usage: python3 -I mread.py FILE OFF N
import ctypes, os, sys

path, off, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
fd = os.open(path, os.O_RDONLY)
size = os.fstat(fd).st_size
page = off - off % 4096
if page >= size or off % 4096 + n > 4096:
    print("(not in the page holding EOF)")
    sys.exit(0)
libc = ctypes.CDLL(None, use_errno=True)
libc.mmap.restype = ctypes.c_void_p
libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                      ctypes.c_long]
PROT_READ, MAP_SHARED = 1, 1
a = libc.mmap(None, 4096, PROT_READ, MAP_SHARED, fd, page)
if a in (None, ctypes.c_void_p(-1).value):
    print("mmap failed: errno %d" % ctypes.get_errno())
    sys.exit(1)
print(" ".join("%02x" % b for b in ctypes.string_at(a + off - page, n)))
