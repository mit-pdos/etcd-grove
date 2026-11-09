# The target configuration C of the Linux file extension

The Fs v2 semantics (`GooseLang/Ext/Fs/Impl.lean`, its header's "Configuration C") claims to
describe one machine configuration and nothing else. Every decision is checked against it, and
every experiment of `notes/axiom-review/` runs on it, made by `mkfs-mount.sh` and checked by
`check.sh`, so that a new test cannot land in a corner of a wider family no decision was
checked against (the flip-flops of rounds 1-4: `fs-v2-r4.md`).

| | C |
|---|---|
| Kernel | Linux 7.0 (7.0.0-38-generic, Ubuntu), x86-64, 4 KiB pages, no swap |
| Filesystem | one local ext4, `mkfs.ext4` defaults (e2fsprogs 1.47: 4 KiB blocks, extents, `has_journal`, `metadata_csum`, `orphan_file`; no `bigalloc`, `fast_commit`, `casefold`, `inline_data`) |
| Mount | ext4's default options: `data=ordered`, `delalloc`, `dioread_nolock`, barriers; any `commit=` interval; not `journal_async_commit`, `nobarrier`, `data=journal`/`writeback`, `nodelalloc`, `dioread_lock`, read-only |
| Process | `RLIMIT_FSIZE` unlimited; Go 1.27.3 (the pinned toolchain) |
| Device | honours cache flushes, writes 512-byte sectors atomically, no media errors |

Why this configuration: it is a reasonable etcd deployment. etcd's hardware guide recommends
local SSD storage and needs no special mount option; ext4 made and mounted with its defaults is
the root filesystem of Ubuntu's and Debian's installers and of most cloud images. It is also this
machine's own root filesystem, so every claim can be measured here.

Outside C (xfs, `data=journal`, 1 KiB/2 KiB blocks, other kernels): not described. Adding one is a
change of the semantics' claim, with its own pass of the experiments below.

## The scripts

- `mkfs-mount.sh`: sourced; `c_mkfs IMG` makes a 1 GiB sparse image with `mkfs.ext4`'s defaults
  on a loop device (1 GiB: mke2fs's "default" type, not "small"); `c_mount DEV DIR [OPTS]` mounts
  it with the default options (`OPTS` may add `commit=N`, or a contrast such as `dioread_lock`,
  which the experiment then says); `c_check DIR` runs `check.sh`.
- `check.sh MOUNT [--allow OPT]`: exits 1 unless the mount and this process are C (kernel, arch,
  page size, `ulimit -f`, swap, filesystem type, block size, features, the kernel's effective
  ext4 options from `/proc/fs/ext4/<dev>/options`).
- `crash.sh WORKDIR SCENARIO [OPTS]`: a crash with the journal's writes on disk and the data's
  held back by `dm-delay` (the interleaving where metadata committed before its data); scenarios
  `append-new`, `empty-write`, `append-end`, `keep-size`, `shrink-grow` (the outcome the crash
  rule allows is in the script's header).

## Results on C (2026-11-09)

| scenario | crash image after recovery | the model |
|---|---|---|
| `append-new` (4096 zero bytes synced; `pwrite 07` at 4096) | size 4097, extent `Uninit`, byte 4096 = `00` | allowed: page 1 is durable zeros |
| the same, `dioread_lock` (not C) | size 4096 | allowed |
| `empty-write` (empty synced file; `pwrite 07` at 0) | size 1, byte 0 = `00` | allowed (`crash_new_block_zeros`) |
| `keep-size` (`fallocate -k 4096 4096` synced; `pwrite 07` at 4096) | size 4097, byte 4096 = `00` | allowed: KEEP_SIZE changes nothing |
| `shrink-grow` (8192 bytes synced; truncate 100, fsync, truncate 8192), data delay 20 s | size 100 | allowed |
| the same, data delay 1 s | size 8192, bytes from 100 on `00` | the guarantee (`crash_past_end_zeros`) |
| `append-end` (size 1, `00 07` on disk; `pwrite 05` at 2) | size 1 | allowed |

`fs-v2-f3/ordered.sh` (C's `mkfs` and mount, its own crash method: the image copied 3 s after the
change, periodic writeback off, `commit=1`) gave the unordered append into the end's block: size
2 reading `00 00`, and with `STALE=1` size 2 reading the stale `07` (`fs-v2.md`, F3).
