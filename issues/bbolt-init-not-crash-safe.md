---
upstream: unchecked
---

# bbolt: a crash during `init` can leave a database that never opens

**Status.** A crash-safety bug, by reasoning against Linux's documented guarantees. It has not
been reproduced on a real crash. `init` makes the metas durable together with the pages they
point at, with no ordering between them. A crash before its `fdatasync` completes can keep a
valid meta and lose the root or freelist page, and every later `Open` then fails or panics.

**Where.** bbolt v1.5.0 (etcd's `go.mod`):
- `db.go:646-686`, `(*DB).init`: one buffer of 4 pages (meta 0, meta 1, freelist page 2, root
  leaf page 3), one `writeAt(buf, 0)`, one `fdatasync`.
- `db.go:272-286`, `Open`: `init` runs only when the file's size is 0. Otherwise `Open` trusts
  the metas.

**What happens.**
- Linux writes back a file's dirty pages in any order. Before `fdatasync` returns, a crash may
  keep any subset of the four pages, and on ext4 the on-disk size follows the data that reached
  the disk.
- If meta 0 or meta 1 survives while page 2 or page 3 does not, the next `Open` sees a nonzero
  size and a meta that passes `Validate`, so it does not re-run `init`. Then:
  - if the file is shorter than 4 pages, the mapping's freelist page lies past EOF and its load
    is a SIGBUS;
  - if the file is 4 pages but page 2 is zeros or stale, `loadFreelist` panics
    (`invalid freelist page`, `internal/freelist/shared.go:258`);
  - if page 3 is zeros, the root bucket is a page of type 0.
- If the file keeps under one page (a nonzero size and no meta), `getPageSize` fails and every
  `Open` returns an error.
- Each of these cases repeats at every `Open`. The database is permanently unopenable until
  someone deletes the file.

**Expected.** bbolt is documented as crash-safe ("fully serializable ACID transactions"). A
freshly created database interrupted by a crash should reopen as empty, or be re-initialized.

**How the proof handles it.** Not proved yet. The Linux file extension's crash relation
(`GooseLang/Ext/OsFs/Impl.lean`, `CrashImage`: unsynced bytes are arbitrary, plan D1) allows
this outcome. `examples/bboltfs`'s minibolt therefore differs from bbolt here on purpose (its
README, "One deliberate difference from bbolt: init"). A proof of bbolt's crash safety needs
the same change in the bbolt fork.

**Possible fixes.**
- Write and `fdatasync` pages 2–3 first, then the metas, then `fdatasync` again.
- Have `Open` re-run `init` when neither meta validates.
- Or: write the metas into a temporary file and rename it into place, which needs directory
  syncs.

**Found.** 2026-10-31, writing the acceptance tests of the Linux file extension
(`examples/bboltfs`, branch `osfs-ext`).
