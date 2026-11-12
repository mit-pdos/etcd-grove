# Requirements on `os` (project bboltfs's translation, the OsFs extension; trust boundary)

## from 4d

1. `os.Getenv(key)` returns some string, without panicking (`internal/common/verify.go:20`,
   `getEnvVerify`: `strings.ToLower(os.Getenv("BBOLT_VERIFY"))`). Any string: `Verify.spec` proves
   both of its branches. Used by: `Verify.spec`.
2. `os.Getpagesize()` returns 4096: the page size of the target the models assume (linux/amd64,
   where `syscall.Getpagesize` is the constant 4096), as the old development trusted
   (`specs-ref/Spec/os/Getpagesize.lean`). Coordinator's decision, round 1 of 4d (F2): 4c's
   `fileHolds`, `DB.Info`, `Tx.Size` and `Open` (D13) are written at 4096.
   `internal/common/types.go:31`: `var DefaultPageSize = os.Getpagesize()`. Used by:
   `BboltCommon.init.spec` (bbolt's `Open` takes it as a new file's page size, db.go:268).

## from 4c

bbolt's `Open` (`SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`) opens its file with `os.OpenFile` (or a client's
`OpenFile`, `Bbolt.openFileOk`) and uses the `*os.File` through `Fd`, `Stat`, `ReadAt`, `WriteAt`,
`Sync`, `Close` (over OsFs's `osFd`, `osMeta`, `osBytes`). It names the representation provisionally
`Bbolt.osFileOf f fd` ("`f` is an `*os.File` over the fd `fd`", exclusive): please provide it (the
old `specs-ref/Spec/os/`'s `fileOwn`), with `os.OpenFile`'s spec giving it and the methods' specs
taking it, so that `osFileOf` is replaced by yours. Etcd's defrag (`backend.go:516-526`) creates its
file with `os.CreateTemp` and returns it from the custom `OpenFile`: `CreateTemp`'s spec should give
the same representation.
