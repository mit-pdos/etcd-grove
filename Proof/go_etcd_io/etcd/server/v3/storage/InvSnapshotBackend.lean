/-
The vocabulary of `OpenSnapshotBackend`'s spec (`server/storage/backend.go`, etcd PR #22518,
branch `pr-verify/etcd-22518`; reused for PR #22499 on branch `pr-verify/etcd-22499`, where
`fs.renamePending`, `fs.entryDurable`, `fs.dirOf` and `fsResult` are in `Fs.lean`, which the
package fact needs): a small, abstract model of directory-entry durability, and the
server configuration's paths. Lean-first (no Rocq counterpart).

Perennial's Lean port has no crash semantics and no file-system model (`notes/STATUS.md`,
"Out of scope for now"), so durability cannot be stated in terms of what survives a crash.
This file states it as **resources that only the trust-boundary specs produce and consume**:

- `fs.renamePending src dst`: the rename of `src` onto the path `dst` has happened (it is
  visible to the running process) but its directory entry may not be on stable storage:
  `os.Rename`'s spec (`Spec/os/Rename.lean`) gives it on success;
- `fs.entryDurable src dst`: the directory entry `dst` is on stable storage and names the file
  renamed from `src`; `fileutil.Fsync` of a handle of `dst`'s directory
  (`Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/Fsync.lean`) turns `fs.renamePending src dst`
  into it, and nothing else produces it (a failed `Fsync` consumes the pending rename: after an
  `fsync` error Linux gives no guarantee that a retry makes it durable);
- `fs.dirHandle f dir`: `f` is an open handle (an `*os.File`) of the directory `dir`, as
  `fileutil.OpenDir` returns (`Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/OpenDir.lean`);
- `fs.dirOf p`: the directory containing the path `p` (`filepath.Dir`);
- `snapDBPath ss id`: the path `ss.DBFilePath(id)` returns (`<dir>/<id>.snap.db`).

They are Lean `opaque` constants (as `ownIvt`, `kvEncode` elsewhere): no lemma unfolds them, so
a proof gets `fs.entryDurable src dst` only from a successful `Fsync` of `dst`'s directory, taken
after the rename. That is the property the PR adds. What the model does not say: that `dst` still names that
file later (a second rename onto `dst` leaves the first `fs.entryDurable` in place: no exclusive
token per directory entry; nothing in the code verified here renames onto `db` twice); anything about
the file's contents (`SaveDBFrom` synced them before; not modeled here), or about the source
entry (`<index>.snap.db`'s removal), which the PR does not sync separately (it is in the same
directory, so the same `Fsync` covers it on Linux).

The server configuration's paths are opaque functions of its `DataDir`: `cfgSnapDir dd`
(`ServerConfig.SnapDir()`, `<dd>/member/snap`) and `cfgBackendPath dd`
(`ServerConfig.BackendPath()`, `<SnapDir>/db`); `ServerConfig.BackendPath`'s spec states that the
backend file is in the snap directory (`fs.dirOf (cfgBackendPath dd) = cfgSnapDir dd`).

`fsResult err P Q`: a returned error `err` is `nil` and `P` holds, or it is a non-`nil` error
whose `Error()` returns a string (`fmt.stringMethodSpec`, what `fmt.Errorf`'s `%w` needs) and `Q`
holds.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.etcd.server.v3.storage.Fs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The path of the snapshot database `id` of the snapshotter at `ss`
(`ss.DBFilePath(id)`, `<dir>/<id as %016x>.snap.db`). -/
opaque snapDBPath : Loc → w64 → GoString

/-- `config.ServerConfig.SnapDir()` of a configuration whose `DataDir` is `dd`. -/
opaque cfgSnapDir : GoString → GoString

/-- `config.ServerConfig.BackendPath()` of a configuration whose `DataDir` is `dd`. -/
opaque cfgBackendPath : GoString → GoString

section defs
variable {GF : BundledGFunctors}

/-- `f` is an open handle of the directory `dir`. -/
opaque fs.dirHandle (f : Loc) (dir : GoString) : IProp GF := iprop(True)

end defs


end EtcdGrove
end Perennial
