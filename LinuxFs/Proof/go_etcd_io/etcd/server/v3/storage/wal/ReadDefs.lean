/-
The read-phase handles of the WAL over `fsExt` (W3/W5 of `notes/wal-fsext-plan.md`): what `Open`
returns and `ReadAll` takes (`walOpeningF`), and what a failed `ReadAll` leaves (`walReadFailedF`),
the program-level counterparts of the ghost `walOpening`/`walReadFailed` (`Ghost.lean`), as
`walOpenWF` (`Handle.lean`) is of `walOpenW`. Both are sealed: the specs that mention them
(`LinuxFs/Spec/.../wal/{Open,WAL__ReadAll}.lean`) do not depend on their bodies.

**Draft bodies** (2026-11-13, branch `wal-read`): the ghost handle and the struct fields `Open`
leaves that every later step reads (`lg`, `dir`, `start`). Still to be added by `Open`'s and
`ReadAll`'s proofs (W3/W5 log of the plan): the decoder (`ownDecoder` over `DecFile`s whose bytes
are the WAL's segments from the opened one, the program's halves of their `osMeta`/`osBytes`), the
locks (`walLockH`), the pipeline (`walPipeH`), `dirFile`, the mutex and the zero fields. Adding them
changes no client statement.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **The fields of a handle `Open` made** (draft, see the file header): the logger, the
directory, the start snapshot `s`. -/
def walOpenIn (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(∃ (lg sp : Loc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"start" w ↦ sp ∗
    walSnapIdTerm sp s)

/-- **`w` is the WAL `Open` opened in `dir` at the snapshot `s`, not yet read** (the specs' handle;
sealed). -/
@[no_expose] def walOpeningF (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  iprop(walOpening (W := W) w dir s ∗ walOpenIn w dir s)

/-- **`w`'s `ReadAll` in `dir` failed** (the specs' handle; sealed): only `Close` accepts it.
Draft body: the ghost handle and the logger and directory fields (`Close`'s spec, W10, adds what it
reads). -/
@[no_expose] def walReadFailedF (w : Loc) (dir : GoString) : IProp GF :=
  iprop(walReadFailed (W := W) w dir ∗ ∃ lg : Loc,
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir)

end handle

end WalFs
end EtcdGrove
end Perennial
