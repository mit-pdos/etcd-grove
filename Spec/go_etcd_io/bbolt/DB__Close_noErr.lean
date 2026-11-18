/-
`DB.Close` (bbolt) with no error of the environment (S3a, `notes/bbolt-integration-plan.md`, D-I5):
`DB.Close.spec` over a semantics whose steps satisfy **no I/O error** (`NoIoErr Sio`, approved by the
user 2026-11-15) and **no error of `flock`, `mmap`, `munmap`** (`NoMapLockErr Sio`, pending the user's
review) on every file (`∀ st i, Sio.ino st i`, as the WAL's `…NoErr` specs). Proof:
`Proof/go_etcd_io/bbolt/DB__Close_noErr.lean`.
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Close()` returns `nil` when the environment's calls do not fail: `DB.Close.spec`, with
`err = nil`. The calls `Close` makes that could fail are `munmap`, `flock(LOCK_UN)` and the file's
`close` (`NoMapLockErr` excludes the first two's errors, `NoIoErr` the third's); a closed database's
`Close` returns `nil` (`db.close()` sees `opened` false). Where etcd's backend needs it:
`applySnapshot` panics on the old backend's `Close` error (the backend's `dbCloseOk` until S3). -/
abbrev DB.Close_noErr.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → ∀ (db : Loc) (γ : BoltName),
  {{ isBolt (GF := GF) db γ ∗ boltCloser γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
