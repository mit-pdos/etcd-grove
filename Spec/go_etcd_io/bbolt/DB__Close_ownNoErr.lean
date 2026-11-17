/-
`DB.Close` giving the file back, with no error of the environment (session bbolt-inv):
`DB.Close_own.spec` over a semantics whose steps satisfy `NoIoErr` and `NoMapLockErr` on every file
(`DB.Close_noErr.spec`'s premises). Proof: `Proof/go_etcd_io/bbolt/DB__Close_ownNoErr.lean`.
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

/-- `db.Close()` by the owner of the committed data, when the environment's calls do not fail:
`nil`, and the file of inode `i` given back holding `D`, unless the file was given up before
(`boltNoFile`: an earlier `DB.Close`, which keeps the file; a mapping bbolt leaked when a remap's
`munmap`, or `madvise` after its `mmap`, failed (failures `NoMapLockErr` excludes since session S3d
made `madvise` a step, but the leak is recorded without the failed step's evidence); or a partial last
page, which a write's failure would leave; `notes/bbolt-integration-plan.md`, Log, "S3d"). -/
abbrev DB.Close_ownNoErr.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → ∀ (db : Loc) (γ : BoltName) (i : Ino) (D : Data),
  {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ 1 D }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗
      (fileHolds i D ∨ (boltState γ 1 D ∗ boltNoFile γ)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
