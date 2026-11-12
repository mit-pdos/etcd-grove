/- Lean-first (no Rocq counterpart). `db.Close()`'s crash-aware spec: `DB.Close.spec`
(`DB__Close.lean`) for an open database over the crash invariant of its file (`isDBC`,
`DBCrash.lean`). It gives back the caller's part of the file, in some state (`csOwn`); what the
state holds (`DB.Close.spec`'s `dbClosed`) is not needed by a boot, which closes the database
last. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__Close
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DBCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.Close.specCrash : Prop :=
  ∀ (γ : DBNames) (γc : GName) (db : Loc) (t n : Nat),
  {{ isDBC (GF := GF) γ γc db ∗ dbOwner (GF := GF) γ t n }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ p : GoString, db.[DB, go!"path"] ↦□ p ∗
      ∃ s : CState, csOwnF (GF := GF) γc s }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
