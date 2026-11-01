/- Lean-first (no Rocq counterpart). `db.meta()` (`examples/bboltfs/minibolt.go`): `pickMeta(db.meta0, db.meta1)` (`pickMetaRes`), read through any fractions of the fields and the metas, when one of the metas is valid (otherwise it panics). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.«meta».spec : Prop :=
  ∀ (db m0 m1 : Loc) (v0 v1 : Meta) (dq dq0 dq1 : DFrac),
    metaValid v0 ∨ metaValid v1 →
    {{ (db.[DB, go!"meta0"] ↦{dq} m0 ∗ db.[DB, go!"meta1"] ↦{dq} m1 ∗
        m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗ ⌜0 < m0.addr ∧ 0 < m1.addr⌝ : IProp GF) }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"meta")) (Val #()))
    {{ RET #(pickMetaRes m0 v0 m1 v1); db.[DB, go!"meta0"] ↦{dq} m0 ∗
        db.[DB, go!"meta1"] ↦{dq} m1 ∗ m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}

end spec

end bboltfs
end EtcdGrove
end Perennial
