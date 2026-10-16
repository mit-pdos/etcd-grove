/- Lean-first (no Rocq counterpart).

`(*Register).answer(pending, applied)` (register.go:148, 2026-10-13): the applier's answer to
the pending read states (each `rsOk`: a `ReadState` value whose context holds the bytes of a
read state `Ready` handed out, `readStateOk`; raft v3.7, stage R6b, D6: a read context is its
bytes), after it applied the committed prefix `ap` (`runOwn`), at least `applied` long: a
waiting read of this replica whose read index is at most `applied` gets the value after `ap`
(`readAns`); the read states with a larger index come back, in a new slice.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Register.answer.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc)
    (ap : List EntryM) (psl : GoSlice) (ps : List ReadState) (dq : DFrac) (applied : w64),
  uint.Z applied ≤ (ap.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      isReplica γr γp r id n st ∗ runOwn γr r ap ∗
      psl ↦*{dq} ps ∗ [∗list] v ∈ ps, rsOk γr.raft v }}
    (App (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"answer")) (Val #psl))
      (Val #applied))
  {{ (rest : GoSlice), RET #rest; runOwn γr r ap ∗
      ∃ ps' : List ReadState, rest ↦* ps' ∗ ownSliceCap ReadState rest (DFrac.own 1) ∗
        [∗list] v ∈ ps', rsOk γr.raft v }}

end spec

end register
end EtcdGrove
end Perennial
