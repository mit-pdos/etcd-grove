/-
Port of `election_proof/spec_SoftState__equal.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `a.equal(b)` (`node.go:45`) on two `*SoftState`s: field-wise equality, and
`SoftState` has exactly the two fields compared. -/
abbrev SoftState.equal.spec : Prop :=
  ∀ (a b : Loc) (va vb : SoftState) (dqa dqb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Ha" ∷ a ↦{dqa} va ∗ "Hb" ∷ b ↦{dqb} vb }}
    (App (Val (a @!! go.GoType.PointerType SoftState.ty @!! go!"equal")) (Val #b))
  {{ RET #(decide (va.Lead' = vb.Lead' ∧ va.RaftState' = vb.RaftState'));
      a ↦{dqa} va ∗ b ↦{dqb} vb }}

end spec

end EtcdGrove
end Perennial
