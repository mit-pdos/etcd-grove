/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/Storage__InitialState.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the two fresh structs, every cell `nil`, are
frozen (`hsRO_of_struct`, `csPts_of_struct_ro`): the hard state is the zero record, the conf state
the voters.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem Storage.InitialState.wp_proof : Storage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s vsl voters
  wp_start as ⟨#Hv, #Hvs⟩
  wp_auto
  wp_alloc hp as Hhp
  -- `&pb.HardState{}`: every cell `nil`, the zero record, frozen
  imod hsRO_of_struct hp (zero_val raftpb.HardState) (HardStateM.mk (W64 0) (W64 0) (W64 0)) ⊤ rfl
    $$ [Hhp] with #Hhs
  · iframe Hhp
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_auto
  wp_alloc cs as Hcs
  -- `&pb.ConfState{Voters: s.voters}`: the voters read-only, the other slices `nil`, `AutoLeave`
  -- `nil`, frozen
  imod csPts_of_struct_ro cs
      (⟨zero_val _, vsl, slice.nil, slice.nil, slice.nil, null, slice.nil, 0⟩ : raftpb.ConfState)
      (kvConfState voters) ⊤ rfl $$ [Hcs] with #Hcs
  · iframe Hcs
    simp only [kvConfState]
    iframe Hvs
    repeat (isplitr; · iapply ownSlice_nil)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_auto
  iapply HΦ
  isplitl []
  · iunfold hsOpt; iright; iexact Hhs
  iExactEq Hcs
  simp

end proof

end kv
end EtcdGrove
end Perennial
