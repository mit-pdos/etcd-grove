/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/EnsureConfState.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.EnsureConfState.wp_proof : raftpb.EnsureConfState.spec (GF := GF) (hG := hG) := by
  intro cs c
  wp_start as Hc
  iapply wp_fupd
  iunfold csOpt at Hc
  icases Hc with (⟨%Hp, %Hc⟩ | Hc)
  · subst Hp Hc
    wp_auto
    rename_i r
    irename : («$r0_ptr» ↦ false : IProp GF) => Hq
    ihave %Hqn := typedPointsto_not_null $$ Hq
    imod cellRO_alloc _ _ $$ Hq with #cq
    ihave Hn1 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn2 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn3 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hn4 : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod csPts_of_struct r { (zero_val raftpb.ConfState) with AutoLeave' := «$r0_ptr» }
      (ConfStateM.mk [] [] [] [] false) ⊤ (by rfl) $$ [«$r0» Hn1 Hn2 Hn3 Hn4 cq]
      with Hcs
    · dsimp only
      iframe
      iframe cq
    rw [show decide (_ ≠ null) = true from decide_eq_true Hqn]
    imodintro
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd rfl h
  · iNamed Hc
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_if_destruct
    · -- a nil `AutoLeave`: it reads `false`; the fresh cell holds `false`
      ihave (⟨-, %Hv⟩ | ⟨-, %Hpn⟩) := cellRO_cases $$ cA
      · irename : («$r0_ptr» ↦ false : IProp GF) => Hq
        ihave %Hqn := typedPointsto_not_null $$ Hq
        imod cellRO_alloc _ _ $$ Hq with #cq
        imodintro
        iapply HΦ
        isplitl
        · iunfold csPts
          iexists sv, sl, so, sn, «$r0_ptr»
          isplitr
          · ipureintro; exact Hnn
          iframe
          rw [show c.AutoLeave' = false from Hv]
          iframe cq Hpb
          ipureintro; intro _; exact Hqn
        · ipureintro; intro _; rfl
      · exact absurd rfl Hpn
    · imodintro
      iapply HΦ
      isplitl
      · iunfold csPts
        iexists sv, sl, so, sn, pa
        isplitr
        · ipureintro; exact Hnn
        iframe
        iframe cA Hpb
        ipureintro; intro _; exact Hif
      · ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
