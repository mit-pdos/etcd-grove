/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/Storage__InitialState.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the two fresh structs, every cell `nil`, are
frozen (`hsRO_of_struct`, `csPts_of_struct_ro`): the hard state is the zero record, the conf state
the voters.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Storage__InitialState
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

theorem Storage.InitialState.wp_proof : Storage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s vsl voters w
  wp_start as ⟨#Hv, #Hvs, #Hw⟩
  iapply wp_fupd
  wp_auto
  -- (2026-10-20, W4) `if s.witness != 0 { cs.Witness = new(s.witness) }`
  let csv : Loc → raftpb.ConfState := fun pw =>
    ⟨zero_val _, vsl, slice.nil, slice.nil, slice.nil, null, pw, null, slice.nil, 0⟩
  wp_join iprop(∃ pw : Loc, «$r0_ptr» ↦ csv pw ∗ (⌜pw = null ∧ w = W64 0⌝ ∨ pw ↦ w) ∗
      cs_ptr ↦ «$r0_ptr» ∗ s_ptr ↦ s) at next with [«$r0» cs s] as ⟨%pw, Hcs0, Hpw, cs, s⟩
  · by_cases hw : w = W64 0
    · subst hw
      rw [show (!decide (W64 0 = W64 0)) = false from rfl]
      wp_auto
      wp_join_done
      iexists null
      iframe «$r0» cs s
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · rw [show (!decide (w = W64 0)) = true by simp only [decide_eq_false hw, Bool.not_false]]
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hr0nn⟩
      iStructNamed «$r0»
      obtain ⟨rp, hrp⟩ : ∃ rp, rp = «$r0_ptr» := ⟨_, rfl⟩
      subst hrp
      wp_auto
      wp_join_done
      iexists «$r0_ptr»
      iframe cs s
      isplitr [«$r0»]
      · iapply typedPointsto_combine _ _ _ Hr0nn
        simp only [TypedPointsto.typedPointstoDef, csv]
        iframe
      iright; iexact «$r0»
  ihave Hpw : iprop(|==> cellRO (GF := GF) pw w) $$ [Hpw]
  · icases Hpw with (%H | H)
    · imodintro; unfold cellRO; ileft; ipureintro; exact ⟨H.1, H.2⟩
    · iapply cellRO_alloc $$ H
  imod Hpw with #Hpw
  irename «$r0» => Hhp
  generalize «$r0_ptr» = hp at *
  rename_i csp
  -- `&pb.HardState{}`: every cell `nil`, the zero record, frozen
  imod hsRO_of_struct hp (zero_val raftpb.HardState) (HardStateM.mk (W64 0) (W64 0) (W64 0)) ⊤ rfl
    $$ [Hhp] with #Hhs
  · iframe Hhp
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  -- `&pb.ConfState{Voters: s.voters}`, and the witness (2026-10-20, W4): the voters read-only,
  -- the other slices `nil`, `AutoLeave` and `WitnessOutgoing` `nil`, frozen
  imod csPts_of_struct_ro csp (csv pw) (kvConfState voters w) ⊤ rfl $$ [Hcs0] with #Hcs
  · iframe Hcs0
    simp only [kvConfState, csv]
    iframe Hvs Hpw
    repeat (isplitr; · iapply ownSlice_nil)
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iapply HΦ
  isplitl []
  · iunfold hsOpt; iright; iexact Hhs
  iExactEq Hcs
  simp [csv]

end proof

end kvwitness
end EtcdGrove
end Perennial
