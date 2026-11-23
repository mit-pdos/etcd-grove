/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__findClosest.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.findClosest(alive)` (client/client.go; model adaptation X1: fixed latencies): no error; the
pings appended to `c.Ping`, `c.ClosestId` set.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [dlog.Assumptions] [strings.Assumptions]

set_option goose.wp.extras true

theorem client.Client.findClosest.wp_proof
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    client.Client.findClosest.specI (hG := hG) := by
  intro cl v asl alive l dq dq'
  wp_start as ⟨Hcl, #Hq, %Hv, Hl, Ha⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Println $$ Hq
  ihave %Hll := ownSlice_len _ _ _ $$ Hl
  ihave %Hal := ownSlice_len _ _ _ $$ Ha
  ihave HI : (∃ (i : w64) (p : GoSlice) (ps : List w64) (ci : w64), "Hi" ∷ i_ptr ↦ i ∗
      "Hcl" ∷ cl ↦ { v with Ping' := p, ClosestId' := ci } ∗ "Hp" ∷ p ↦* ps ∗
      "Hpc" ∷ ownSliceCap w64 p (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.replicas'.len⌝ : IProp netDistGF) $$ [i Hcl]
  · iexists _, slice.nil, [], v.ClosestId'
    isplitl [i]
    · iexact i
    isplitl [Hcl]
    · rw [← Hv.1]; iexact Hcl
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hiN : sint.nat i < l.length := by word
    have hiA : sint.nat i < alive.length := by omega
    list_elem alive (sint.nat i) as b
    list_elem l (sint.nat i) as a
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    wp_apply wp_load_slice_index asl (sint.Z i) alive dq' b Hi.1 $$ [Ha] as Ha
    · iframe Ha; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hb_lookup
    cases b
    · wp_auto
      wp_for_post
      iframe
      iexists _, p, ps, ci
      iframe
      ipureintro; word
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    wp_apply wp_load_slice_index v.replicas' (sint.Z i) l dq a Hi.1 $$ [Hl] as Hl
    · iframe Hl; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Ha_lookup
    wp_apply strings.wp_Split a go!":" (by simp) as %spl ⟨Hspl, -⟩
    ihave %Hsl := ownSlice_len _ _ _ $$ Hspl
    have hne := strings.split_ne_nil a go!":"
    obtain ⟨a0, ha0⟩ : ∃ a0, (strings.split a go!":")[0]? = some a0 := by
      cases h : strings.split a go!":" with
      | nil => exact absurd h hne
      | cons x _ => exact ⟨x, rfl⟩
    have hsl0 : 0 < sint.Z spl.len := by
      have : 0 < (strings.split a go!":").length := List.length_pos_iff.mpr hne
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index spl (sint.Z (W64 0)) _ (DFrac.own 1) a0 (by word) $$ [Hspl] as Hspl
    · iframe Hspl; ipureintro; exact ha0
    wp_if_destruct
    all_goals (try wp_auto)
    all_goals wp_if_destruct
    all_goals (try wp_auto)
    all_goals (
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨-, -⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply wp_Println $$ Hq
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨Hfsl, -⟩
      wp_apply wp_slice_append p ps _ _ (DFrac.own 1) $$ [$Hp $Hpc $Hfsl] as %p' ⟨Hp, Hpc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists _, p', _, _
      iframe
      ipureintro; word)
  · by_cases hci : ci = W64 (-1)
    · rw [decide_eq_true hci]
      wp_auto
      rename_i ik_ptr
      irename : (ik_ptr ↦ (Perennial.zero_val w64 : w64)) => Hk
      ihave %Hpl := ownSlice_len _ _ _ $$ Hp
      ihave HJ : (∃ (j : w64) (k : w64) (lv mv : w64) (ci' : w64), "Hj" ∷ i_ptr ↦ j ∗
          "Hk" ∷ ik_ptr ↦ k ∗ "Hlv" ∷ l_ptr ↦ lv ∗ "Hmin" ∷ min_ptr ↦ mv ∗
          "Hcl" ∷ cl ↦ { v with Ping' := p, ClosestId' := ci' } ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z p.len⌝ : IProp netDistGF) $$ [i Hk l min Hcl]
      · iexists _, _, _, _, ci
        iframe
        ipureintro; word
      wp_for HJ
      wp_if_destruct
      · have hjN : sint.nat j < ps.length := by word
        list_elem ps (sint.nat j) as x
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, by word⟩)]
        wp_apply wp_load_slice_index p (sint.Z j) ps (DFrac.own 1) x Hj.1 $$ [Hp] as Hp
        · iframe Hp; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hx_lookup
        generalize (float64Leb x mv && !float64Eq x mv) = bb
        cases bb
        all_goals (try wp_auto)
        all_goals (
          wp_for_post
          iframe
          iexists _, _, _, _, _
          iframe
          ipureintro; word)
      · iapply HΦ
        iframe
        ipureintro; rfl
    · rw [decide_eq_false hci]
      wp_auto
      iapply HΦ
      iframe
      ipureintro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
