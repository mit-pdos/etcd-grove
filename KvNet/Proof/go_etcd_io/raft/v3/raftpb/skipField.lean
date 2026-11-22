-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/skipField.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.skipField
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.skipScalar
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem tag_fieldnum (v : w64) : uint.nat (v >>> W64 3) = uint.nat v / 8 := by
  change (v >>> W64 3).toNat = _
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem tag_wiretype (v : w64) : uint.nat (v &&& W64 7) = uint.nat v % 8 := by
  change (v &&& W64 7).toNat = _
  rw [BitVec.toNat_and, show (W64 7).toNat = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem raftpb.skipField.wp_proof
    (wp_scalar : raftpb.skipScalar.spec (GF := GF) (hG := hG))
    (wp_varint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.skipField.spec (GF := GF) (hG := hG) := by
  intro b dq bs i tag Hi Hlen
  wp_start as Hb
  ihave %Hsize := ownSlice_len $$ Hb
  have htag := tag_wiretype tag
  wp_auto
  wp_if_destruct
  · have hgroup : uint.nat tag % 8 = 3 := by rw [← htag]; word
    wp_apply wp_slice_literal (V := w64) [tag >>> W64 3]
    isplitr
    · ipureintro; rfl
    iintro %s ⟨Hs, Hcap⟩
    wp_auto
    ihave IH : iprop(∃ (j : w64) (sl : GoSlice) (opened : List w64),
        "i" ∷ i_ptr ↦ j ∗ "Hopen" ∷ open_ptr ↦ sl ∗
        "stack" ∷ sl ↦* opened.reverse ∗ "cap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hidx" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ bs.length⌝ ∗
        "%Hres" ∷ ⌜ccSkipField bs (sint.nat i) (uint.nat tag) =
          ccGroupAt bs (sint.nat j) (opened.map uint.nat)⌝) $$ [i «open» Hs Hcap]
    · iexists i, _, [tag >>> W64 3]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil]
      iframe
      ipureintro
      exact ⟨⟨Hi, Hlen⟩, by rw [ccSkipField, ite_eq_left hgroup]; simp only [tag_fieldnum]⟩
    wp_for IH
    ihave %HstackLen := ownSlice_len $$ stack
    rw [List.length_reverse] at HstackLen
    by_cases hz : sl.len = W64 0
    · have hc : (!decide (sl.len = W64 0)) = false := by simp only [hz, decide_true, Bool.not_true]
      rw [hc, ite_eq_right (by simpa using false_neq_true), ite_eq_left (by simp)]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      have hempty : opened = [] := List.eq_nil_of_length_eq_zero (by rw [hz] at HstackLen; word)
      rw [Hres, hempty, List.map_nil, ccGroupAt_nil]
      exact ⟨rfl, by word⟩
    · have hc : (!decide (sl.len = W64 0)) = true := by rw [decide_eq_false hz]; rfl
      rw [hc, ite_eq_left (by simp)]
      wp_auto
      obtain ⟨top, outer, rfl⟩ : ∃ top outer, opened = top :: outer := by
        cases opened with
        | nil => simp at HstackLen; exfalso; apply hz; word
        | cons top out => exact ⟨top, out, rfl⟩
      wp_apply wp_varint b dq bs j Hidx.1 Hidx.2 $$ [$Hb] as %v %k %ok ⟨Hb, %Hr⟩
      cases hv : ccVarintL bs (sint.nat j) with
      | none =>
        rw [hv] at Hr
        subst Hr
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        have ht : ccTagL bs (sint.nat j) (2^31 - 1) = none := by simp [ccTagL, hv]
        rw [Hres, List.map_cons, ccGroupAt_no_tag _ ht]
      | some pair =>
        obtain ⟨vv, start⟩ := pair
        rw [hv] at Hr
        obtain ⟨rfl, rfl, hstart⟩ := Hr
        have hj := ccVarintL_bound hv
        wp_auto
        have hmax : uint.Z (W64 2147483647) = 2147483647 := rfl
        have hn := tag_fieldnum v
        have hb : uint.Z (v >>> W64 3) = ((uint.nat v / 8 : Nat) : Int) := by
          change ((uint.nat (v >>> W64 3) : Nat) : Int) = _
          rw [hn]
        have hnone : ¬ (1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^31-1) →
            ccGroupAt bs (sint.nat j) (List.map uint.nat (top :: outer)) = none := by
          intro h
          apply ccGroupAt_no_tag
          unfold ccTagL
          rw [hv]
          exact ite_eq_right h
        wp_if_destruct
        · wp_for_post
          iapply HΦ
          iframe
          ipureintro
          rw [Hres, hnone (by rw [← hn]; word)]
        · wp_if_destruct
          · wp_for_post
            iapply HΦ
            iframe
            ipureintro
            rw [Hres, hnone (by omega)]
          · have hvalid : 1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^31-1 := by
              rw [← hn]
              constructor <;> word
            have ht : ccTagL bs (sint.nat j) (2^31 - 1) = some (uint.nat v, start) := by
              unfold ccTagL
              rw [hv]
              exact ite_eq_left hvalid
            have hstep := ccGroupAt_tag (outer.map uint.nat) (num := uint.nat top) ht
            have hwire := tag_wiretype v
            have hlen' : sint.Z sl.len = (outer.length : Int) + 1 := by
              simp only [List.length_cons] at HstackLen
              word
            have hki : sint.nat k = start := by word
            have hkbound : 0 ≤ sint.Z k ∧ sint.Z k ≤ bs.length := by
              simp only at hstart
              omega
            change ccSkipField bs (sint.nat i) (uint.nat tag) =
              ccGroupAt bs (sint.nat j) (uint.nat top :: outer.map uint.nat) at Hres
            rw [hstep] at Hres
            wp_if_destruct
            · have h3 : uint.nat v % 8 = 3 := by rw [← hwire, Hif]; rfl
              rw [h3] at Hres
              wp_if_destruct
              · wp_for_post
                iapply HΦ
                iframe
                ipureintro
                have hlarge : ¬ (outer.map uint.nat).length + 1 ≤ 10000 := by
                  rw [List.length_map]
                  have : sint.Z (W64 10000) = 10000 := rfl
                  omega
                rw [Hres, ite_eq_right hlarge]
                rfl
              · wp_apply wp_slice_literal (V := w64) [v >>> W64 3]
                isplitr
                · ipureintro; rfl
                iintro %lp ⟨Hv, -⟩
                wp_apply wp_slice_append $$ [$stack $cap $Hv] as %sl' ⟨Hstack, Hcap, -⟩
                wp_for_post
                iframe
                iexists k, sl', (v >>> W64 3) :: top :: outer
                simp only [List.reverse_cons]
                iframe
                ipureintro
                refine ⟨hkbound, ?_⟩
                have hsmall : (outer.map uint.nat).length + 1 ≤ 10000 := by
                  rw [List.length_map]
                  have : sint.Z (W64 10000) = 10000 := rfl
                  omega
                rw [Hres, ite_eq_left hsmall, hki]
                simp only [List.map_cons, hn]
            · have h3 : uint.nat v % 8 ≠ 3 := by rw [← hwire]; word
              wp_if_destruct
              · have h4 : uint.nat v % 8 = 4 := by rw [← hwire, Hif]; rfl
                rw [h4] at Hres
                change ccSkipField bs (sint.nat i) (uint.nat tag) =
                  (if uint.nat v / 8 = uint.nat top then ccGroupAt bs start (outer.map uint.nat) else none) at Hres
                have hin : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by
                  constructor <;> word
                have hlenNat : (outer.length : Int) = sl.len.toInt - 1 := by change sl.len.toInt = _ at hlen'; omega
                have hlmax : sl.len.toInt < 2^63 := by word
                have hl : (sint.Z (sl.len - W64 1)).toNat = outer.reverse.length := by
                  rw [List.length_reverse]
                  change (sl.len - W64 1).toInt.toNat = outer.length
                  rw [BitVec.toInt_sub, show (W64 1).toInt = 1 from rfl, Int.bmod_eq_of_le] <;> omega
                rw [ite_eq_left hin]
                wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) _ _ top hin.1 $$ [stack] as Hstack
                · iframe
                  ipureintro
                  rw [hl]
                  simp
                wp_auto
                wp_if_destruct
                · ihave %Hwf := ownSliceCap_wf _ _ $$ cap
                  have hsub : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
                      sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by constructor <;> word
                  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
                        sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap by constructor <;> word)]
                  wp_auto
                  icases (ownSlice_slice (W64 0) (sl.len - W64 1) sl (DFrac.own 1) ((v >>> W64 3) :: outer).reverse hsub).1
                    $$ Hstack with ⟨-, Hpre, Hend⟩
                  ihave Hcap := ownSlice_slice_absorb_capacity sl _ (W64 0) (sl.len - W64 1) hsub $$ [Hend cap]
                  · iframe
                  wp_for_post
                  iframe
                  iexists k, _, outer
                  have hl' : sint.nat (sl.len - W64 1) = outer.reverse.length := hl
                  have hs : subslice (sint.nat (W64 0)) (sint.nat (sl.len - W64 1)) ((v >>> W64 3) :: outer).reverse =
                      outer.reverse := by rw [show sint.nat (W64 0) = 0 from rfl, hl', List.reverse_cons]; simp [subslice]
                  rw [hs]
                  iframe
                  ipureintro
                  refine ⟨hkbound, ?_⟩
                  rw [Hres, hki, ite_eq_left hn.symm]
                · wp_for_post
                  iapply HΦ
                  iframe
                  ipureintro
                  have hneq : uint.nat v / 8 ≠ uint.nat top := by rw [← hn]; word
                  rw [Hres, ite_eq_right hneq]
              · have h4 : uint.nat v % 8 ≠ 4 := by rw [← hwire]; word
                have heq : ccSkipField bs (sint.nat i) (uint.nat tag) =
                    (ccSkipScalar bs start (uint.nat (v &&& W64 7))).bind
                      (fun last => ccGroupAt bs last (uint.nat top :: outer.map uint.nat)) := by
                  rw [Hres, hwire]
                  split <;> simp_all
                wp_apply wp_scalar b dq bs k (v &&& W64 7) hkbound.1 hkbound.2 $$ [$Hb] as %last %ok ⟨Hb, %Hr⟩
                rw [hki] at Hr
                cases hs : ccSkipScalar bs start (uint.nat (v &&& W64 7)) with
                | none =>
                  rw [hs] at Hr
                  subst Hr
                  wp_auto
                  wp_for_post
                  iapply HΦ
                  iframe
                  ipureintro
                  rw [heq, hs]
                  rfl
                | some lastIdx =>
                  rw [hs] at Hr
                  obtain ⟨rfl, hlast⟩ := Hr
                  have he := ccSkipScalar_bound hs
                  wp_auto
                  wp_for_post
                  iframe
                  iexists last, sl, top :: outer
                  iframe
                  ipureintro
                  have hl : sint.nat last = lastIdx := by word
                  refine ⟨⟨by omega, by omega⟩, ?_⟩
                  rw [heq, hs, hl]
                  rfl
  · wp_apply wp_scalar b dq bs i (tag &&& W64 7) Hi Hlen $$ [$Hb] as %j %ok ⟨Hb, %Hr⟩
    iapply HΦ
    iframe
    ipureintro
    have h : uint.nat tag % 8 ≠ 3 := by rw [← htag]; word
    rw [ccSkipField, ite_eq_right h, ← htag]
    cases hv : ccSkipScalar bs (sint.nat i) (uint.nat (tag &&& W64 7)) <;> rw [hv] at Hr <;> exact Hr

end proof
end EtcdGrove
end Perennial
