/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__PutRecvProposals.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).PutRecvProposals`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

theorem Slot.PutRecvProposals.wp_proof
    (wp_Eq : ProxySeqIdEqual.spec (GF := GF) (hG := hG)) :
    Slot.PutRecvProposals.spec (GF := GF) := fun s γ q v o => by
  iintro #Hpkg #Hslot #Hrep
  ihave ⟨#Hsync, #Hsort, #Hmsg⟩ := ledgerDeps $$ Hpkg
  unfold isSlot
  icases Hslot with ⟨#Hq, #Ht, #Hm⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  ihave HΦ : |={⊤}=> (⌜cntOk (st.total 0 1 + 1)⌝ ∗ ghostVar γ (1 : Qp).half (st.addProp o) ∗ (True -∗ Φ #())) $$ [AU Hγ]
  · imod AU with ⟨%x, Hα, -, Hcommit⟩
    rcases x with ⟨st0, ⟨⟩⟩
    dsimp only [Tele.app]
    icases Hα with ⟨Hst, %Hbnd⟩
    unfold slotSt
    icombine Hγ Hst gives %H
    obtain ⟨_, Heq⟩ := H
    subst Heq
    imod ghostVar_update_halves (st.addProp o) γ st st $$ Hγ Hst with ⟨Hγ, Hst⟩
    imod Hcommit $$ %() Hst with HΦ
    imodintro
    iframe Hγ
    isplitr
    · ipureintro; exact Hbnd
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iexact HΦ
  iapply fupd_wp
  imod HΦ with ⟨%hb, Hγ, HΦ⟩
  imodintro
  have hwf' := st.wf_addProp o Hwf hb
  iNamed Hf
  ihave %Hpl := ownSlice_len _ _ _ $$ Hpsl
  ihave %Htll := talliesRep_len _ _ $$ Htl
  ihave %Ho := objRep_ids _ _ $$ Hrep
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "Hpsl" ∷ ps ↦* tl ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ps.len ∧
        ∀ (k : Nat) (x : ObjV × Nat), k < sint.nat i → st.props[k]? = some x →
          x.1.sameId o = false⌝ : IProp GF) $$ [i Hpsl]
  · iexists W64 0
    iframe i Hpsl
    ipureintro
    refine ⟨by decide, by word, fun k x hk _ => by word⟩
  wp_for HI
  wp_if_destruct
  · have hlt := Hif
    obtain ⟨hi0, hil, hprev⟩ := Hi
    have hil' : sint.nat i < tl.length := by word
    list_elem tl (sint.nat i) as ti
    list_elem st.props (sint.nat i) as xi
    have hti : tl[(sint.Z i).toNat]? = some ti := by
      rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hti_lookup
    icases ownSlice_elem_acc (sint.Z i) ti ps _ tl hi0 hti $$ Hpsl with ⟨Hel, Hpsl⟩
    icases (tally_split _ _ _).1 $$ Hel with ⟨%hni, Hpi, Hci⟩
    simp only [hi0, Hif, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_Eq $$ [$Hpi $p] as ⟨Hpi, p⟩
    ihave #Hx := talliesRep_lookup tl _ _ ti xi Hti_lookup Hxi_lookup $$ Htl
    unfold tallyRep
    icases Hx with ⟨#Hxo, %Hxc⟩
    ihave %Hxid := objRep_ids _ _ $$ Hxo
    obtain ⟨hT1, hT2⟩ : 1 ≤ st.bcT.length ∧ st.bcT.length < 2 ^ 32 := by
      obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := Hwf; omega
    ihave %Htsl0 := ownSlice_len _ _ _ $$ Htsl
    have hts0 : (0 : Int) < sint.Z ts.len := by
      rw [List.length_map] at Htsl0; word
    list_elem st.bcT 0 as t0
    wp_if_destruct
    · -- found: the tally of `o`'s id is at `i`
      have hsame : xi.1.sameId o = true := by
        rw [sameId_true_iff]; rw [← Hxid.1, ← Hxid.2, ← Ho.1, ← Ho.2]; exact Hif
      have hz : sint.Z (W64 0) = 0 := rfl
      have ha0 : (st.bcT.map encT)[(0 : Int).toNat]? = some (encT t0) := by
        simp [Ht0_lookup]
      have hv0 : (encT t0).arr[(0 : Int).toNat]? = some (W64 t0.1) := by simp [encT]
      icases slice_array_acc ts _ (st.bcT.map encT) 0 0 (encT t0) (W64 t0.1) (Int.le_refl 0)
        (Int.le_refl 0) ha0 hv0 $$ Htsl with ⟨Ht0, Htsl⟩
      repeat (simp only [hi0, hlt, hz, hts0, Int.le_refl, _root_.and_self, ↓reduceIte]; wp_auto)
      wp_for_post
      ihave Hel := (tally_split _ ({ ti with Count' := ti.Count' + W64 1 } : Tally) _).2 $$ [Hpi Hci]
      · iframe Hpi Hci; ipureintro; exact hni
      ihave Hpsl := Hpsl $$ Hel
      ihave Htsl := Htsl $$ Ht0
      rw [show Int.toNat 0 = 0 from rfl, encT_incr0 st.bcT t0 Ht0_lookup, ← st.addProp_bcT o hT1]
      rw [show (sint.Z i).toNat = sint.nat i by word]
      have hprops := st.addProp_props_found o (st.wf_distinct Hwf) _ xi Hxi_lookup hsame
      ihave #Htl' := talliesRep_set tl st.props (sint.nat i) { ti with Count' := ti.Count' + W64 1 }
        (xi.1, xi.2 + 1) $$ [Htl]
      · iframe Htl
        unfold tallyRep
        iframe Hxo
        ipureintro; simp only [Hxc, W64_succ]
      rw [← hprops]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
          Hbscap Hts Htsl Htscap Hγ Hwk]
      · inext
        unfold slotInv
        iexists st.addProp o
        isplitl [Hwk]
        · simp only [SlotSt.addProp]; iexact Hwk
        unfold slotFields
        iframe Hγ
        isplitl
        · iexists dec, ps, bs, ts, _
          simp only [SlotSt.addProp_isDone, SlotSt.addProp_hasRecvDec, SlotSt.addProp_decision,
            SlotSt.addProp_bc]
          iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl' Hbs Hbsl Hbscap Hts Htsl Htscap
          iexact Hdecrep
        · ipureintro; exact hwf'
      iapply HΦ
      itrivial
    · -- not this one: on to `i + 1`
      have hnot : xi.1.sameId o = false := by
        rcases Bool.eq_false_or_eq_true (xi.1.sameId o) with h | h
        · exfalso; apply Hif
          rw [sameId_true_iff] at h
          rw [Hxid.1, Hxid.2, Ho.1, Ho.2]; exact ⟨h.1, h.2⟩
        · exact h
      ihave Hel := (tally_split _ ti _).2 $$ [Hpi Hci]
      · iframe Hpi Hci; ipureintro; exact hni
      ihave Hpsl := Hpsl $$ Hel
      rw [list_set_lookup_self _ _ _ hti]
      wp_for_post
      iframe
      iexists i + W64 1
      iframe i Hpsl
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k x hk hx
      rcases Nat.lt_or_ge k (sint.nat i) with h | h
      · exact hprev k x h hx
      · have : k = sint.nat i := by word
        subst this; rw [Hxi_lookup] at hx; cases hx; exact hnot
  · obtain ⟨hi0, hil, hprev⟩ := Hi
    have hn : ∀ x ∈ st.props, x.1.sameId o = false := by
      intro x hx
      rcases List.mem_iff_getElem?.1 hx with ⟨k, hk⟩
      have := (List.getElem?_eq_some_iff.1 hk).1
      exact hprev k x (by word) hk
    have hprops := st.addProp_props_new o hn
    wp_apply wp_slice_literal (V := Tally) (t := Tally.ty) [Tally.mk v (W64 1)]
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hz, Hzcap⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hpsl $Hpscap $Hz] as %ps' ⟨Hpsl, Hpscap, -⟩
    obtain ⟨hT1, hT2⟩ : 1 ≤ st.bcT.length ∧ st.bcT.length < 2 ^ 32 := by
      obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := Hwf; omega
    ihave %Htsl0 := ownSlice_len _ _ _ $$ Htsl
    have hts0 : (0 : Int) < sint.Z ts.len := by
      rw [List.length_map] at Htsl0; word
    list_elem st.bcT 0 as t0
    have hz : sint.Z (W64 0) = 0 := rfl
    have ha0 : (st.bcT.map encT)[(0 : Int).toNat]? = some (encT t0) := by
      simp [Ht0_lookup]
    have hv0 : (encT t0).arr[(0 : Int).toNat]? = some (W64 t0.1) := by simp [encT]
    icases slice_array_acc ts _ (st.bcT.map encT) 0 0 (encT t0) (W64 t0.1) (Int.le_refl 0)
      (Int.le_refl 0) ha0 hv0 $$ Htsl with ⟨Ht0, Htsl⟩
    repeat (simp only [hz, hts0, Int.le_refl, _root_.and_self, ↓reduceIte]; wp_auto)
    ihave Htsl := Htsl $$ Ht0
    rw [show Int.toNat 0 = 0 from rfl, encT_incr0 st.bcT t0 Ht0_lookup, ← st.addProp_bcT o hT1]
    ihave #Htl' := talliesRep_app tl st.props (Tally.mk v (W64 1)) (o, 1) $$ [Htl]
    · iframe Htl
      unfold tallyRep
      iframe Hrep
      ipureintro; rfl
    rw [← hprops]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
        Hbscap Hts Htsl Htscap Hγ Hwk]
    · inext
      unfold slotInv
      iexists st.addProp o
      isplitl [Hwk]
      · simp only [SlotSt.addProp]; iexact Hwk
      unfold slotFields
      iframe Hγ
      isplitl
      · iexists dec, ps', bs, ts, _
        simp only [SlotSt.addProp_isDone, SlotSt.addProp_hasRecvDec, SlotSt.addProp_decision,
          SlotSt.addProp_bc]
        iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl' Hbs Hbsl Hbscap Hts Htsl Htscap
        iexact Hdecrep
      · ipureintro; exact hwf'
    iapply HΦ
    itrivial

end proof
end Perennial.rabia.internal.ledger
