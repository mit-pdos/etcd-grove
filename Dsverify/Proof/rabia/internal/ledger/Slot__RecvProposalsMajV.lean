/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__RecvProposalsMajV.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).RecvProposalsMajV`.
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

theorem Slot.RecvProposalsMajV.wp_proof
    (wp_Lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) :
    Slot.RecvProposalsMajV.spec (GF := GF) := fun s γ q => by
  iintro #Hpkg #Hslot
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
  ihave HΦ : |={⊤}=> (⌜st.props ≠ []⌝ ∗
      ghostVar γ (1 : Qp).half { st with props := sortProps st.props } ∗
      ∀ v : ConsensusObj, objRep v ((sortProps st.props).head?.map (·.1)).get! -∗ Φ #v) $$ [AU Hγ]
  · imod AU with ⟨%x, Hα, -, Hcommit⟩
    rcases x with ⟨st0, ⟨⟩⟩
    dsimp only [Tele.app]
    icases Hα with ⟨Hst, %Hne⟩
    unfold slotSt
    icombine Hγ Hst gives %H
    obtain ⟨_, Heq⟩ := H
    subst Heq
    imod ghostVar_update_halves { st with props := sortProps st.props } γ st st $$ Hγ Hst
      with ⟨Hγ, Hst⟩
    imod Hcommit $$ %() Hst with HΦ
    imodintro
    iframe Hγ
    isplitr
    · ipureintro; exact Hne
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iexact HΦ
  iapply fupd_wp
  imod HΦ with ⟨%Hne, Hγ, HΦ⟩
  imodintro
  iNamed Hf
  ihave Hown : ownTallies ps st.props $$ [Hpsl]
  · unfold ownTallies; iexists tl; iframe Hpsl Htl; ipureintro; exact st.wf_props_cnt Hwf
  wp_apply Slot.wp_SortRecvProposals wp_Lt s ps st.props (st.wf_distinct Hwf)
    (st.wf_props_len Hwf) $$ [$Hps $Hown] as ⟨Hps, Hown⟩
  · iexact Hsort
  unfold ownTallies
  iNamedSuffix Hown "'"
  ihave %Hl := ownSlice_len _ _ _ $$ Hpsl'
  ihave %Hlen := talliesRep_len _ _ $$ Htl'
  have hsl : (sortProps st.props).length = st.props.length := by
    simp only [sortProps, List.length_mergeSort]
  have hpos : 0 < st.props.length := List.length_pos_iff.2 Hne
  list_elem tl 0 as t0
  list_elem (sortProps st.props) 0 as x0
  have h0 : 0 < sint.Z ps.len := by word
  icases ownSlice_elem_acc 0 t0 ps _ tl (Int.le_refl 0) Ht0_lookup $$ Hpsl' with ⟨He, Hpsl'⟩
  have hz : sint.Z (W64 0) = 0 := rfl
  simp only [hz, h0, Int.le_refl, and_self, ↓reduceIte]
  wp_auto
  ihave #Hx0 := talliesRep_lookup tl _ 0 t0 x0 Ht0_lookup Hx0_lookup $$ Htl'
  ihave Hpsl' := Hpsl' $$ He
  rw [show Int.toNat 0 = 0 from rfl, list_set_lookup_self _ _ _ Ht0_lookup]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl' Hpscap Hbs Hbsl
      Hbscap Hts Htsl Htscap Hγ Hwk]
  · inext
    unfold slotInv
    iexists { st with props := sortProps st.props }
    isplitl [Hwk]
    · iexact Hwk
    unfold slotFields
    iframe Hγ
    isplitl
    · iexists dec, ps, bs, ts, tl
      iframe Hdone Hrecv Hdec Hps Hpsl' Hpscap Htl' Hbs Hbsl Hbscap Hts Htsl Htscap
      iexact Hdecrep
    · ipureintro; exact st.wf_sort Hwf
  iapply HΦ
  unfold tallyRep
  icases Hx0 with ⟨#Hx0, -⟩
  rw [List.head?_eq_getElem?, Hx0_lookup]
  simp only [Option.map_some, Option.get!_some]
  iexact Hx0

end proof
end Perennial.rabia.internal.ledger
