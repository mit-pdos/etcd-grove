/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecEpilogue.lean`, run `rabia-r1wake-1`.)

The proofs of the executor's `putBackMyProposal` and `epilogue` (`wp_putBackMyProposal`'s and
`wp_epilogue`'s statements).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecWait
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecBefore

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

theorem SlotOk.set_done {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit} (o : ObjV)
    (h : SlotOk cf s st ents ql p exd dl rl) :
    SlotOk cf s { st with isDone := true, decision := o } ents ql p true dl rl := by
  unfold SlotOk at *
  obtain ⟨a, b, c, d, e, f, _, _, i⟩ := h
  exact ⟨a, b, c, d, e, f, rfl, fun _ => rfl, i⟩

/-- `SetDecision`'s step in `epilogue`: the slot done (the executor's mirror), its `decInfo`. -/
theorem step_setDecision (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (t : Nat)
    (d : DVal) (o : ObjV) (cmds : List GoString) (E : CoPset) (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc t st -∗
      (ghostVar (exName γl γc t) (1 : Qp).half false ∗ fact γ.rab (.dec t) (.dval d) ∗
        decObjOk γ cf t d o ∗ prefixFacts γ.rab t cmds) ={E}=∗
      slotGhost γ cf k γl γc t { st with isDone := true, decision := o } ∗
      decInfo γ cf t { st with isDone := true, decision := o } ∗ iprop(True) := by
  iintro Hg ⟨Hx', #Hdec, #Hdo, #Hpf⟩
  unfold slotGhost
  icases Hg with ⟨%ents, %ql, %pend, %exd, %dl, %rl, Hent, Hq, Hp, Hx, Hdw, Hrd, Hres, %hok⟩
  imod ghostVar_update_halves (A := Bool) true (exName γl γc t) exd false $$ Hx Hx' with ⟨Hx, -⟩
  imodintro
  isplitl [Hent Hq Hp Hx Hdw Hrd Hres]
  · iexists ents, ql, pend, true, dl, rl
    iframe
    ipureintro; exact hok.set_done o
  isplitr
  · unfold decInfo
    simp only [↓reduceIte]
    iexists d, cmds
    iframe Hdec Hdo Hpf
  · itrivial

end ghost

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS] [math.rand.Hyps GF]

theorem wp_putBackMyProposal_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames)
    (γc : ConsNames) (ch : SrvChans) (c : Loc) (s : Nat) (e : SlotV) (pv : PrivSt)
    (hs : s < lenLedger) :
    {{ exPre (GF := GF) γ cf ∗ consRO γ cf k γl γc ch c ∗ ⌜γl.slots[s]? = some e⌝ ∗ slotPriv e.loc pv ∗
        pendOk γ cf γl pv.myProp }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"putBackMyProposal"))
        (Val #(W32 s)))
    {{ RET #(); slotPriv e.loc pv }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, #Hro, %he, Hpriv, Hpend⟩
  have hs' : (W32 (s : Int)).toNat < lenLedger := by unfold lenLedger at *; word
  wp_auto
  wp_apply (wp_PanicTermNotMatched γ k γl γc ch c (W32 (s : Int)) hs') $$ [$Hconf $Hro]
  ihave ⟨%ps, #HConf⟩ := confRO_val $$ Hconf
  ihave Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %qlk, %wg, #Hsid, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hqlk,
    #Hledger, #Hqm, #Hsm, #Hchans, #HlRO, #Hsinv, #Hschans, #Hkeys⟩
  ihave Hc2 := HConf
  iStructNamed Hc2
  unfold ledgerRO
  icases HlRO with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at hs Hl hs'
  have hmod : W32 (s : Int) % W32 10000 = W32 (s : Int) := by word
  ihave ⟨Hph, Hrnd, ⟨%mpv, Hmpf, #Hmpo⟩, %Rr, HRr, Hpcl⟩ := (slotPriv_fields e.loc pv).1 $$ Hpriv
  wp_auto
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (s : Int))))) _ _ e.loc
    (by word) $$ [Hsl]
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (s : Int))))).toNat = s by word]
    simp [he]
  iintro -
  wp_auto
  ihave #HroF : consRO γ cf k γl γc ch c $$ []
  · unfold consRO ledgerRO; iexact Hro
  wp_apply (wp_QPush D.push γ k γl γc ch c mpv pv.myProp) $$ [$HroF $Hmpo $Hpend]
  ihave Hpriv := Hpcl $$ %pv.phase %pv.round %mpv [Hph Hrnd Hmpf HRr]
  · iframe Hph Hrnd Hmpf HRr; iexact Hmpo
  have hpveq : ({ pv with phase := pv.phase, round := pv.round } : PrivSt) = pv := rfl
  rw [hpveq]
  iapply HΦ
  iexact Hpriv

theorem ex_SetDecision_t (hspec : Slot.SetDecision.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (v : ConsensusObj) (o : ObjV) (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ objRep v o -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s { st with isDone := true, decision := o } ∗
          decInfo γ cf s { st with isDone := true, decision := o } ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #()) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"SetDecision")) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hv #Hi HR Hstep HΦ
  iapply wp_SetDecision_inv hspec γ k γl γc s e he v o R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hv | isplitr)

theorem blockLen_le {c : RCfg} (hc : c.Ok) : 1 ≤ c.blockLen ∧ c.blockLen ≤ 10 := by
  have h4 := hc.2.2.2
  unfold RCfg.blockLen
  generalize c.blocks = b at h4 ⊢
  match b, h4 with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

theorem wp_epilogue_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames)
    (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) (d : DVal) (o : ObjV) (v : ConsensusObj)
    (hd : FKey.mydec k σ.t ∈ σ.Ke) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ decidedW γ cf k σ.t d o v ∗
        fact γ.rab (.prop k σ.t) (.obj (objId x.o)) }}
      (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"epilogue"))
        (Val #(W32 σ.t))) (Val #v))
    {{ RET #(); ∃ σ', exIdle γ cf k γl γc ch c σ' ∗ ⌜σ'.t = σ.t + 1⌝ }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun, Hdw, #Hprop⟩
  ihave ⟨#Hro, Hrun⟩ := exRun_ro γ k γl γc ch c σ x $$ Hrun
  unfold exRun
  icases Hrun with ⟨Hcom, Hcoin, Hseq, %ht, Hsr⟩
  unfold exSlotRes
  icases Hsr with ⟨%e, %he, Hpriv, %hmy, Hpend, Hcons, #Hql, %hq, Hex⟩
  unfold decidedW
  icases Hdw with ⟨#Hmy, #Hdec, #Hdo, #Hv⟩
  iunfold exCommon at Hcom
  icases Hcom with ⟨-, Hfields, #Hhist, Hmt, %hHlen, #Hpf, HKe, %hKeys, Hexa, Hprod, %hlog,
    Hfresh⟩
  have hs' : (W32 (σ.t : Int)).toNat < lenLedger := by unfold lenLedger at *; word
  wp_auto
  wp_apply (wp_PanicTermNotMatched γ k γl γc ch c (W32 (σ.t : Int)) hs') $$ [$Hconf $Hro]
  ihave #HroF : consRO γ cf k γl γc ch c $$ []
  · iexact Hro
  ihave ⟨%ps, #HConf⟩ := confRO_val $$ Hconf
  ihave Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %qlk, %wg, #Hsid, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hqlk,
    #Hledger, #Hqm, #Hsm, #Hchans, #HlRO, #Hsinv, #Hschans, #Hkeys⟩
  ihave Hc2 := HConf
  iStructNamed Hc2
  unfold ledgerRO
  icases HlRO with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  unfold lenLedger at ht Hl hs'
  have hmod : W32 (σ.t : Int) % W32 10000 = W32 (σ.t : Int) := by word
  wp_auto
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
    (by word) $$ [Hsl]
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
    simp [he]
  iintro -
  wp_pures
  wp_apply_core ex_SetDecision_t D.setDecision γ k γl γc σ.t e he v o
    iprop(ghostVar (exName γl γc σ.t) (1 : Qp).half false ∗ fact γ.rab (.dec σ.t) (.dval d) ∗
        decObjOk γ cf σ.t d o ∗ prefixFacts γ.rab σ.t σ.cmds)
    (fun _ => iprop(True)) $$ Hpl Hse Hv Hsinv [Hex]
  · iframe Hex; iframe #
  · iintro %st Hg HR
    iapply step_setDecision $$ Hg HR
  iintro %st -
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsm] as ⟨Hlocked, Hst⟩
  unfold statInv
  icases Hst with ⟨%na, %nb, %nd, %ne, Hna, Hnb, Hnd, Hne⟩
  unfold exFields
  icases Hfields with ⟨⟨%mp, %dm, Hdm, Hmap⟩, ⟨%ca, %cb, %cd, Hca, Hcb, Hcd⟩, ⟨%tr, Htr⟩,
    ⟨%hsl, %hxs, Hhsl, Hhxs, %hlen⟩⟩
  ihave %hvo := objRep_fields v o $$ Hv
  have hs3 : σ.t < lenLedger := by unfold lenLedger; omega
  wp_join iprop(statInv c ∗
      (∃ (mp : GoMap) (dm : GMap w64 Bool), structFieldRef Consensus go!"Discard" c ↦ mp ∗
        ownMap mp (DFrac.own 1) dm) ∗
      (∃ (a b d : w64), structFieldRef Consensus go!"CurrConsecutiveNulls" c ↦ a ∗
        structFieldRef Consensus go!"MaxConsecutiveNulls" c ↦ b ∗
        structFieldRef Consensus go!"MaxConsecutiveNullsEndSeq" c ↦ d) ∗
      slotPriv e.loc x.pv ∗
      (if d = .obj (objId x.o) then pendOk γ cf γl x.o else iprop(emp)) ∗
      c_ptr ↦ c ∗ seq_ptr ↦ (W32 (σ.t : Int)) ∗ slot_ptr ↦ (W32 (σ.t : Int)))
    at next with [Hna Hnb Hnd Hne Hdm Hmap Hca Hcb Hcd Hpriv Hpend dec c seq slot]
    as ⟨Hstat, Hdisc, Hnulls, Hpriv, Htok, c, seq, slot⟩
  · cases d with
    | null =>
      unfold decObjOk
      icases Hdo with %hn
      have hvn : v.IsNull' = true := hvo.2.2.2.trans hn.1
      rw [hvn]
      wp_auto
      ihave Hpend : pendOk γ cf γl x.pv.myProp $$ [Hpend]
      · rw [hmy]; iexact Hpend
      ihave #HroG : consRO γ cf k γl γc ch c $$ []
      · unfold consRO ledgerRO statInv; iexact HroF
      wp_apply (wp_putBackMyProposal_proof D γ k γl γc ch c σ.t e x.pv hs3) $$
        [$Hpriv $Hpend $HroG] as Hpriv
      · isplitl []
        · isplitl []
          · iexact Hpkg
          isplitl []
          · iexact Hconf
          isplitl []
          · iexact Hsh
          · iexact Hcfg
        · ipureintro; exact he
      unfold statInv
      iframe
      isplitr
      · ipureintro; rfl
      simp only [reduceCtorEq, ↓reduceIte]
      iempintro
    | obj id =>
      unfold decObjOk
      icases Hdo with ⟨%hid, #Hook⟩
      ihave %hnn : ⌜o.isNull = false⌝ $$ [Hook]
      · unfold objOk; icases Hook with ⟨%rs0, -, -, %h⟩; ipureintro; exact h.1
      have hvn : v.IsNull' = false := hvo.2.2.2.trans hnn
      rw [hvn]
      wp_auto
      wp_join iprop((∃ (b1 d1 : w64),
          structFieldRef Consensus go!"MaxConsecutiveNulls" c ↦ b1 ∗
          structFieldRef Consensus go!"MaxConsecutiveNullsEndSeq" c ↦ d1) ∗
          c_ptr ↦ c ∗ dec_ptr ↦ v ∗
          structFieldRef Consensus go!"CurrConsecutiveNulls" c ↦ ca)
        with [Hcb Hcd c dec Hca] as ⟨⟨%b1, %d1, Hcb, Hcd⟩, c, dec, Hca⟩
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
        (by word) $$ [Hsl]
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
        simp [he]
      iintro -
      ihave ⟨Hph, Hrnd, ⟨%mpv, Hmpf, #Hmpo⟩, %Rr, HRr, Hpcl⟩ := (slotPriv_fields e.loc x.pv).1 $$ Hpriv
      ihave #Hpm : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message $$ []
      · iPkgInit
      wp_pures
      wp_apply (D.seqIdEq dec_ptr _ v mpv (DFrac.own 1) (DFrac.own 1)) $$ [$Hpm $dec $Hmpf]
        as ⟨dec, Hmpf⟩
      ihave Hpriv := Hpcl $$ %x.pv.phase %x.pv.round %mpv [Hph Hrnd Hmpf HRr]
      · iframe Hph Hrnd Hmpf HRr; iexact Hmpo
      have hpveq : ({ x.pv with phase := x.pv.phase, round := x.pv.round } : PrivSt) = x.pv := rfl
      rw [hpveq]
      ihave %hmf := objRep_fields mpv x.pv.myProp $$ Hmpo
      have hmatch : (v.ProSeq' = mpv.ProSeq' ∧ v.ProId' = mpv.ProId') ↔
          DVal.obj id = DVal.obj (objId x.o) := by
        rw [hvo.2.1, hvo.1, hmf.2.1, hmf.1, hmy, ← hid.1]
        simp only [objId, DVal.obj.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h2], by rw [h1]⟩
        · rintro ⟨h1, h2⟩; exact ⟨BitVec.eq_of_toNat_eq h2, BitVec.eq_of_toNat_eq h1⟩
      rw [← decide_not]
      wp_if_destruct
      · -- unmatched
        have hne : ¬ (DVal.obj id = DVal.obj (objId x.o)) := fun h => Hif (hmatch.2 h)
        ihave Hpend : pendOk γ cf γl x.pv.myProp $$ [Hpend]
        · rw [hmy]; iexact Hpend
        ihave #HroG : consRO γ cf k γl γc ch c $$ []
        · unfold consRO ledgerRO statInv; iexact HroF
        wp_apply (wp_putBackMyProposal_proof D γ k γl γc ch c σ.t e x.pv hs3) $$
          [$Hpriv $Hpend $HroG] as Hpriv
        · isplitl []
          · isplitl []
            · iexact Hpkg
            isplitl []
            · iexact Hconf
            isplitl []
            · iexact Hsh
            · iexact Hcfg
          · ipureintro; exact he
        wp_apply wp_idSeqKey dec_ptr v $$ [$Hpkg $dec] as %key dec
        wp_apply wp_mapInsert go.uint64 mp dm key true $$ [$Hmap] as Hmap
        unfold statInv
        iframe
        rw [if_neg hne]
        isplitl []
        · ipureintro; rfl
        · iempintro
      · -- matched
        have heq : DVal.obj id = DVal.obj (objId x.o) := hmatch.1 (Classical.not_not.1 Hif)
        unfold statInv
        iframe
        rw [ite_cond_eq_true _ _ (eq_true heq)]
        iexact Hpend
  wp_apply sync.Mutex.wp_Unlock $$ [$Hsm $Hlocked Hstat]
  · unfold statInv; iexact Hstat
  ihave ⟨Hph, Hrnd, ⟨%mpv, Hmpf, #Hmpo⟩, %Rr, HRr, Hpcl⟩ := (slotPriv_fields e.loc x.pv).1 $$ Hpriv
  rw [if_pos (show 0 ≤ sint.Z (W64 (uint.Z (W32 (σ.t : Int)))) ∧
      sint.Z (W64 (uint.Z (W32 (σ.t : Int)))) < sint.Z ledger.len by constructor <;> word)]
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
    (by word) $$ [Hsl]
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
    simp [he]
  iintro -
  wp_pures
  wp_load
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 (uint.Z (W32 (σ.t : Int)))) ∧
      sint.Z (W64 (uint.Z (W32 (σ.t : Int)))) < sint.Z ledger.len by constructor <;> word)]
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
    (by word) $$ [Hsl]
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
    simp [he]
  iintro -
  wp_pures
  wp_load
  wp_auto
  wp_join iprop(∃ n : w32, currentRoundNum_ptr ↦ n) with [currentRoundNum]
    as ⟨%n1, currentRoundNum⟩
  · wp_if_destruct
    all_goals try wp_if_destruct
    all_goals
      isplitl []
      · itrivial
      · iexists _; iframe
  ihave %Hhl := ownSlice_len _ _ _ $$ Hhxs
  rw [hlen] at Hhl
  ihave %hcok := cfgIs_ok γ.rab cf $$ Hcfg
  have hbl := blockLen_le hcok
  wp_join iprop((∃ n2 : w32, currentRoundNum_ptr ↦ n2 ∗ ⌜uint.Z n2 < 2 * cf.blockLen + 2⌝) ∗
      structFieldRef Consensus go!"NumOfRoundsDist" c ↦ hsl ∗ c_ptr ↦ c)
    with [currentRoundNum Hhsl c]
    as ⟨⟨%n2, currentRoundNum, %hn2⟩, Hhsl, c⟩
  · iframe; ipureintro; word
  · iframe; ipureintro; word
  have hidx : (sint.Z (W64 (uint.Z n2))).toNat < hxs.length := by rw [hlen]; word
  rw [if_pos (show 0 ≤ sint.Z (W64 (uint.Z n2)) ∧ sint.Z (W64 (uint.Z n2)) < sint.Z hsl.len by
    constructor <;> word)]
  wp_auto
  obtain ⟨y, hy⟩ : ∃ y, hxs[(sint.Z (W64 (uint.Z n2))).toNat]? = some y :=
    ⟨_, List.getElem?_eq_getElem hidx⟩
  rw [if_pos (show 0 ≤ sint.Z (W64 (uint.Z n2)) ∧ sint.Z (W64 (uint.Z n2)) < sint.Z hsl.len by
    constructor <;> word)]
  wp_apply wp_load_slice_index hsl (sint.Z (W64 (uint.Z n2))) hxs (DFrac.own 1) y (by word)
    $$ [Hhxs]
  · iframe Hhxs; ipureintro; exact hy
  iintro Hhxs
  wp_apply wp_store_slice_index hsl (sint.Z (W64 (uint.Z n2))) hxs (y + W64 1) $$ [Hhxs] as Hhxs
  · iframe Hhxs; ipureintro; constructor <;> word
  -- the next slot's state
  ihave ⟨%cmds', #Hpf'⟩ : ∃ cmds', prefixFacts γ.rab (σ.t + 1) cmds' $$ []
  · cases d with
    | null =>
      iexists σ.cmds
      simp only [prefixFacts]
      iexists σ.cmds, DVal.null
      iframe Hpf Hdec
      ipureintro; rfl
    | obj id =>
      unfold decObjOk
      icases Hdo with ⟨%hid, #Hook⟩
      unfold objOk
      icases Hook with ⟨%rs0, #Hpo, #Hreg, -⟩
      iexists σ.cmds ++ o.commands
      simp only [prefixFacts]
      iexists σ.cmds, DVal.obj id
      iframe Hpf Hdec
      iexists rs0, o.commands
      rw [← hid.1]
      iframe Hpo Hreg
      ipureintro; rfl
  ihave #Hhist' : histFacts γ k (σ.H ++ [(x.o, d)]) $$ []
  · unfold histFacts
    iapply BigSepL.bigSepL_snoc.2
    iframe Hhist
    rw [hHlen]
    iframe Hprop Hmy
  ihave Hmt' : matchedToks γ cf γl (σ.H ++ [(x.o, d)]) $$ [Hmt Htok]
  · unfold matchedToks
    iapply BigSepL.bigSepL_snoc.2
    iframe Hmt
    iexact Htok
  ihave #HroG : consRO γ cf k γl γc ch c $$ []
  · unfold consRO ledgerRO statInv; iexact HroF
  iapply HΦ
  iexists { σ with t := σ.t + 1, H := σ.H ++ [(x.o, d)], cmds := cmds' }
  isplitl
  · unfold exIdle exCommon exFields exCoinOk
    icases Hcoin with ⟨%r0, %rv, Hcf, -⟩
    have hseq : ((σ.t + 1 : Nat) : Int) - 1 = (σ.t : Int) := by omega
    dsimp only
    rw [hseq]
    iframe HroG Hhist' Hmt' Hpf' HKe Hexa Hprod Hfresh Hseq Hdisc Hnulls Htr Hhsl Hhxs
    iframe
    ipureintro
    refine ⟨⟨by rw [List.length_set, hlen], by simp [hHlen], ?_, hlog.1, hlog.2.1, ?_⟩,
      by unfold lenLedger; omega⟩
    · refine ⟨fun key hk => ?_, fun key hk => by simp at hk⟩
      obtain ⟨s0, hs0, hlt⟩ := hKeys.1 key hk
      exact ⟨s0, hs0, Or.inl (by omega)⟩
    · refine ⟨fun m hm s0 ρ hr => ?_, fun ρ hρ => by omega⟩
      rcases hlog.2.2.1 m hm s0 ρ hr with h | h
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
  · ipureintro; rfl


end proof

end Perennial.rabia.roles.server.layers.consensus
