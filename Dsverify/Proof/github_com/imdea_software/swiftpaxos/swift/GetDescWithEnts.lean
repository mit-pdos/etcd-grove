/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GetDescWithEnts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**GetDescWithEnts** (round 43, D52 (4)): GetDescWith's lemmas on the entries and the Upsert
lock (`descEnts_insert*`, `descInv_lockLend/Acc/Return`, `descInv_seqTakeL`, …).
-/
module


public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWithLoan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **A spawned goroutine's entry committed** (round 27; Upsert's commit of `k ↦ d`, `k ∉ Mc`):
the entry (running, unsignalled: `descGo`) and its incarnation `γi` (live; the goroutine holds the
other half), from the spawn's quarter of the slot's element, the entry's halves of
`active`/`msgs`/`stopChan`, its quarter and half of `seq`, the channels' bags (with `incW`), and
the signal token. -/
theorem swift.descEnts_insertGo (γ : sp.Names) (γd γn : GName) (g : swift.DescG)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString)
    (Mc : GMap GoString GoInterface) (k : GoString) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) (j : Nat) (m sc : Loc) (γmc γsc : ChanNames)
    (hk : Mc !! k = none) (hky : k = str y) (E : CoPset) (W : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (hW : W !! k = none) :
    ([∗map] k ↦ v ∈ Mc, swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half (k, d) ∗
      ghostVar γi (1 : Qp).half.half (k, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
      ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗
      isChanBag γmc m (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) ∗
      isChanBag γsc sc (fun wg => iprop(swift.stopMP g.γs γsg (str y) d sc wg ∗ □ swift.incW g γi γsg)) ∗
      swift.sgTok γsg ∗ typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ⊢
    |={E}=> ([∗map] k ↦ v ∈ <[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc,
        swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g (<[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc) ∗
      swift.incW g γi γsg := by
  iintro ⟨Hents, HK, Hv, Hvq, Hrc, Hs2, Hs4, Hel, Ha, Hm, #Hmb, #Hsb, Hsg, Hsc⟩
  imod swift.incInv_commit g Mc k d γi γsg true hk E $$ [HK Hv] with ⟨HK, #Hw⟩
  · iframe
  imodintro
  iframe HK Hw
  iapply (BigSepM.bigSepM_insert (Φ := fun k v =>
    swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v)
    (show Iris.Std.PartialMap.get? Mc k = none from hk)).2
  iframe Hents
  iunfold swift.descEnt
  iexists d, y
  isplitr
  · ipureintro; exact ⟨rfl, hky⟩
  rw [hW]
  unfold swift.entW
  ileft
  -- round 38 (P1): the outer `msgs` ¼ and `descGo`'s ¼
  icases (typedPointsto_half_split _ _ _).1 $$ Hm with ⟨Hmo, Hm⟩
  iunfold swift.entS
  iexists false, m
  iframe Hs2 Hmo
  iunfold swift.entI
  iright; ileft
  isplitr
  · ipureintro; rfl
  iunfold swift.descGo
  iexists j, (1 : Qp).half.half, true, sc, γsc, γsg, m, γi
  subst hky
  iframe Hel Hw Hvq Hrc Hs4 Hm
  isplitr
  · iunfold swift.bagW
    iexists γmc, (swift.incW g γi γsg)
    iframe Hmb Hw
  isplitr
  · iunfold swift.stopBag
    iexists (swift.incW g γi γsg)
    iframe Hsb Hw
  -- round 40 (P39-1): the unsignalled branch
  iunfold swift.goSt
  ileft
  simp only [↓reduceIte]
  iframe Ha Hsc
  ileft; iexact Hsg

/-- **A new sequential descriptor's entry committed** (round 27; round 37, table rev 8 G-sqγi and
rev 8b K2): its incarnation committed **live** (the invariant takes half of `γi`; the raw owner
state the other half), the creation (`srOk`, `soOk`'s third clause) of its entry state `sqC` (in
the entry) and raw owner state `g.sr`. -/
theorem swift.descEnts_insertSeq (γ : sp.Names) (γd γn : GName) (g : swift.DescG)
    (str : swift.CommandId → GoString) (DR : Loc → IProp netDistGF)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC0 g)
    (hstr : c0.str = str)
    (Mc : GMap GoString GoInterface) (k : GoString) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) (sqv fqv : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (m sc : Loc) (q : Qp)
    (hk : Mc !! k = none) (hky : k = str y) (E : CoPset) (γe : GName)
    (hγe : γe = g.γS ∨ γe = g.γS2) (W : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (hW : W !! k = none) :
    ([∗map] k ↦ v ∈ Mc, swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g Mc ∗ ghostVar γi 1 (k, d) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
      ghostMapElem γe d (DFrac.own 1) y ∗
      swift.dfld d go!"msgs" ↦ m ∗ isChanBag γm m (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) ∗
      swift.dfld d go!"active" ↦ true ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
      swift.dfld d go!"stopChan" ↦ sc ∗ ghostMapElem c0.γsh d (DFrac.own 1) q ∗
      swift.descRaw c0 RC0 (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) y g.ev.b sqv fqv szS szF
        memS memF γm d ⊢
    |={E}=> ([∗map] k ↦ v ∈ <[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc,
        swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g (<[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc) ∗
      g.sr d y := by
  iintro ⟨Hents, HK, Hv, Hs2, He, Hm, #Hmb, Ha, Hs, Hsc, Hsh, Hraw⟩
  -- round 38 (P1): the outer `msgs` ¼; `seqNew` has ¾
  ihave ⟨Hm, Hmo⟩ := swift.pt_1_34 _ _ $$ Hm
  icases (ghostVar_split_half γi 1 (k, d)).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod swift.incInv_commit g Mc k d γi γsg true hk E $$ [HK Hv1] with ⟨HK, #Hw⟩
  · iframe
  ihave ⟨Hq, Ho⟩ := hSo.2.2.1 γi γsg sqv fqv szS szF memS memF γm m sc q d y
    $$ [Hm Ha Hs Hsc Hsh Hraw Hv2]
  · iunfold swift.seqNew
    rw [hstr, ← hky]
    iframe
    iframe Hmb Hw
  imodintro
  iframe HK Ho
  iapply (BigSepM.bigSepM_insert (Φ := fun k v =>
    swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v)
    (show Iris.Std.PartialMap.get? Mc k = none from hk)).2
  iframe Hents
  iunfold swift.descEnt
  iexists d, y
  isplitr
  · ipureintro; exact ⟨rfl, hky⟩
  rw [hW]
  unfold swift.entW
  ileft
  iunfold swift.entS
  iexists true, m
  iframe Hs2 Hmo
  iunfold swift.entI
  iright; iright
  isplitr
  · ipureintro; rfl
  iunfold swift.sqE
  iexists γe
  iframe He Hq
  ipureintro; exact hγe

/-- **A goroutine's or the inline owner's new sequential descriptor committed** (round 40; table rev
10 T3'c, §3R10.16 #4, C6, gap 40-3): inside the commit, the incarnation committed live; the raw
owner state made by `srOk` goes into the inbox (`seqInbox_add`, refuting a reused key's raw form
with `active` whole, `srA`); the entry gets the inbox's element and `sqC`. -/
theorem swift.descEnts_insertSeqI (γ : sp.Names) (γd γn : GName) (g : swift.DescG)
    (str : swift.CommandId → GoString) (DR : Loc → IProp netDistGF)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hsr : swift.srOk c0 RC0 g) (hsrA : swift.srA g)
    (hstr : c0.str = str)
    (Mc : GMap GoString GoInterface) (k : GoString) (d : Loc) (y : swift.CommandId)
    (γi γsg : GName) (sqv fqv : GoInterface)
    (szS szF : Nat) (memS memF : w32 → Prop) (γm : ChanNames) (m sc : Loc) (q : Qp)
    (hk : Mc !! k = none) (hky : k = str y) (E : CoPset) (hE : ↑swift.seqN ⊆ E)
    (W : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (hW : W !! k = none) :
    inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗
      ([∗map] k ↦ v ∈ Mc, swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g Mc ∗ ghostVar γi 1 (k, d) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
      swift.dfld d go!"msgs" ↦ m ∗ isChanBag γm m (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) ∗
      swift.dfld d go!"active" ↦ true ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
      swift.dfld d go!"stopChan" ↦ sc ∗ ghostMapElem c0.γsh d (DFrac.own 1) q ∗
      swift.descRaw c0 RC0 (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) y g.ev.b sqv fqv szS szF
        memS memF γm d ⊢
    |={E}=> ([∗map] k ↦ v ∈ <[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc,
        swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v) ∗
      swift.incInv g (<[k := interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d]> Mc) := by
  iintro ⟨#HSI, Hlc, Hents, HK, Hv, Hs2, Hm, #Hmb, Ha, Hs, Hsc, Hsh, Hraw⟩
  ihave ⟨Hm, Hmo⟩ := swift.pt_1_34 _ _ $$ Hm
  icases (ghostVar_split_half γi 1 (k, d)).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod swift.incInv_commit g Mc k d γi γsg true hk E $$ [HK Hv1] with ⟨HK, #Hw⟩
  · iframe
  imod swift.seqInbox_add g hsrA d y (swift.sqC d y) E hE $$ [Hlc Ha Hm Hs Hsc Hsh Hraw Hv2] with ⟨He, Hq⟩
  · iframe HSI Hlc Ha
    iintro Ha
    ihave ⟨Hq, Ho⟩ := hsr γi γsg sqv fqv szS szF memS memF γm m sc q d y
      $$ [Hm Ha Hs Hsc Hsh Hraw Hv2]
    · iunfold swift.seqNew
      rw [hstr, ← hky]
      iframe
      iframe Hmb Hw
    iframe
  imodintro
  iframe HK
  iapply (BigSepM.bigSepM_insert (Φ := fun k v =>
    swift.descEnt γ γd g DR (swift.descGo γn g str) str (W !! k) k v)
    (show Iris.Std.PartialMap.get? Mc k = none from hk)).2
  iframe Hents
  iunfold swift.descEnt
  iexists d, y
  isplitr
  · ipureintro; exact ⟨rfl, hky⟩
  rw [hW]
  unfold swift.entW
  ileft
  iunfold swift.entS
  iexists true, m
  iframe Hs2 Hmo
  iunfold swift.entI
  iright; iright
  isplitr
  · ipureintro; rfl
  iunfold swift.sqE
  iexists g.γS2
  iframe He Hq
  ipureintro; exact Or.inr rfl

/-- The running epoch's `FQ` (round 27: the spawn's `newDesc` reads it): half of it, its quorum. -/
theorem swift.epRunL_fq (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (ev : swift.EpV) (γp : GName) (i : Nat) (Qd : Qp) :
    swift.epRunL γ γc γm rp x ev γp i Qd ⊢
    replica.mset.quorumIs ev.fq ev.szF ev.memF ∗
      typedPointsto (swift.fld rp go!"FQ") ev.fq (DFrac.own (1 : Qp).half) ∗
      (typedPointsto (swift.fld rp go!"FQ") ev.fq (DFrac.own (1 : Qp).half) -∗
        swift.epRunL γ γc γm rp x ev γp i Qd) := by
  have hrp : (x.epN rp).rp = rp := rfl
  iintro Hr
  iunfold swift.epRunL at Hr
  icases Hr with ⟨%γl, %q0, Hpool, Hrest, Hrc, Hfil, Hrm, %Hst⟩
  iunfold swift.epochPool at Hpool
  icases Hpool with ⟨Ha, Hsh, Hc⟩
  iunfold swift.epochShare at Hsh
  icases Hsh with ⟨Hrd, Hx, Hs, Hf⟩
  iunfold swift.fqShare at Hf
  icases Hf with ⟨HF, #Hq, %Hm⟩
  iunfold swift.epochRest at Hrest
  icases Hrest with ⟨Hs1, HS1, HS2, Hr1, He1, Hxe1, Hxp1, HFQ⟩
  simp only [hrp]
  iframe Hq HFQ
  iintro HFQ
  iunfold swift.epRunL
  iexists γl, q0
  iframe Hrc Hfil Hrm
  isplitl [Ha Hrd Hx Hs HF Hc]
  · iunfold swift.epochPool
    iframe Ha Hc
    iunfold swift.epochShare
    iunfold swift.fqShare
    simp only [hrp]
    iframe Hrd Hx Hs HF Hq
    ipureintro; exact Hm
  isplitl [Hs1 HS1 HS2 Hr1 He1 Hxe1 Hxp1 HFQ]
  · iunfold swift.epochRest
    simp only [hrp]
    iframe
  ipureintro; exact Hst

theorem swift.elem_quarters (γ : GName) (k : Nat) (v : Bool) :
    ghostMapElem (GF := netDistGF) γ k (DFrac.own (1 : Qp).half) v ⊣⊢
      ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v ∗
        ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp).half]
  exact (ghostMapElem_fractional k γ v).fractional _ _

/-- Upsert's commit with its continuation weakened (round 27: both cases of the callback end in one
state `A`, then the same tail). -/
theorem swift.commit_mono (E : CoPset) (V V' : GMap GoString GoInterface → IProp netDistGF)
    (P : GMap GoString GoInterface → Prop) (A B : IProp netDistGF) :
    (▷ |={E, ∅}=> ∃ M, V M ∗ (⌜P M⌝ -∗ V' M -∗ |={∅, E}=> A)) ∗ (A -∗ B) ⊢
    ▷ |={E, ∅}=> ∃ M, V M ∗ (⌜P M⌝ -∗ V' M -∗ |={∅, E}=> B) := by
  iintro ⟨H, HAB⟩
  inext
  imod H with ⟨%M, HV, Hk⟩
  imodintro
  iexists M
  iframe HV
  iintro %HP HV'
  imod Hk $$ %HP HV' with HA
  imodintro
  iapply HAB $$ HA

/-- `descDS`'s persistent context (round 37b). -/
theorem swift.descDS_ctx (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    swift.descDS γ γc γm x rp ⊢ swift.descDSCtx rp x := by
  iintro H
  iunfold swift.descDS at H
  icases H with ⟨%g, %ev, %γp, %i, -, -, -, -, #HDctx, -⟩
  iexact HDctx

/-- **The run loop's part of an owner's context** (round 37b, sv-swb; table rev 8c §3.17,
GAP-37b with GAP-37d): `proposeCtxB` of the kind-free record and the history pair, from
`runLoopCtx` (with `descDSCtx`'s quorum of `SQ`, which `runLoopCtx` does not keep). -/
theorem swift.runLoopCtx_ownB (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢
      □ (swift.descDSCtx rp x -∗ swift.proposeCtxB (x.dc γ γc γm rp) ∗
        (∃ hsl : GoSlice, swift.fld rp go!"history" ↦□ hsl ∗
          sync.isMutex (swift.fld rp go!"historyL") (swift.historyLInv hsl))) := by
  iintro Hrl
  iunfold swift.runLoopCtx at Hrl
  icases Hrl with ⟨%s, %b, %γs, %sq, %hsl, %fr, %pl, %sam, %csv, %n, -, #Fsnd, #Hsbag, #Fbt, #Hbh,
    -, #Fhist, -, -, #Ffr, -, -, #Fsam, #Hsam, -, -, #Fufp, -, #Fcs, %Hcs, -, -, #HhL, -, -, -, -,
    %lg, #Hcfg⟩
  imodintro
  iintro #Hdc
  iunfold swift.descDSCtx at Hdc
  icases Hdc with ⟨-, -, -, -, ⟨%sq', %szS, %memS, #FSQ, #HqS, %HmS⟩, -⟩
  isplitr
  · iunfold swift.proposeCtxB
    isplitr
    · iunfold swift.ackCtx
      iexists sq', szS, memS, b, s, γs, csv
      iframe FSQ HqS Fbt Hbh Fsnd Hsbag Fcs
      isplitr
      · ipureintro; exact HmS
      isplitr
      · ipureintro; exact Hcs
      iexists _; iexact Fufp
    iexists sam, fr, lg, _
    iframe Fsam Hsam Ffr Hcfg Fufp
  iexists hsl
  iframe Fhist HhL

/-! ### Round 38 (table rev 9a T5l/T5r, plan R9a.2): the lock-lend

A lock holder (UpsertVL's callback, existing branch) reads `desc.seq` and `desc.msgs` (non-atomic,
E8) with fractions of the entry's **outer** part, lent out of `descInv` (`entL`); its deposit (its
lock token at `t`, its refuter `lendRef ρ`) and `γw`'s half name the lend, so the return gives the
same token back (R9-2, C3). The entry's inner part `entI` stays in place: the stop arm (T19) never
waits on a lender (P1). Both lemmas take the caller's not-stopped witness (C2). These replace round
37's `descInv_lendL`/`descInv_returnL` (GAP-37a sorries). -/

/-- The entries but one keep their state when `W` changes only at that key. -/
theorem swift.descEnts_W_ne (γ : sp.Names) (γd : GName) (g : swift.DescG)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (M : GMap GoString GoInterface) (k : GoString)
    (W W' : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (hM : ∀ k' v, Iris.Std.PartialMap.get? M k' = some v → k' ≠ k)
    (hW : ∀ k', k' ≠ k → W' !! k' = W !! k') :
    ([∗map] k' ↦ v ∈ M, swift.descEnt γ γd g DR Run str (W !! k') k' v) ⊢
      [∗map] k' ↦ v ∈ M, swift.descEnt γ γd g DR Run str (W' !! k') k' v := by
  apply BigSepM.bigSepM_mono
  intro k' v hk'
  rw [hW k' (hM k' v hk')]
  try exact .rfl

theorem swift.delete_ne (Mc : GMap GoString GoInterface) (k : GoString) :
    ∀ k' v, Iris.Std.PartialMap.get? (Iris.Std.PartialMap.delete Mc k) k' = some v → k' ≠ k := by
  intro k' v h
  exact fun e => (Iris.Std.LawfulPartialMap.get?_delete_some_iff.1 h).1 e.symm

/-- **An entry's bag witness** (round 38, table rev 9a C1): from the inner part, a home's or a
running goroutine's `bagW` at the `msgs` the outer part holds; a sequential entry has none (`s`). -/
theorem swift.entI_bag (γ : sp.Names) (DR : Loc → IProp netDistGF) (γn : GName) (g : swift.DescG)
    (str : swift.CommandId → GoString) (d : Loc) (y : swift.CommandId) (s : Bool) (m : Loc)
    (q : Qp) :
    swift.entI γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y s ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own q) ⊢
    swift.entI γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y s ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own q) ∗
      □ (⌜s = false⌝ -∗ swift.bagW m (g.mp y)) := by
  iintro ⟨H, Hm⟩
  iunfold swift.entI at H
  icases H with (⟨%hs, Hh⟩ | ⟨%hs, Hr⟩ | ⟨%hs, Hq⟩)
  · iunfold swift.descHomeS at Hh
    icases Hh with ⟨%m', %sc, %sl, %fa, %a, Hm', #Hb, Hrest⟩
    icombine Hm Hm' gives %hm
    subst hm
    iframe Hm
    isplitl [Hm' Hrest]
    · iunfold swift.entI
      ileft
      isplitr
      · ipureintro; exact hs
      iunfold swift.descHomeS
      iexists m, sc, sl, fa, a
      isplitl [Hm']
      · iexact Hm'
      isplitr
      · iexact Hb
      iexact Hrest
    imodintro
    iintro -
    iexact Hb
  · iunfold swift.descGo at Hr
    icases Hr with ⟨%j, %qj, %a, %sc, %γc, %γsg, %m', %γi, Hel, Hw, Hvi, Hrci, Hsq, Hms, #Hmb, Hrest⟩
    icombine Hm Hms gives %hm
    subst hm
    iframe Hm
    isplitl [Hel Hw Hvi Hrci Hsq Hms Hrest]
    · iunfold swift.entI
      iright; ileft
      isplitr
      · ipureintro; exact hs
      iunfold swift.descGo
      iexists j, qj, a, sc, γc, γsg, m, γi
      iframe Hel Hw Hvi Hrci Hsq Hms Hmb
      iexact Hrest
    imodintro
    iintro -
    iexact Hmb
  · iframe Hm
    isplitl [Hq]
    · iunfold swift.entI
      iright; iright
      iframe Hq
      ipureintro; exact hs
    imodintro
    iintro %h
    subst hs
    cases h

/-- **The descriptors' message predicates carry `deliver`'s `int` payload fact** (round 39, D43 (5)):
every `descMP` alternative is a pointer, a string, or a slot's `int` (a `w64`). -/
theorem swift.mpOk_ty (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (hmp : swift.mpOk x γ γc γm rp g) (y : swift.CommandId) (W : IProp netDistGF) :
    swift.mpTy (fun v => iprop(g.mp y v ∗ W)) := by
  intro m
  have hmp' : g.mp = _ := hmp
  simp only [hmp']
  iintro ⟨H, -⟩
  iunfold swift.descMP at H
  iunfold swift.ackMsgP at H
  icases H with ((⟨%l, %fa, ⟨%hm, -⟩, -⟩ | ⟨%l, %sa, %hm, -⟩ | %hs) |
    ⟨%pm, %gp, %cc, %dep, %hs, %sq, %ld, %s, %B, %D, %P, %H, %hm, -⟩ | Hsl | Hse)
  · ipureintro; intro ii hii hty; subst hm; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)
  · ipureintro; intro ii hii hty; subst hm; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)
  · ipureintro; intro ii hii hty; obtain ⟨s, hs⟩ := hs; subst hs; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)
  · ipureintro; intro ii hii hty; subst hm; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)
  · iunfold swift.slotMP at Hsl
    icases Hsl with ⟨%s, ⟨%hm, -⟩, -⟩
    ipureintro; intro ii hii hty; subst hm; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)
  · iunfold swift.syncMP at Hse
    icases Hse with ⟨%se, %gp, %c, %vs, %dsl, %D, %M, %i, %hm, -⟩
    ipureintro; intro ii hii hty; subst hm; simp only [interface.mkOk] at hii; injection hii with hii; subst hii; first | exact ⟨_, rfl⟩ | (cases hty) | (simp at hty) | (exfalso; revert hty; decide)

/-- **The lock-lend** (T5l; round 38, plan R9a.2): see the section header. A deposit already there
(`W !! k = some _`) holds another lock token of `k` (`cmapLocked_excl`); a read-lent entry holds a
pin (`cmapLocked_pin_false`). -/
theorem swift.descInv_lockLend (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface)
    (t : github_com.orcaman.concurrent_map.CmapLock) (ρ : swift.LendK) (Wt : IProp netDistGF) (hWt : swift.liveOk g Wt) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗ Wt ∗
      github_com.orcaman.concurrent_map.cmapLocked g.γdc k (some v) t ∗ swift.lendRef g k ρ ⊢
    |={⊤}=> Wt ∗ ∃ (d : Loc) (y : swift.CommandId) (s : Bool) (m : Loc),
      ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y⌝ ∗
      typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half.half) ∗
      □ (⌜s = false⌝ -∗ swift.bagW m (g.mp y)) ∗
      ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) := by
  iintro ⟨#HI, Hlc, HWt, Hlk, Href⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  imod github_com.orcaman.concurrent_map.cmapLocked_lookup (⊤ \ ↑swift.descN) swift.descN_cmap_sub
    g.γdc k (some v) t Mc $$ [Hlk Hview] with ⟨Hlk, Hview, %Hk⟩
  · iframe
  icases (BigSepM.bigSepM_delete Hk).1 $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d, %y, %Hv, Hs⟩
  cases hW : W !! k with
  | some o =>
    obtain ⟨t', ρ', v'⟩ := o
    unfold swift.entW
    icases Hs with ⟨-, Hs⟩
    iunfold swift.entL at Hs
    icases Hs with ⟨%s, %m, -, -, -, Hlk2, -, -⟩
    iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_excl (⊤ \ ↑swift.descN) swift.descN_cmap_sub
      g.γdc k (some v) (some v) t t' Mc $$ [Hlk Hlk2 Hview]
    iframe
  | none =>
  unfold swift.entW
  icases Hs with (Hs | ⟨%π, -, Hpin, -⟩)
  rotate_left
  · iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_pin_false (⊤ \ ↑swift.descN)
      swift.descN_cmap_sub g.γdc k (some v) t v π.half Mc $$ [Hlk Hpin Hview]
    iframe
  iunfold swift.entS at Hs
  icases Hs with ⟨%s, %m, Hs, Hm, HIn⟩
  ihave ⟨HIn, Hm, #Hbag⟩ := swift.entI_bag γ DR γn g str d y s m _ $$ [HIn Hm]
  · iframe
  icases (typedPointsto_half_split _ _ _).1 $$ Hs with ⟨Hs1, Hs2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  imod ghost_map_insert (γ := g.γw) k (t, ρ, v) hW $$ HW with ⟨HW, Hwel⟩
  icases (ghostMapElem_halves g.γw k (t, ρ, v)).1 $$ Hwel with ⟨Hw1, Hw2⟩
  imod Hclose $$ [Hst2 Hview HW Hents HK Hpool Hrec Hled Hrca Hs1 Hm1 Hw1 Hlk Href HIn] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, (W.insert k (t, ρ, v))
    iframe Hview HW HK Hpool Hrec Hled Hrca
    isplitr
    · ipureintro
      intro k' hk'
      by_cases e : k = k'
      · subst e; rw [Hk]; simp
      · rw [GMap.lookup_insert_ne W _ e] at hk'; exact HWd k' hk'
    iapply (BigSepM.bigSepM_delete Hk).2
    isplitl [Hs1 Hm1 Hw1 Hlk Href HIn]
    · iunfold swift.descEnt
      iexists d, y
      isplitr
      · ipureintro; exact Hv
      rw [GMap.lookup_insert W k (t, ρ, v)]
      unfold swift.entW
      isplitr
      · ipureintro; rfl
      iunfold swift.entL
      iexists s, m
      iframe Hs1 Hm1 Hw1 Hlk Href HIn
    iapply (swift.descEnts_W_ne γ γd g DR (swift.descGo γn g str) str _ k W (W.insert k (t, ρ, v))
      (swift.delete_ne Mc k) (fun k' h => GMap.lookup_insert_ne W _ (Ne.symm h))) $$ Hents
  imodintro
  iframe HWt
  iexists d, y, s, m
  iframe Hs2 Hm2 Hw2 Hbag
  ipureintro; exact Hv

/-- Opening `descInv` at a lock-lent key (round 38): the entry is `k`'s, lock-lent at our `γw`
half; the caller's update `upd` changes the lent entry (its value, its descriptor `d`). -/
theorem swift.descInv_lockAcc (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface)
    (t : github_com.orcaman.concurrent_map.CmapLock) (ρ : swift.LendK) (d : Loc)
    (Hv : v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)
    (Wt P Q : IProp netDistGF) (hWt : swift.liveOk g Wt)
    (upd : ∀ y : swift.CommandId, k = str y →
      P ∗ ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
        swift.entL γ DR (swift.descGo γn g str) (swift.sqE g) g.mp g k v t ρ d y ⊢
      |={⊤ \ ↑swift.descN}=> Q ∗ ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
        swift.entL γ DR (swift.descGo γn g str) (swift.sqE g) g.mp g k v t ρ d y) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗ Wt ∗
      ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗ P ⊢
    |={⊤}=> Wt ∗ ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗ Q := by
  iintro ⟨#HI, Hlc, HWt, Hw, HP⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  ihave %hW := ghost_map_lookup $$ HW Hw
  cases hMk : Mc !! k with
  | none => exact absurd hMk (HWd k (by rw [show W !! k = W.lookup k from rfl, hW]; simp))
  | some v0 =>
  icases (BigSepM.bigSepM_delete hMk).1 $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y, %Hv', Hs⟩
  rw [show W !! k = W.lookup k from rfl, hW]
  unfold swift.entW
  icases Hs with ⟨%Hvv, Hs⟩
  subst Hvv
  have hd : d' = d := swift.mkOk_desc_inj d' d (Hv'.1.symm.trans Hv)
  subst hd
  imod upd y Hv'.2 $$ [HP Hw Hs] with ⟨HQ, Hw, Hs⟩
  · iframe
  imod Hclose $$ [Hst2 Hview HW Hents HK Hpool Hrec Hled Hrca Hs] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe Hview HW HK Hpool Hrec Hled Hrca
    isplitr
    · ipureintro; exact HWd
    iapply (BigSepM.bigSepM_delete hMk).2
    iframe Hents
    iunfold swift.descEnt
    iexists d', y
    isplitr
    · ipureintro; exact Hv'
    rw [show W !! k = W.lookup k from rfl, hW]
    unfold swift.entW
    isplitr
    · ipureintro; rfl
    iexact Hs
  imodintro
  iframe

/-- **The lock-return** (T5r; round 38, plan R9a.2): `γw`'s halves agree, so the deposit is the
caller's (`t`, `ρ`, the value `v` and its descriptor `d`); the token and the refuter come back,
the outer part is whole again, `γw`'s key is deleted. -/
theorem swift.descInv_lockReturn (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface)
    (t : github_com.orcaman.concurrent_map.CmapLock) (ρ : swift.LendK) (d : Loc) (s : Bool) (m : Loc) (Wt : IProp netDistGF)
    (hWt : swift.liveOk g Wt)
    (Hv : v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗ £ 1 ∗ Wt ∗
      ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
      typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half.half) ⊢
    |={⊤}=> Wt ∗ github_com.orcaman.concurrent_map.cmapLocked g.γdc k (some v) t ∗
      swift.lendRef g k ρ := by
  iintro ⟨#HI, Hlc, HWt, Hw, Hs4, Hm8⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  cases st
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    have hWt' := hWt
    unfold swift.liveOk at hWt'
    iapply hWt' $$ [HWt Hst2 Hrest]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  ihave %hW := ghost_map_lookup $$ HW Hw
  cases hMk : Mc !! k with
  | none => exact absurd hMk (HWd k (by rw [show W !! k = W.lookup k from rfl, hW]; simp))
  | some v0 =>
  icases (BigSepM.bigSepM_delete hMk).1 $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y, %Hv', Hs⟩
  rw [show W !! k = W.lookup k from rfl, hW]
  unfold swift.entW
  icases Hs with ⟨%Hvv, Hs⟩
  subst Hvv
  have hd : d' = d := swift.mkOk_desc_inj d' d (Hv'.1.symm.trans Hv)
  subst hd
  iunfold swift.entL at Hs
  icases Hs with ⟨%s', %m', Hs', Hm', Hw', Hlk, Href, HIn⟩
  ihave ⟨%hs, Hs⟩ := typedPointsto_half_combine _ s s' (1 : Qp).half $$ [Hs4 Hs']
  · iframe
  ihave ⟨%hm, Hm⟩ := typedPointsto_half_combine _ m m' (1 : Qp).half.half $$ [Hm8 Hm']
  · iframe
  ihave Hwel := (ghostMapElem_halves g.γw k (t, ρ, v)).2 $$ [Hw Hw']
  · iframe
  imod ghost_map_delete $$ HW Hwel with HW
  imod Hclose $$ [Hst2 Hview HW Hents HK Hpool Hrec Hled Hrca Hs Hm HIn] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, (W.delete k)
    iframe Hview HW HK Hpool Hrec Hled Hrca
    isplitr
    · ipureintro
      intro k' hk'
      by_cases e : k = k'
      · subst e; rw [hMk]; simp
      · rw [GMap.lookup_delete_ne W e] at hk'; exact HWd k' hk'
    iapply (BigSepM.bigSepM_delete hMk).2
    isplitl [Hs Hm HIn]
    · iunfold swift.descEnt
      iexists d', y
      isplitr
      · ipureintro; exact Hv'
      rw [GMap.lookup_delete W k]
      unfold swift.entW
      ileft
      iunfold swift.entS
      iexists s', m'
      iframe Hs Hm HIn
    iapply (swift.descEnts_W_ne γ γd g DR (swift.descGo γn g str) str _ k W (W.delete k)
      (swift.delete_ne Mc k) (fun k' h => GMap.lookup_delete_ne W (Ne.symm h))) $$ Hents
  imodintro
  iframe HWt Hlk Href

/-- **T7s's owner-state move while lock-lent** (round 38, gap 38-1, table §3R9.19): the lent
entry's inner part is sequential (our `seq` share is `true`); its element moves the owner state
to the run loop's store (`seqTake`), and comes back as `γS`'s. -/
theorem swift.descInv_seqTakeL (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (str : swift.CommandId → GoString) (hinj : Function.Injective str)
    (c0 : swift.DC) (RC0 : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC0 g)
    (k : GoString) (v : GoInterface) (t : github_com.orcaman.concurrent_map.CmapLock) (ρ : swift.LendK) (d : Loc) (y : swift.CommandId)
    (Wt : IProp netDistGF) (hWt : swift.liveOk g Wt)
    (Hv : v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR (swift.descGo γn g str) str) ∗
      inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗ £ 1 ∗ Wt ∗
      ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗ swift.seqStore g ⊢
    |={⊤}=> Wt ∗ ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
      ∃ S : GMap Loc swift.CommandId, ⌜S !! d = some y⌝ ∗ ghostMapAuth g.γS 1 S ∗
        ([∗map] d' ↦ y' ∈ S.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
        g.so d y := by
  iintro ⟨#HI, #HSI, Hlc, Hlc2, HWt, Hw, Hs4, HSS⟩
  iapply swift.descInv_lockAcc γ γd γn γout g ep DR str k v t ρ d Hv.1 Wt
    iprop(inv swift.seqN (swift.seqInbox g) ∗ £ 1 ∗
      typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗ swift.seqStore g)
    iprop(typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
      ∃ S : GMap Loc swift.CommandId, ⌜S !! d = some y⌝ ∗ ghostMapAuth g.γS 1 S ∗
        ([∗map] d' ↦ y' ∈ S.delete d, g.so d' y' ∨ ghostMapElem g.γS d' (DFrac.own 1) y') ∗
        g.so d y) hWt
  · intro y' hy'
    have hyy : y' = y := hinj (hy'.symm.trans Hv.2)
    subst hyy
    iintro ⟨⟨#HSI, Hlc2, Hs4, HSS⟩, Hw, Hs⟩
    iunfold swift.entL at Hs
    icases Hs with ⟨%s', %m', Hs', Hm', Hw', Hlk, Href, HIn⟩
    icombine Hs4 Hs' gives %hs
    subst hs
    iunfold swift.entI at HIn
    icases HIn with (⟨%h, -⟩ | ⟨%h, -⟩ | ⟨-, Hq⟩)
    · cases h
    · cases h
    iunfold swift.sqE at Hq
    icases Hq with ⟨%γe, %Hγe, Hel, Hq⟩
    imod swift.seqTake γ DR g c0 RC0 hSo γe Hγe d y' (⊤ \ ↑swift.descN) swift.seqN_desc_sub
      $$ [HSI Hlc2 Hel HSS] with ⟨Hel, %S, %HSd, HSA, HSm, Hso⟩
    · iframe HSI; iframe
    imodintro
    iframe Hw Hs4
    isplitl [HSA HSm Hso]
    · iexists S
      iframe HSA HSm Hso
      ipureintro; exact HSd
    iunfold swift.entL
    iexists true, m'
    iframe Hs' Hm' Hw' Hlk Href
    iunfold swift.entI
    iright; iright
    isplitr
    · ipureintro; rfl
    iunfold swift.sqE
    iexists g.γS
    iframe Hel Hq
    ipureintro; exact Or.inl rfl
  iframe HI HSI Hlc HWt Hw Hlc2 Hs4 HSS

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
