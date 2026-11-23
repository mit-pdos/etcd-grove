/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/StopDescs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`stopDescs`' exit** (round 17, sv-swb; after the fork's SWB-14 fix 982c3e9, notes/prove-swift.md
§23): `stopDescs` returns after a round that stopped none and a read of `routineCount <= 0` under
`cntL`. At that read `cntL`'s registry is empty (`swift.cntLGhost … c []`, `c = 0`), and the run
loop freezes it (`swift.cntLGhost_freeze`). A running entry of the descriptors' invariant holds a
share of its goroutine's registered loan (`hRun`: a `ghostMapElem γn i (own q) false`, `i ≠ 0`),
so with the registry empty every entry is at home: the run loop takes the whole view and every
entry's `descHome` (`swift.descInv_take_frozen`), closing the invariant at `st = true`.

* `swift.bigSepM_frame_mono`: a big separating map rewritten entry by entry with a frame `R`
  (here `cntL`'s registry authority) threaded through;
* `swift.descEntH`: an entry at home; `swift.descEnt_home_of`: a `descEnt` is one, given the
  registry with no loan;
* `swift.descInv_take_frozen`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CntL

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- An entry of the stopped descriptors (the descriptor at home, whole). -/
def swift.descEntH (γ : sp.Names) (γd : GName) (DR : Loc → IProp netDistGF)
    (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (d : Loc) (y : swift.CommandId),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y⌝ ∗
    swift.descHome γ (swift.descDF DR) d y)

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

instance swift.qp_inhabited : Inhabited Qp := ⟨1⟩

instance swift.cntFrozen_timeless (γn : GName) (f : Bool) : Timeless (swift.cntFrozen γn f) := by
  unfold swift.cntFrozen; infer_instance

instance swift.epochShare_timeless (ep : swift.EpN) (ev : swift.EpV) (q : Qp) :
    Timeless (swift.epochShare ep ev q) := by
  unfold swift.epochShare swift.epochRd swift.epochTok swift.fqShare replica.mset.quorumIs replica.quorum.qOwn; infer_instance

theorem swift.bigSepM_frame_mono (R : IProp netDistGF)
    (Φ Ψ : GoString → GoInterface → IProp netDistGF)
    (h : ∀ k v, R ∗ Φ k v ⊢ R ∗ Ψ k v) :
    ∀ m : GMap GoString GoInterface,
      R ∗ ([∗map] k ↦ v ∈ m, Φ k v) ⊢ R ∗ [∗map] k ↦ v ∈ m, Ψ k v := by
  apply GMap.map_ind
  · iintro ⟨HR, -⟩
    iframe HR
    iapply BigSepM.bigSepM_empty.2; itrivial
  · intro k v m hk ih
    iintro ⟨HR, Hm⟩
    icases (BigSepM.bigSepM_insert hk).1 $$ Hm with ⟨Hx, Hm⟩
    ihave ⟨HR, Hy⟩ := h k v $$ [HR Hx]
    · iframe
    ihave ⟨HR, Hm⟩ := ih $$ [HR Hm]
    · iframe
    iframe HR
    iapply (BigSepM.bigSepM_insert hk).2
    iframe

/-- The same for the sub-pool's loans (`Nat ↦ Qp`). -/
theorem swift.bigSepM_frame_mono_nq (R : IProp netDistGF) (Φ Ψ : Nat → Qp → IProp netDistGF)
    (h : ∀ k v, R ∗ Φ k v ⊢ R ∗ Ψ k v) :
    ∀ m : GMap Nat Qp, R ∗ ([∗map] k ↦ v ∈ m, Φ k v) ⊢ R ∗ [∗map] k ↦ v ∈ m, Ψ k v := by
  apply GMap.map_ind
  · iintro ⟨HR, -⟩
    iframe HR
    iapply BigSepM.bigSepM_empty.2; itrivial
  · intro k v m hk ih
    iintro ⟨HR, Hm⟩
    icases (BigSepM.bigSepM_insert hk).1 $$ Hm with ⟨Hx, Hm⟩
    ihave ⟨HR, Hy⟩ := h k v $$ [HR Hx]
    · iframe
    ihave ⟨HR, Hm⟩ := ih $$ [HR Hm]
    · iframe
    iframe HR
    iapply (BigSepM.bigSepM_insert hk).2
    iframe

/-- The frozen registry (`cntL`'s authority with no loan, the run loop's flag at `true`)
refutes any share of a loan's element at `false`. -/
theorem swift.frozen_no_elem (γn : GName) (L : GMap Nat Bool) (f : Bool) (hL : swift.cntLMap L f [])
    (j : Nat) (qj : Qp) :
    ghostMapAuth γn 1 L ∗ swift.cntFrozen γn true ∗ ghostMapElem γn j (DFrac.own qj) false ⊢
      False := by
  iintro ⟨Ha, Hf, Hel⟩
  icombine Ha Hel gives %Hl
  by_cases hj : j = 0
  · subst hj
    iunfold swift.cntFrozen at Hf
    icombine Hf Hel gives %Hc
    exfalso; simp at Hc
  · exfalso
    rw [hL j] at Hl
    simp [hj] at Hl

/-- A `descHomeS` with the entry's outer part (`seq` ½; round 38, P1: `msgs` ¼): the descriptor at
home, whole. -/
theorem swift.descHomeS_whole (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (MPy : GoInterface → IProp netDistGF) (d : Loc)
    (y : swift.CommandId) (s : Bool) (m' : Loc) :
    swift.descHomeS γ DR MPy d y s ∗
      typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"msgs") m' (DFrac.own (1 : Qp).half.half) ⊢
      swift.descHome γ (swift.descDF DR) d y := by
  iintro ⟨Hh, Hs2, Hm2⟩
  iunfold swift.descHomeS at Hh
  icases Hh with ⟨%m, %sc, %sl, %fa, %a, Hm, -, Hsc, Hsl, Hfa, Hfs, Hff, Ha, Hs1, %Has, HDR⟩
  ihave ⟨-, Hm⟩ := swift.pt_34_14 _ m m' $$ [Hm Hm2]
  · iframe
  unfold swift.descHome swift.descFree swift.descDF
  iexists m, sc, sl, fa
  iframe Hm Hsc Hsl Hfa Hfs Hff
  iexists a, s
  ihave ⟨-, Hs⟩ := typedPointsto_half_combine _ s s (1 : Qp) $$ [Hs1 Hs2]
  · iframe
  iframe Ha HDR Hs
  ipureintro; exact Has

/-- A whole fraction and another share of one ghost variable: impossible (round 37). -/
theorem swift.qp_one_add_le (q : Qp) (h : 1 + q ≤ 1) : False := by
  have := q.2; simp at h; grind

/-- **The frozen state's refuters of a lock-lend** (round 38, table rev 9 T20): the run loop's round
map at `∅` refutes `run`'s element; the receipts' authority with no loan refutes `own`'s. -/
def swift.lendDead (g : swift.DescG) : IProp netDistGF :=
  iprop(ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
    ∃ LJ : GMap Nat (Nat × Qp), ghostMapAuth g.γlj 1 LJ ∗ ⌜∀ i, LJ !! i = none⌝)

theorem swift.lendDead_ref (g : swift.DescG) (k : GoString) (ρ : swift.LendK) :
    swift.lendDead g ∗ swift.lendRef g k ρ ⊢ (False : IProp netDistGF) := by
  iintro ⟨HD, Hr⟩
  iunfold swift.lendDead at HD
  icases HD with ⟨HS, %LJ, HJ, %HLJ⟩
  rcases ρ with _ | ⟨iL, j⟩
  · unfold swift.lendRef
    ihave %h := ghost_map_lookup $$ HS Hr
    simp at h
  · unfold swift.lendRef
    ihave %h := ghost_map_lookup $$ HJ Hr
    rw [HLJ iL] at h
    cases h

/-- With the registry frozen and no entry lent (`γb` whole at `none`, round 37; round 38: no
lock-lend either, `lendDead`), an entry is at home. -/
theorem swift.descEnt_home_of (γ : sp.Names) (γd γn : GName) (g : swift.DescG)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString)
    (hRun : ∀ d y, Run d y ⊢ ∃ (i : Nat) (q : Qp), ghostMapElem γn i (DFrac.own q) false)
    (c0 : swift.DC) (RC : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC g)
    (L : GMap Nat Bool) (f : Bool) (hL : swift.cntLMap L f [])
    (W : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (k : GoString) (v : GoInterface) :
    (ghostMapAuth γn 1 L ∗ swift.cntFrozen γn true ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ swift.seqStore g ∗
        swift.seqInbox g ∗ swift.lendDead g) ∗
      swift.descEnt γ γd g DR Run str (W !! k) k v ⊢
      (ghostMapAuth γn 1 L ∗ swift.cntFrozen γn true ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ swift.seqStore g ∗
        swift.seqInbox g ∗ swift.lendDead g) ∗
        swift.descEntH γ γd DR str k v := by
  iintro ⟨⟨Ha, Hf, Hb, HS, HS2, HD⟩, He⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d, %y, %Hv, Hst⟩
  cases hW : W !! k with
  | some o =>
    obtain ⟨t, ρ, v'⟩ := o
    unfold swift.entW
    icases Hst with ⟨-, Hst⟩
    iunfold swift.entL at Hst
    icases Hst with ⟨%s, %m, -, -, -, -, Hr, -⟩
    iexfalso
    iapply swift.lendDead_ref g k ρ $$ [HD Hr]
    iframe
  | none =>
  unfold swift.entW
  icases Hst with (Hst | ⟨%π, Hb2, -, -⟩)
  rotate_left
  · icombine Hb Hb2 gives %Hc
    exact (swift.qp_one_add_le _ Hc.1).elim
  iunfold swift.entS at Hst
  icases Hst with ⟨%s, %mo, Hseq, Hmo, Hh⟩
  iunfold swift.entI at Hh
  icases Hh with (⟨-, Hh⟩ | ⟨-, Hr⟩ | ⟨%Hs1, Hq⟩)
  · iframe Ha Hf Hb HS HS2 HD
    iunfold swift.descEntH
    iexists d, y
    isplitr
    · ipureintro; exact Hv
    iapply swift.descHomeS_whole $$ [Hh Hseq Hmo]
    iframe
  rotate_left
  · subst Hs1
    -- round 29 (G11): the owner state from the store the entry's element names
    iunfold swift.sqE at Hq
    icases Hq with ⟨%γe, %Hγe, Hel, Hq⟩
    rcases Hγe with Hγe | Hγe <;> subst Hγe
    · iunfold swift.seqStore at HS
      icases HS with ⟨%S, HSa, HSm⟩
      ihave %HSd := ghost_map_lookup $$ HSa Hel
      icases (BigSepM.bigSepM_delete HSd).1 $$ HSm with ⟨Hso, HSm⟩
      icases Hso with (Hso | Hel2)
      rotate_left
      · iexfalso
        icombine Hel Hel2 gives %Hc
        exfalso; have := DFrac.valid_own_op Hc.1; simp at this
      ihave Hh := hSo.2.1 d y $$ [Hq Hso]
      · iframe
      iframe Ha Hf Hb HS2 HD
      isplitl [HSa HSm Hel]
      · iunfold swift.seqStore
        iexists S
        iframe HSa
        iapply (BigSepM.bigSepM_delete HSd).2
        iframe HSm
        iright; iexact Hel
      iunfold swift.descEntH
      iexists d, y
      isplitr
      · ipureintro; exact Hv
      iapply swift.descHomeS_whole $$ [Hh Hseq Hmo]
      iframe
    · iunfold swift.seqInbox at HS2
      icases HS2 with ⟨%S, HSa, HSm⟩
      ihave %HSd := ghost_map_lookup $$ HSa Hel
      icases (BigSepM.bigSepM_delete HSd).1 $$ HSm with ⟨Hso, HSm⟩
      icases Hso with (Hso | Hel2)
      rotate_left
      · iexfalso
        icombine Hel Hel2 gives %Hc
        exfalso; have := DFrac.valid_own_op Hc.1; simp at this
      ihave Hso := hSo.2.2.2.2.1 d y $$ Hso
      ihave Hh := hSo.2.1 d y $$ [Hq Hso]
      · iframe
      iframe Ha Hf Hb HS HD
      isplitl [HSa HSm Hel]
      · iunfold swift.seqInbox
        iexists S
        iframe HSa
        iapply (BigSepM.bigSepM_delete HSd).2
        iframe HSm
        iright; iexact Hel
      iunfold swift.descEntH
      iexists d, y
      isplitr
      · ipureintro; exact Hv
      iapply swift.descHomeS_whole $$ [Hh Hseq Hmo]
      iframe
  · ihave ⟨%i, %q, Hel⟩ := hRun d y $$ Hr
    iexfalso
    iapply swift.frozen_no_elem γn L f hL i q $$ [Ha Hf Hel]
    iframe

/-- The sub-pool's records refute themselves once frozen: every loan back. -/
theorem swift.loanRec_frozen (γn γlj : GName) (ep : swift.EpN) (ev : swift.EpV)
    (L0 : GMap Nat Bool) (f : Bool) (hL : swift.cntLMap L0 f []) (L : GMap Nat Qp) :
    (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗ swift.loanRec γn γlj L ⊢
      (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗
        [∗map] _i ↦ q ∈ L, swift.epochShare ep ev q := by
  iunfold swift.loanRec
  iapply swift.bigSepM_frame_mono_nq _ _ _ _ L
  intro i q
  iintro ⟨⟨Ha, Hf⟩, ⟨%j, %qj, Hel, -⟩⟩
  iexfalso
  iapply swift.frozen_no_elem γn L0 f hL j qj $$ [Ha Hf Hel]
  iframe

/-- Once frozen, the sub-pool has no loan (round 24: each loan's record is a registry element,
refuted by the frozen flag). -/
theorem swift.loanRec_empty (γn γlj : GName) (L0 : GMap Nat Bool) (f : Bool)
    (hL : swift.cntLMap L0 f []) (L : GMap Nat Qp) :
    (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗ swift.loanRec γn γlj L ⊢
      (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗ ⌜L = ∅⌝ := by
  iintro ⟨⟨Ha, Hf⟩, Hrec⟩
  by_cases hE : L = ∅
  · iframe Ha Hf; ipureintro; exact hE
  · have hk : ∃ k q, L !! k = some q := by
      apply Classical.byContradiction; intro h
      apply hE
      apply GMap.map_eq
      intro k
      simp only [GMap.lookup_empty]
      cases hk : L !! k with
      | none => rfl
      | some q => exact absurd ⟨k, q, hk⟩ h
    obtain ⟨k, q, hk⟩ := hk
    iunfold swift.loanRec at Hrec
    icases (BigSepM.bigSepM_delete hk).1 $$ Hrec with ⟨⟨%j, %qj, Hel, -⟩, -⟩
    iexfalso
    iapply swift.frozen_no_elem γn L0 f hL j qj $$ [Ha Hf Hel]
    iframe

/-- **Once frozen, the ledger is empty** (round 34, table rev 4-6 T20): each out key's body is a
registry element at `false`, refuted by the frozen flag; the epoch's half of `Out` (at `∅`) goes to
the run loop (it moves to the next epoch's `descInv`). -/
theorem swift.ledgerD_empty (γn γout : GName) (L0 : GMap Nat Bool) (f : Bool)
    (hL : swift.cntLMap L0 f []) :
    (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗ swift.ledgerD γn γout ⊢
      (ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗
        ghostMapAuth γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) := by
  iintro ⟨⟨Ha, Hf⟩, Hled⟩
  iunfold swift.ledgerD at Hled
  icases Hled with ⟨%Out, HO, Hb⟩
  by_cases hE : Out = ∅
  · subst hE; iframe
  · have hk : ∃ k jq, Out !! k = some jq := by
      apply Classical.byContradiction; intro h
      apply hE
      apply GMap.map_eq
      intro k
      simp only [GMap.lookup_empty]
      cases hk : Out !! k with
      | none => rfl
      | some q => exact absurd ⟨k, q, hk⟩ h
    obtain ⟨k, jq, hk⟩ := hk
    icases (BigSepM.bigSepM_delete hk).1 $$ Hb with ⟨Hel, -⟩
    iexfalso
    iapply swift.frozen_no_elem γn L0 f hL jq.1 jq.2 $$ [Ha Hf Hel]
    iframe

/-- **A goroutine's "epoch not stopped" fact** (round 24): its loan token of the descriptors'
sub-pool refutes the stopped invariant's empty loan authority. -/
theorem swift.loan_not_stopped (γq : GName) (i : Nat) (q : Qp) :
    ghostMapAuth γq 1 (∅ : GMap Nat Qp) ∗ swift.epochLoan γq i q ⊢ (False : IProp netDistGF) := by
  iintro ⟨Ha, He⟩
  iunfold swift.epochLoan at He
  ihave %h := ghost_map_lookup $$ Ha He
  simp at h

/-- **`stopDescs`' exit, its ghost core** (round 18): with `cntL`'s registry empty and frozen
(`cntLGhost … c []`, the run loop's flag at `true`) and no borrow of `stopDescs` outstanding,
the run loop takes the descriptors' whole view, every entry at home, the sub-pool's share
back, and closes the invariant stopped. Round 51 (49-2, D70 (4)): the incarnations' state
`incInv g Mc` is kept (it was dropped), for the stopped carrier. -/
theorem swift.descInv_take_frozen (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG)
    (ep : swift.EpN) (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString)
    (hRun : ∀ d y, Run d y ⊢ ∃ (i : Nat) (q : Qp), ghostMapElem γn i (DFrac.own q) false)
    (c0 : swift.DC) (RC : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC g)
    (dm : GoSlice) (γdl : GName) (dd c : w64) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗
      ghostVar g.γst (1 : Qp).half false ∗
      swift.cntLGhost γn dm γdl dd c [] ∗ swift.cntFrozen γn true ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗
      swift.seqStore g ∗ inv swift.seqN (swift.seqInbox g) ∗
      ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ⊢
    |={⊤}=> swift.cntLGhost γn dm γdl dd c [] ∗ swift.cntFrozen γn true ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗
      ghostVar g.γst (1 : Qp).half true ∗ swift.epochShare ep g.ev g.Qd ∗
      ghostMapAuth γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
      (∃ dm1 : GoSlice, typedPointsto (swift.fld ep.rp go!"cmdDescs") dm1 (DFrac.own (1 : Qp).half)) ∗
      ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
      ∃ Mc : GMap GoString GoInterface, github_com.orcaman.concurrent_map.cmapView g.γdc Mc ∗
        ▷ ([∗map] k ↦ v ∈ Mc, swift.descEntH γ γd DR str k v) ∗ ▷ swift.incInv g Mc := by
  iintro ⟨#HI, Hst, Hg, Hf, Hb, HS, #HSI, HSs⟩
  iinv HI with Hi Hclose
  imod (inv_acc (E := ⊤ \ ↑swift.descN) (N := swift.seqN) swift.seqN_desc_sub) $$ HSI with ⟨HS2, Hclose2⟩
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, >Hst2, Hrest⟩
  icombine Hst Hst2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, >Hview, -, -, Hents, Hinc, Hpool, Hrec, Hled, Hrca⟩
  imod ghostVar_update_halves true g.γst false false $$ Hst Hst2 with ⟨Hst, Hst2⟩
  iunfold swift.cntLGhost at Hg
  icases Hg with ⟨%L0, %f, Ha, H0, %Hp, Hr⟩
  -- round 38 (table rev 9 T20): no loan, so no `own` lock-lend; R's round map ∅, so no `run` one
  ihave Hfr0 : ▷ ((ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗ ⌜L = ∅⌝) $$ [Ha Hf Hrec]
  · inext
    iapply swift.loanRec_empty γn g.γlj L0 f Hp.1 L
    iframe
  icases Hfr0 with ⟨⟨>Ha, >Hf⟩, >%HL⟩
  subst HL
  ihave Hfr : ▷ ((ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true ∗ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗
      swift.seqStore g ∗ swift.seqInbox g ∗ swift.lendDead g) ∗
      [∗map] k ↦ v ∈ Mc, swift.descEntH γ γd DR str k v) $$ [Ha Hf Hb HS HS2 Hents HSs Hrca]
  · inext
    ihave HD : swift.lendDead g $$ [HSs Hrca]
    · iunfold swift.rcptAuth at Hrca
      icases Hrca with ⟨%LJ, HJ, %HLJ, -⟩
      iunfold swift.lendDead
      iframe HSs
      iexists LJ
      iframe HJ
      ipureintro
      intro i
      apply Classical.byContradiction
      intro h
      exact HLJ i h (GMap.lookup_empty i)
    iapply swift.bigSepM_frame_mono _ _ _
      (swift.descEnt_home_of γ γd γn g DR Run str hRun c0 RC hSo L0 f Hp.1 W) Mc
    iframe
  icases Hfr with ⟨⟨>Ha, >Hf, >Hb, -, HS2, HD⟩, Hents⟩
  imod Hclose2 $$ HS2 with -
  ihave Hsh : ▷ ((ghostMapAuth γn 1 L0 ∗ swift.cntFrozen γn true) ∗
      swift.epochShare ep g.ev g.Qd ∗
      typedPointsto (swift.fld ep.rp go!"cmdDescs") dm1 (DFrac.own (1 : Qp).half) ∗
      ghostMapAuth g.γq 1 (∅ : GMap Nat Qp) ∗
      ghostMapAuth γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
      ghostMapAuth g.γs 1 (∅ : GMap GoString Bool)) $$ [Ha Hf Hpool Hled HD]
  · inext
    ihave ⟨Hfr, Hout⟩ := swift.ledgerD_empty γn γout L0 f Hp.1 $$ [Ha Hf Hled]
    · iframe
    iframe Hout
    iunfold swift.lendDead at HD
    icases HD with ⟨HSs, -⟩
    iframe HSs
    unfold swift.epochPoolX swift.poolS
    icases Hpool with ⟨Hγq, Hsh0, Hw⟩
    iframe Hfr Hγq
    ihave Hx := Hw $$ Hsh0
    ihave Hx := Hx $$ [] 
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iunfold swift.epochShareX at Hx
    icases Hx with ⟨Hx1, Hx2⟩
    icases (swift.descX_Qd ep.rp γd g dm1).1 $$ Hx2 with ⟨Hcd, -⟩
    iframe
  icases Hsh with ⟨⟨>Ha, >Hf⟩, >Hsh, >Hcd, >Hγq, >Hout, >HSs⟩
  imod Hclose $$ [Hst2 Hγq] with -
  · inext
    iunfold swift.descInv
    iexists true
    simp only [↓reduceIte]
    iframe Hst2 Hγq
  imodintro
  iframe Hst Hf Hb Hsh Hout HSs
  isplitl [Ha H0 Hr]
  · iunfold swift.cntLGhost
    iexists L0, f
    iframe
    ipureintro; exact Hp
  isplitl [Hcd]
  · iexists dm1; iexact Hcd
  iexists Mc
  iframe

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
