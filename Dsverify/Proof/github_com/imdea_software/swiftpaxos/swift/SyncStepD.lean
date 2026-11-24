/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncStepD.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's ballot-changing steps through the node invariant with the epoch and the row
tokens (`swift.nodeInvD`, Proof/swift/DescNode.lean): a new ballot (`handleNewLeader`), the new
leader's computed `MSync` (`handleNewLeaderAckNs`, allocating the order's row tokens), and the
taking of an `MSync` (`handleSync`, with the epoch's whole half: the row tokens of the `MSync`'s
commands allocated (a follower) or updated (the new leader), accepted).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescNode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncStep

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

-- `sp.recOrderStep_nodup`, `sp.recOrder_nodup`, `sp.syncOrder_nodup`: moved to Local.lean (SWB-7).

-- `swift.insAll`, `swift.insAll_lookup`: moved to DescNode.lean (round 32, generic in the value).

/-- A replica's sequences with a new row `(b', o)` first. -/
theorem swift.locAt_cons (st st' : sp.RState) (b' : Nat) (o : List sp.CmdId)
    (hL : st'.locR = (b', o) :: st.locR) (b : Nat) :
    st'.locAt b = if b = b' then o else st.locAt b := by
  unfold sp.RState.locAt; rw [hL]
  by_cases h : b = b'
  · subst h; simp
  · simp [h, Ne.symm h]

/-- A step adding the row `(b', o)` (no row of `b'` before), keeping every command's rows, sets
the row tokens of `o` in `b'` to `rv`: `rowsOk` holds if `rv` is the new rows of `o`'s commands
and the commands of `b'` outside `o` have none. -/
theorem swift.rowsOk_newRow (st st' : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV) (b' : Nat)
    (o : List sp.CmdId) (rv : swift.RowV) (hok : swift.rowsOk st O)
    (hL : st'.locR = (b', o) :: st.locR)
    (hold : ∀ y, y ∈ st.locAt b' → y ∈ o)
    (hin : ∀ y ∈ o, swift.rowsOf st' b' y = rv)
    (hout : ∀ b y, ¬ (b = b' ∧ y ∈ o) → swift.rowsOf st' b y = swift.rowsOf st b y) :
    swift.rowsOk st' (swift.insAll O b' o rv) := by
  intro b y
  rw [swift.insAll_lookup]
  by_cases h : b = b' ∧ y ∈ o
  · rw [if_pos h]; obtain ⟨rfl, hy⟩ := h
    exact ⟨(hin y hy).symm, by rw [swift.locAt_cons st st' b o hL, if_pos rfl]; exact hy⟩
  · rw [if_neg h]
    have hk := hok b y
    revert hk
    rcases O.lookup (b, y) with _ | rv'
    · intro hk; show swift.rowsOf st' b y = _; rw [hout b y h]; exact hk
    · intro hk
      show rv' = _ ∧ _
      by_cases hb : b = b'
      · subst hb; exact absurd ⟨rfl, hold y hk.2⟩ h
      · rw [hout b y h, swift.locAt_cons st st' b' o hL, if_neg hb]; exact hk

theorem swift.rowsOf_tookSync (st : sp.RState) (b' : Nat) (o : List sp.CmdId) (b : Nat)
    (y : sp.CmdId) :
    swift.rowsOf (st.tookSync b' o) b y =
      if b = b' ∧ y ∈ o then ((swift.rowsOf st b y).1, (swift.rowsOf st b y).2.1, true,
        (swift.rowsOf st b y).2.2.2)
      else swift.rowsOf st b y := by
  unfold swift.rowsOf sp.RState.tookSync
  simp only [sp.RState.preAt, sp.RState.pathAt, List.mem_append, List.mem_map]
  by_cases h : b = b' ∧ y ∈ o
  · rw [if_pos h]; obtain ⟨rfl, hy⟩ := h; simp [hy]
  · rw [if_neg h]
    simp only [Prod.mk.injEq, true_and, and_true]
    have : ((∃ a, a ∈ o ∧ b' = b ∧ a = y) ∨ (b, y) ∈ st.accR) ↔ (b, y) ∈ st.accR := by
      constructor
      · rintro (⟨a, ha, rfl, rfl⟩ | h'); exact absurd ⟨rfl, ha⟩ h; exact h'
      · exact Or.inr
    simp only [this]

/-- The view after the new leader computed its `MSync` order `o` of `b'`. -/
def swift.LView.computed (w : swift.LView) (b' : Nat) (o : List sp.CmdId) : swift.LView :=
  (w.1, w.2.1, w.2.2.1, (b', o) :: w.2.2.2)

/-- The view after a new ballot `b'`. -/
def swift.LView.newBal (w : swift.LView) (b' : Nat) : swift.LView :=
  (b', w.2.1, false, w.2.2.2)

-- `swift.rvSync` moved to RetBase.lean (round 32).

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- Row tokens allocated for the fresh commands `o` of ballot `b`. -/
theorem swift.rowToks_alloc (γo : GName) (b : Nat) (rv : swift.RowV) (o : List sp.CmdId)
    (hnd : o.Nodup) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (hfresh : ∀ y ∈ o, O.lookup (b, y) = none) :
    ⊢ (ghostMapAuth γo 1 O : IProp netDistGF) ==∗
      ghostMapAuth γo 1 (swift.insAll O b o rv) ∗ [∗list] y ∈ o, swift.rowTok γo b y rv := by
  induction o generalizing O with
  | nil => iintro H; imodintro; simp only [swift.insAll, List.foldl_nil]; iframe H; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y o ih =>
    rw [show swift.insAll O b (y :: o) rv = swift.insAll (O.insert (b, y) rv) b o rv from rfl]
    iintro H
    imod ghost_map_insert (b, y) rv (hfresh y List.mem_cons_self) $$ H with ⟨H, Ht⟩
    have hnd' := (List.nodup_cons.mp hnd)
    imod ih hnd'.2 (O.insert (b, y) rv) (fun y' hy' => by
      rw [GMap.lookup_insert_eq_iff, if_neg (fun e => hnd'.1 (by cases e; exact hy'))]
      exact hfresh y' (List.mem_cons_of_mem _ hy')) $$ H with ⟨H, Hts⟩
    imodintro
    iframe H
    iapply BigSepL.bigSepL_cons.2
    unfold swift.rowTok
    iframe

/-- Row tokens updated to `rv`. -/
theorem swift.rowToks_update (γo : GName) (b : Nat) (rv0 rv : swift.RowV) (o : List sp.CmdId)
    (O : GMap (Nat × sp.CmdId) swift.RowV) :
    ⊢ (ghostMapAuth γo 1 O : IProp netDistGF) -∗ ([∗list] y ∈ o, swift.rowTok γo b y rv0) ==∗
      ghostMapAuth γo 1 (swift.insAll O b o rv) ∗ [∗list] y ∈ o, swift.rowTok γo b y rv := by
  induction o generalizing O with
  | nil => iintro H -; imodintro; simp only [swift.insAll, List.foldl_nil]; iframe H; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y o ih =>
    rw [show swift.insAll O b (y :: o) rv = swift.insAll (O.insert (b, y) rv) b o rv from rfl]
    iintro H Hts
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨Ht, Hts⟩
    iunfold swift.rowTok at Ht
    imod ghost_map_update rv $$ H Ht with ⟨H, Ht⟩
    imod ih (O.insert (b, y) rv) $$ H Hts with ⟨H, Hts⟩
    imodintro
    iframe H
    iapply BigSepL.bigSepL_cons.2
    unfold swift.rowTok
    iframe

/-- The tokens' values are the authority's. -/
theorem swift.rowToks_lookup (γo : GName) (b : Nat) (rv : swift.RowV) (o : List sp.CmdId)
    (O : GMap (Nat × sp.CmdId) swift.RowV) :
    (ghostMapAuth γo 1 O : IProp netDistGF) ∗ ([∗list] y ∈ o, swift.rowTok γo b y rv) ⊢
      ⌜∀ y ∈ o, O.lookup (b, y) = some rv⌝ := by
  induction o with
  | nil => iintro -; ipureintro; simp
  | cons y o ih =>
    iintro ⟨H, Hts⟩
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨Ht, Hts⟩
    iunfold swift.rowTok at Ht
    ihave %h1 := ghost_map_lookup $$ H Ht
    ihave %h2 := ih $$ [H Hts]
    · iframe
    ipureintro
    intro y' hy'
    rcases List.mem_cons.mp hy' with rfl | hy'
    · exact h1
    · exact h2 y' hy'

/-- **A new ballot** through `nodeInvD` (`handleNewLeader`, its descriptors stopped: the run
loop holds the epoch's other half): the view and the epoch move to `b'`, recovering. Round N5
(D72 (1)): `b'` is above the ballot, and the replica gets `b'`'s report token. -/
theorem swift.newBallot_stepD (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (hE' : ↑sp.spN ⊆ E \ ↑swift.nodeN)
    (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (w : swift.LView) (bc : Nat × Nat) (b' : Nat)
    (hr : r < N) (hk : nodeOf l r = some k) (hb : w.1 < b') (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      ghostVar γv (1 : Qp).half w ∗ swift.epochTok γe (1 : Qp).half bc ∗
      sp.predPre γ k (some (sp.PEv.newBallot b', W')) ⊢
    |={E}=> ghostVar γv (1 : Qp).half (w.newBal b') ∗
      sp.predPost γ k (some (sp.PEv.newBallot b', W')) ∗
      swift.epochTok γe (1 : Qp).half (b', w.2.1) ∗ swift.repTok sn.γrp b' := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hw, Hep, Hpre⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  subst Heq
  iunfold swift.epochTok at Hep
  imod sp.upd_newBallot (E \ ↑swift.nodeN) hE' N fr l r k st b' hr hk
    (Nat.le_of_lt hb) W' $$ [Hst Hpre] with ⟨Hst, Hpost⟩
  · iframe Hinv Hcfg Hst Hpre
  imod swift.nodeX_newBal (E \ ↑swift.nodeN) γ sn st b' hb $$ HX with ⟨HX, Htk⟩
  imod ghostVar_update_halves ((swift.viewOf st).newBal b') γv (swift.viewOf st) (swift.viewOf st)
    $$ Hw Hw2 with ⟨Hw, Hw2⟩
  imod ghostVar_update_halves ((b', st.cballot) : Nat × Nat) γe bc (swift.epochOf st)
    $$ Hep He with ⟨Hep, He⟩
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st.newBal b', O
    iframe Hst HO
    isplitl [Hw2]
    · rw [show swift.viewOf (st.newBal b') = (swift.viewOf st).newBal b' from rfl]; iexact Hw2
    isplitl [He]
    · rw [show swift.epochOf (st.newBal b') = (b', st.cballot) from rfl]; iexact He
    isplitl [HS]
    · rw [show (st.newBal b').cballot = st.cballot from rfl]; iexact HS
    isplitl [HX]
    · iexact HX
    · ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  iframe Hpost
  iframe Hw Htk
  iunfold swift.epochTok
  rw [show (swift.viewOf st).2.1 = st.cballot from rfl]
  iexact Hep

/-- **The new leader's `MSync`** through `nodeInvD` (`handleNewLeaderAckNs` → `recoveredSync`):
`upd_computeSync`, and the row tokens of its order allocated in `b'` (empty rows: the replica
had no row of `b'`). The epoch is unchanged. -/
theorem swift.computeSync_stepD (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (hE' : ↑sp.spN ⊆ E \ ↑swift.nodeN)
    (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N k : Nat)
    (fr : Bool) (l : List GoString) (w : swift.LView) (b' : Nat) (reps : List (Nat × sp.Report))
    (hr : sp.leaderOf N b' < N) (hk : nodeOf l (sp.leaderOf N b') = some k) (hb : 0 < b')
    (hbal : w.1 = b') (hnorm : w.2.2.1 = false) (hrow : ∀ o, (b', o) ∉ w.2.2.2)
    (hmaj : sp.isMajority N (reps.map Prod.fst)) (hc : w.2.1 < b') (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      ghostVar γv (1 : Qp).half w ∗ ([∗list] p ∈ reps, sp.reported γ p.1 b' p.2) ∗
      sp.predPre γ k (some (sp.PEv.computeSync b' (reps.map Prod.fst), W')) ⊢
    |={E}=> ghostVar γv (1 : Qp).half (w.computed b' (sp.syncOrder (sp.recoverSync N reps))) ∗
      sp.predPost γ k (some (sp.PEv.computeSync b' (reps.map Prod.fst), W')) ∗
      sp.syncIs γ b' (sp.recoverSync N reps) ∗
      ([∗list] i ↦ x ∈ sp.syncOrder (sp.recoverSync N reps), sp.locAt γ (sp.leaderOf N b') b' i x) ∗
      ([∗list] y ∈ sp.syncOrder (sp.recoverSync N reps), swift.rowTok γo b' y swift.rowEmpty) ∗
      -- round 46 (D-SWC2-5): the tokens' tickets, minted with them
      [∗list] y ∈ sp.syncOrder (sp.recoverSync N reps), swift.xTixK sn.γxu (b', y) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hw, #Hreps, Hpre⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  subst Heq
  imod sp.upd_computeSync (E \ ↑swift.nodeN) hE' N fr l k st b' reps hr hk hb
    hbal hnorm hrow hmaj W' $$ [Hst Hpre] with ⟨Hst, Hpost, #HM, #Hl⟩
  · iframe Hinv Hcfg Hst Hpre Hreps
  have hnil : st.locAt b' = [] := sp.locAt_nil_of_rows hrow
  have hfresh : ∀ y ∈ sp.syncOrder (sp.recoverSync N reps), O.lookup (b', y) = none := by
    intro y _
    have hk := Hok b' y
    revert hk
    rcases O.lookup (b', y) with _ | rv
    · intro _; rfl
    · intro hk; rw [hnil] at hk; exact absurd hk.2 (List.not_mem_nil)
  imod swift.rowToks_alloc γo b' swift.rowEmpty _ (sp.syncOrder_nodup _) O hfresh $$ HO
    with ⟨HO, Htoks⟩
  have hsub : ∀ K, (O.lookup K).isSome →
      ((swift.insAll O b' (sp.syncOrder (sp.recoverSync N reps)) swift.rowEmpty).lookup K).isSome := by
    intro K hK; obtain ⟨b2, y2⟩ := K; rw [swift.insAll_lookup]; split
    · rfl
    · exact hK
  have hnew : ∀ K, ((swift.insAll O b' (sp.syncOrder (sp.recoverSync N reps))
      swift.rowEmpty).lookup K).isSome → (O.lookup K).isSome ∨ K.1 ≠ st.cballot := by
    intro K hK; obtain ⟨b2, y2⟩ := K; rw [swift.insAll_lookup] at hK
    by_cases e : b2 = b' ∧ y2 ∈ sp.syncOrder (sp.recoverSync N reps)
    · right; show b2 ≠ st.cballot; have : st.cballot < b' := hc; omega
    · rw [if_neg e] at hK; left; exact hK
  imod (swift.storeD_growMint γ γo sn st.cballot O _ b' _ (sp.syncOrder_nodup _) hfresh
    (fun y hy => by rw [swift.insAll_lookup, if_pos ⟨rfl, hy⟩]; rfl) hsub hnew) $$ HS
    with ⟨HS, Htix⟩
  imod ghostVar_update_halves ((swift.viewOf st).computed b' (sp.syncOrder (sp.recoverSync N reps)))
    γv (swift.viewOf st) (swift.viewOf st) $$ Hw Hw2 with ⟨Hw, Hw2⟩
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st.computed b' (sp.syncOrder (sp.recoverSync N reps)), _
    iframe Hst HO
    isplitl [Hw2]
    · rw [show swift.viewOf (st.computed b' (sp.syncOrder (sp.recoverSync N reps))) =
        (swift.viewOf st).computed b' (sp.syncOrder (sp.recoverSync N reps)) from rfl]
      iexact Hw2
    isplitl [He]
    · rw [show swift.epochOf (st.computed b' (sp.syncOrder (sp.recoverSync N reps))) =
        swift.epochOf st from rfl]
      iexact He
    isplitl [HS]
    · rw [show (st.computed b' (sp.syncOrder (sp.recoverSync N reps))).cballot = st.cballot
        from rfl]
      iexact HS
    isplitl [HX]
    · iapply (swift.nodeX_mono γ sn st (st.computed b' (sp.syncOrder (sp.recoverSync N reps)))
        (Nat.le_refl _) rfl rfl (fun _ h => h)); iexact HX
    · ipureintro
      refine ⟨Hacc, swift.rowsOk_newRow st _ O b' _ _ Hok rfl
        (fun y hy => by rw [hnil] at hy; cases hy) (fun y _ => ?_) (fun _ _ _ => rfl)⟩
      have hk := Hok b' y
      rw [hfresh y ‹_›] at hk
      exact hk
  imodintro
  iframe Hpost
  iframe Hw Htoks Htix
  isplitr
  · iexact HM
  · iexact Hl

/-- **Taking ballot `b'`'s `MSync`** through `nodeInvD` (`handleSync`, with the epoch's whole
half): `upd_takeSync`; the epoch moves to `(b', b')`; the row tokens of the order in `b'` are
allocated (a follower, which had no row of `b'`) or updated (the new leader, from
`computeSync_stepD`) to `rvSync` (accepted), for the order's descriptors. -/
theorem swift.takeSync_stepD (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (hE' : ↑sp.spN ⊆ E \ ↑swift.nodeN)
    (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (w : swift.LView) (bc : Nat × Nat) (b' : Nat)
    (M : sp.SyncMsg) (hr : r < N) (hk : nodeOf l r = some k) (hbal : w.1 ≤ b')
    (hc : w.2.1 < b') (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      ghostVar γv (1 : Qp).half w ∗ swift.epochTok γe (1 : Qp).half bc ∗ sp.syncIs γ b' M ∗
      (⌜w.locAt b' = []⌝ ∨
        (⌜w.locAt b' = sp.syncOrder M⌝ ∗ ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x) ∗
          ([∗list] y ∈ sp.syncOrder M, swift.rowTok γo b' y swift.rowEmpty) ∗
          [∗list] y ∈ sp.syncOrder M, swift.xTixK sn.γxu (b', y))) ∗
      sp.predPre γ k (some (sp.PEv.takeSync b', W')) ⊢
    |={E}=> ghostVar γv (1 : Qp).half (w.tookSync b' (sp.syncOrder M)) ∗
      sp.predPost γ k (some (sp.PEv.takeSync b', W')) ∗
      swift.epochTok γe (1 : Qp).half (b', b') ∗
      ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x) ∗
      ([∗list] x ∈ sp.syncOrder M, sp.accepted γ r b' x) ∗
      ([∗list] y ∈ sp.syncOrder M, swift.claimTok sn.γcl (b', y) .sync) ∗
      ghostMapElem sn.γcg (b', false) (DFrac.own 1) (none : Option GName) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hw, Hep, #HM, Hsrc, Hpre⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  subst Heq
  iunfold swift.epochTok at Hep
  have hcb : st.cballot < b' := hc
  -- the row tokens of the order
  ihave Hj : (|={E \ ↑swift.nodeN}=> ⌜(∀ y, swift.rowsOf st b' y = swift.rowEmpty) ∧
        ∀ y ∈ st.locAt b', y ∈ sp.syncOrder M⌝ ∗
      ghostMapAuth γo 1 (swift.insAll O b' (sp.syncOrder M) swift.rvSync) ∗
      ([∗list] y ∈ sp.syncOrder M, swift.rowTok γo b' y swift.rvSync) ∗
      (⌜∀ y ∈ sp.syncOrder M, O.lookup (b', y) = none⌝ ∨
        [∗list] y ∈ sp.syncOrder M, swift.xTixK sn.γxu (b', y)) ∗
      (⌜st.locAt b' = []⌝ ∨
        (⌜st.locAt b' = sp.syncOrder M⌝ ∗ [∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x)))
    $$ [HO Hsrc]
  · icases Hsrc with (%h0 | ⟨%h0, #Hl, Ht, Htx⟩)
    · have h0' : st.locAt b' = [] := h0
      have hnone : ∀ y, O.lookup (b', y) = none := by
        intro y
        have hk := Hok b' y
        revert hk
        rcases O.lookup (b', y) with _ | rv
        · intro _; rfl
        · intro hk; rw [h0'] at hk; exact absurd hk.2 (List.not_mem_nil)
      imod swift.rowToks_alloc γo b' swift.rvSync _ (sp.syncOrder_nodup M) O
        (fun y _ => hnone y) $$ HO with ⟨HO, Htoks⟩
      imodintro
      iframe HO Htoks
      isplitl []
      · ipureintro
        refine ⟨fun y => ?_, fun y hy => by rw [h0'] at hy; cases hy⟩
        have hk := Hok b' y; rw [hnone y] at hk; exact hk
      isplitl []
      · ileft; ipureintro; exact fun y _ => hnone y
      · ileft; ipureintro; exact h0'
    · have h0' : st.locAt b' = sp.syncOrder M := h0
      ihave %Hlk := swift.rowToks_lookup γo b' swift.rowEmpty _ O $$ [HO Ht]
      · iframe
      have hemp : ∀ y, swift.rowsOf st b' y = swift.rowEmpty := by
        intro y
        have hk := Hok b' y
        by_cases hy : y ∈ sp.syncOrder M
        · rw [Hlk y hy] at hk; exact hk.1.symm
        · revert hk
          rcases O.lookup (b', y) with _ | rv
          · intro hk; exact hk
          · intro hk; rw [h0'] at hk; exact absurd hk.2 hy
      imod swift.rowToks_update γo b' swift.rowEmpty swift.rvSync _ O $$ HO Ht with ⟨HO, Htoks⟩
      imodintro
      iframe HO Htoks
      isplitl []
      · ipureintro; exact ⟨hemp, fun y hy => by rw [h0'] at hy; exact hy⟩
      isplitl [Htx]
      · iright; iexact Htx
      · iright; isplitl []
        · ipureintro; exact h0'
        · iexact Hl
  imod Hj with ⟨%Hj, HO, Htoks, Htx, Hsrc⟩
  -- round 32 (T28, rev 5b G-pre): the order's tokens into the store, `sync` claims out
  have hcov : ∀ y, ((swift.insAll O b' (sp.syncOrder M) swift.rvSync).lookup (b', y)).isSome →
      y ∈ sp.syncOrder M := by
    intro y hy
    rw [swift.insAll_lookup] at hy
    by_cases e : b' = b' ∧ y ∈ sp.syncOrder M
    · exact e.2
    · rw [if_neg e] at hy
      have hk := Hok b' y
      revert hk
      rcases e' : O.lookup (b', y) with _ | rv
      · rw [e'] at hy; cases hy
      · intro hk; exact Hj.2 y hk.2
  imod swift.storeD_takeSync γ γo sn st.cballot b' O M (sp.syncOrder M) (sp.syncOrder_nodup M)
    hcb (fun _ h => h) hcov $$ [HS HM Htoks Htx] with ⟨HS, Htoks⟩
  · iframe HS HM Htoks Htx
  imod sp.upd_takeSync (E \ ↑swift.nodeN) hE' N fr l r k st b' M hr hk hbal
    (fun x hx => by have := Hacc b' x hx; omega) W' $$ [Hst Hpre Hsrc] with ⟨Hst, Hpost, #Hl, #Ha⟩
  · iframe Hinv Hcfg Hst Hpre HM Hsrc
  imod ghostVar_update_halves ((swift.viewOf st).tookSync b' (sp.syncOrder M)) γv (swift.viewOf st)
    (swift.viewOf st) $$ Hw Hw2 with ⟨Hw, Hw2⟩
  imod ghostVar_update_halves ((b', b') : Nat × Nat) γe bc (swift.epochOf st)
    $$ Hep He with ⟨Hep, He⟩
  -- round 56 (D79 (1), 52-3): ballot `b'`'s key in the epochs' map, reserved (`b' > cballot`)
  iunfold swift.nodeX at HX
  icases HX with ⟨HXT, HXs, -, HXcg⟩
  iunfold swift.cgAuth at HXcg
  icases HXcg with ⟨%G, HGa, %hG⟩
  have hGf : G.lookup (b', false) = none := by
    cases h : G.lookup (b', false) with
    | none => rfl
    | some _ => have := hG.1 (b', false) (by rw [h]; rfl); simp at this; omega
  imod ghost_map_insert (γ := sn.γcg) (b', false) (none : Option GName) hGf $$ HGa with ⟨HGa, HGr⟩
  ihave Hcg' : swift.cgAuth sn b' $$ [HGa]
  · iunfold swift.cgAuth
    iexists G.insert (b', false) none
    iframe HGa
    ipureintro
    constructor
    · intro k h
      rw [GMap.lookup_insert_eq_iff] at h
      by_cases e : (b', false) = k
      · subst e; exact Nat.le_refl _
      · rw [if_neg e] at h; have := hG.1 k h; omega
    · intro b h
      rw [GMap.lookup_insert_eq_iff, if_neg (by simp)] at h
      obtain ⟨γk, hk⟩ := hG.2 b h
      refine ⟨γk, ?_⟩
      rw [GMap.lookup_insert_eq_iff]
      by_cases e : (b', false) = (b, false)
      · simp only [Prod.mk.injEq, and_true] at e; subst e
        have := hG.1 _ h; simp at this; omega
      · rw [if_neg e]; exact hk
  imod Hclose $$ [Hst Hw2 He HO HS HXT HXs Hcg'] with -
  · inext
    iunfold swift.nodeInvD
    iexists st.tookSync b' (sp.syncOrder M), _
    iframe Hst HO
    isplitl [Hw2]
    · rw [show swift.viewOf (st.tookSync b' (sp.syncOrder M)) =
        (swift.viewOf st).tookSync b' (sp.syncOrder M) from rfl]
      iexact Hw2
    isplitl [He]
    · rw [show swift.epochOf (st.tookSync b' (sp.syncOrder M)) = (b', b') from rfl]
      iexact He
    isplitl [HS]
    · rw [show (st.tookSync b' (sp.syncOrder M)).cballot = b' from rfl]; iexact HS
    isplitl [HXT HXs Hcg']
    · -- round N5: the report tokens (ballot `b' ≥` the old one), the new base's acceptances
      unfold swift.nodeX
      rw [show (st.tookSync b' (sp.syncOrder M)).repR = st.repR from rfl,
        show (st.tookSync b' (sp.syncOrder M)).cballot = b' from rfl,
        show (st.tookSync b' (sp.syncOrder M)).ballot = b' from rfl,
        show (st.tookSync b' (sp.syncOrder M)).accR =
          (sp.syncOrder M).map (fun x => (b', x)) ++ st.accR from rfl]
      icases HXT with ⟨%T, HTa, %hT⟩
      iframe Hcg'
      isplitl [HTa]
      · iexists T; iframe HTa; ipureintro; intro b h; have := hT b h
        have h2 : st.ballot ≤ b' := hbal; omega
      isplitl [HXs]
      · iexact HXs
      · iright; iexists M; iframe HM; ipureintro
        intro y hy
        exact List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩)
    · ipureintro
      refine ⟨?_, swift.rowsOk_newRow st _ O b' _ _ Hok rfl Hj.2 (fun y hy => ?_)
        (fun b y h => by rw [swift.rowsOf_tookSync, if_neg h])⟩
      · intro b x hx
        simp only [sp.RState.tookSync, List.mem_append, List.mem_map] at hx ⊢
        rcases hx with ⟨y, -, hy⟩ | hx
        · cases hy; omega
        · have := Hacc b x hx; omega
      · rw [swift.rowsOf_tookSync, if_pos ⟨rfl, hy⟩, Hj.1 y]; rfl
  imodintro
  iframe Hpost
  iframe Hw Htoks
  isplitl [Hep]
  · iunfold swift.epochTok; iexact Hep
  isplitl []
  · iexact Hl
  · iframe Ha; iexact HGr

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
