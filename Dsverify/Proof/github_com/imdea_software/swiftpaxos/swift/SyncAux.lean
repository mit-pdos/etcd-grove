/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncAux.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync`'s auxiliary lemmas (internal, the swift group's; round 13, sv-swa):

* `sp.cmdIs_list_len`: distinct registered commands (persistent `cmdIs` facts) are at most
  `6 · 2^25` (the clients' bounds in `sp.inv`, `sp.cmds_len`); `swift.props_size`: so are
  `proposes`' entries (each with its `cmdIs`), hence `sortedProposes`' premise `≤ 2^62`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RepsOkInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecKept
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbN
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256


/-! ## The reproposals' loop: `proposes` without the entries the `MSync` lacks -/

/-- `proposes` after the reproposals' loop over the ids `l`: the entries `phM` (the `MSync`'s
`Phases`) lacks are deleted. -/
def swift.dropMissing (phM : GMap swift.CommandId w64) (l : List swift.CommandId)
    (pM : GMap swift.CommandId Loc) : GMap swift.CommandId Loc :=
  l.foldl (fun m x => if (phM !! x).isSome then m else GMap.delete x m) pM

theorem swift.dropMissing_snoc (phM : GMap swift.CommandId w64) (l : List swift.CommandId)
    (x : swift.CommandId) (pM : GMap swift.CommandId Loc) :
    swift.dropMissing phM (l ++ [x]) pM = if (phM !! x).isSome then swift.dropMissing phM l pM
      else GMap.delete x (swift.dropMissing phM l pM) := by
  simp [swift.dropMissing, List.foldl_append]

theorem swift.dropMissing_lookup_gen (phM : GMap swift.CommandId w64) (l : List swift.CommandId)
    (pM : GMap swift.CommandId Loc) (k : swift.CommandId) :
    swift.dropMissing phM l pM !! k =
      if k ∈ l ∧ (phM !! k).isSome = false then none else pM !! k := by
  induction l generalizing pM with
  | nil => simp [swift.dropMissing]
  | cons a t ih =>
    have h1 : swift.dropMissing phM (a :: t) pM =
        swift.dropMissing phM t (if (phM !! a).isSome then pM else GMap.delete a pM) := rfl
    rw [h1, ih]
    by_cases hka : k = a
    · subst hka
      cases hp : (phM !! k).isSome <;> simp [hp, GMap.lookup_delete]
    · have hne : a ≠ k := fun h => hka h.symm
      cases hp : (phM !! a).isSome <;> simp [hp, hka, hne, GMap.lookup_delete]

theorem swift.dropMissing_lookup (phM : GMap swift.CommandId w64) (l : List swift.CommandId)
    (pM : GMap swift.CommandId Loc) (k : swift.CommandId) (hk : k ∉ l) :
    swift.dropMissing phM l pM !! k = pM !! k := by
  rw [swift.dropMissing_lookup_gen]; simp [hk]

theorem swift.dropMissing_all (phM : GMap swift.CommandId w64) (l : List swift.CommandId)
    (pM : GMap swift.CommandId Loc) (hcov : ∀ k, (pM !! k).isSome → k ∈ l)
    (k : swift.CommandId) :
    swift.dropMissing phM l pM !! k = if (phM !! k).isSome then pM !! k else none := by
  rw [swift.dropMissing_lookup_gen]
  by_cases hl : k ∈ l
  · cases hp : (phM !! k).isSome <;> simp [hp, hl]
  · have : pM !! k = none := by
      cases h : pM !! k
      · rfl
      · exact absurd (hcov k (by simp [h])) hl
    cases hp : (phM !! k).isSome <;> simp [hp, hl, this]


/-! ## The descriptors' freeing: the entries not yet visited -/

theorem swift.foldl_delete_lookup (l : List GoString) (M : GMap GoString GoInterface)
    (k : GoString) (hk : k ∉ l) :
    (l.foldl (fun M k => GMap.delete k M) M) !! k = M !! k := by
  induction l generalizing M with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hka : a ≠ k := fun h => hk (h ▸ List.mem_cons_self ..)
    rw [ih _ (fun h => hk (List.mem_cons_of_mem _ h)), GMap.lookup_delete_ne _ hka]


/-! ## The `MSync`'s order has all its commands -/

theorem sp.recOrderStep_grow (k : sp.Kept) (ids P : List sp.CmdId) :
    (∀ c ∈ ids, c ∈ P) ∧ sp.recOrderStep k ids P = P ∨
      ∃ c, c ∈ ids ∧ c ∉ P ∧ sp.recOrderStep k ids P = P ++ [c] := by
  unfold sp.recOrderStep
  dsimp only
  split
  · rename_i hc
    have := List.mem_filter.mp (List.mem_of_find?_eq_some hc)
    simp only [decide_eq_true_eq] at this
    exact Or.inr ⟨_, this.1, this.2, rfl⟩
  · rename_i hc
    have := List.mem_filter.mp (List.mem_of_mem_head? hc)
    simp only [decide_eq_true_eq] at this
    exact Or.inr ⟨_, this.1, this.2, rfl⟩
  · rename_i hh
    left
    refine ⟨fun c hc => ?_, rfl⟩
    refine Classical.byContradiction fun hn => ?_
    have hmem : c ∈ ids.filter (· ∉ P) := List.mem_filter.mpr ⟨hc, by simpa using hn⟩
    cases hr : ids.filter (· ∉ P) with
    | nil => rw [hr] at hmem; simp at hmem
    | cons a t => rw [hr] at hh; simp at hh

theorem sp.iter_recOrderStep_sup (k : sp.Kept) (ids : List sp.CmdId) (n : Nat) (P : List sp.CmdId) :
    ∀ c ∈ P, c ∈ sp.iter (sp.recOrderStep k ids) n P := by
  induction n generalizing P with
  | zero => intro c hc; exact hc
  | succ n ih =>
    intro c hc
    apply ih
    rcases sp.recOrderStep_grow k ids P with ⟨-, h⟩ | ⟨d, -, -, h⟩
    · rw [h]; exact hc
    · rw [h]; exact List.mem_append_left _ hc

theorem sp.recOrder_complete (k : sp.Kept) (ids : List sp.CmdId) (hnd : ids.Nodup) :
    ∀ c ∈ ids, c ∈ sp.recOrder k ids := by
  rw [sp.recOrder_eq]
  suffices h : ∀ n P, (∀ c ∈ P, c ∈ ids) → P.Nodup → ids.length ≤ P.length + n →
      ∀ c ∈ ids, c ∈ sp.iter (sp.recOrderStep k ids) n P from
    h ids.length [] (by simp) List.nodup_nil (by simp)
  intro n
  induction n with
  | zero =>
    intro P hsub hP hlen c hc
    have hperm := (List.subperm_of_subset hP hsub).perm_of_length_le (by simpa using hlen)
    exact hperm.mem_iff.mpr hc
  | succ n ih =>
    intro P hsub hP hlen c hc
    rcases sp.recOrderStep_grow k ids P with ⟨hall, h⟩ | ⟨d, hd, hdP, h⟩
    · exact sp.iter_recOrderStep_sup k ids (n + 1) P c (hall c hc)
    · show c ∈ sp.iter (sp.recOrderStep k ids) n (sp.recOrderStep k ids P)
      rw [h]
      refine ih _ (fun x hx => ?_) ?_ (by simp; omega) c hc
      · rcases List.mem_append.mp hx with hx | hx
        · exact hsub x hx
        · simp at hx; subst hx; exact hd
      · exact List.nodup_append.mpr ⟨hP, by simp, fun a ha b hb => by
          simp at hb; subst hb; intro e; subst e; exact hdP ha⟩

theorem sp.syncOrder_complete (M : sp.SyncMsg) (hnd : (M.map Prod.fst).Nodup) (x : sp.CmdId)
    (hx : x ∈ M.map Prod.fst) : x ∈ sp.syncOrder M := by
  unfold sp.syncOrder
  apply sp.recOrder_complete
  · unfold sp.sortIds
    exact (List.mergeSort_perm _ _).nodup_iff.mpr hnd
  · unfold sp.sortIds
    exact List.mem_mergeSort.mpr hx

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable {γ : sp.Names} {γc γm γl : GName}

theorem sp.cmdIs_all (mC : GMap sp.CmdId sp.Cmd) (l : List sp.CmdId) :
    ghostMapAuth γ.cmds 1 mC ∗ □ ([∗list] x ∈ l, ∃ c, sp.cmdIs γ x c) ⊢
      ghostMapAuth γ.cmds 1 mC ∗ ⌜∀ x ∈ l, ∃ c, mC.lookup x = some c⌝ := by
  induction l with
  | nil =>
    iintro ⟨HC, -⟩
    iframe HC
    ipureintro; intro x hx; simp at hx
  | cons a t ih =>
    iintro ⟨HC, #Hl⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨⟨%c, #Hc⟩, #Ht⟩
    iunfold sp.cmdIs at Hc
    ihave %h1 := ghost_map_lookup $$ HC Hc
    ihave ⟨HC, %h2⟩ := ih $$ [HC]
    · iframe HC; imodintro; iexact Ht
    iframe HC
    ipureintro
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c, h1⟩
    · exact h2 x hx

/-- Distinct registered commands are at most `6 · 2^25` (see the file header). -/
theorem sp.cmdIs_list_len (E : CoPset) (hE : ↑sp.spN ⊆ E) (l : List sp.CmdId) (hnd : l.Nodup) :
    sp.inv γ γc γm γl ∗ □ ([∗list] x ∈ l, ∃ c, sp.cmdIs γ x c) ⊢
      |={E}=> ⌜l.length ≤ 6 * 2 ^ 25⌝ := by
  unfold sp.inv
  iintro ⟨#Hinv, #Hl⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, >%Hdom, Hcmds, Hconns⟩
  ihave ⟨HC, %Hreg⟩ := sp.cmdIs_all mC l $$ [HC]
  · iframe HC; imodintro; iexact Hl
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes Hproto HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    ipureintro
    exact ⟨Hrepr, Hcl, Hdom⟩
  imodintro
  ipureintro
  exact sp.cmds_len Hrepr.cmds Hcl Hdom.2 l hnd (fun x hx => by
    obtain ⟨c, hc⟩ := Hreg x hx
    rw [← Hrepr.cmds, hc]; simp)

theorem sp.cmdIs_all2 (mC : GMap sp.CmdId sp.Cmd) (M : sp.SyncMsg) :
    ghostMapAuth γ.cmds 1 mC ∗ □ ([∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1) ⊢
      ghostMapAuth γ.cmds 1 mC ∗ ⌜∀ p ∈ M, mC.lookup p.1 = some p.2.1⌝ := by
  induction M with
  | nil =>
    iintro ⟨HC, -⟩
    iframe HC
    ipureintro; intro x hx; simp at hx
  | cons a t ih =>
    iintro ⟨HC, #Hl⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨#Hc, #Ht⟩
    iunfold sp.cmdIs at Hc
    ihave %h1 := ghost_map_lookup $$ HC Hc
    ihave ⟨HC, %h2⟩ := ih $$ [HC]
    · iframe HC; imodintro; iexact Ht
    iframe HC
    ipureintro
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact h2 x hx

/-- The `MSync`'s commands are puts or gets (D10; their registrations). -/
theorem sp.sync_kinds (E : CoPset) (hE : ↑sp.spN ⊆ E) (b : Nat) (M : sp.SyncMsg) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ b M ⊢ |={E}=> ⌜∀ p ∈ M, p.2.1.isPut ∨ p.2.1.isGet⌝ := by
  iintro ⟨#Hinv, #HM⟩
  imod sp.syncIs_cmdIs E hE b M $$ [Hinv HM] with #Hl
  · iframe Hinv HM
  unfold sp.inv
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, HDom, Hcmds, Hconns⟩
  ihave ⟨HC, %Hreg⟩ := sp.cmdIs_all2 mC M $$ [HC]
  · iframe HC; imodintro; iexact Hl
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes Hproto HQs HDom Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    ipureintro
    exact ⟨Hrepr, Hcl⟩
  imodintro
  ipureintro
  intro p hp
  exact (Hcl p.1 p.2.1 (Hreg p hp)).2.1


end ghost

section props
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

theorem swift.props_cmdIs (γ : sp.Names) (pM : GMap swift.CommandId Loc) :
    ([∗map] x ↦ gp ∈ pM, ∃ c, swift.propIs γ gp (toCmdId x) c) ⊢
      ([∗map] x ↦ gp ∈ pM, ∃ c, swift.propIs γ gp (toCmdId x) c) ∗
        [∗map] x ↦ _gp ∈ pM, ∃ c, sp.cmdIs γ (toCmdId x) c := by
  rw [← BigSepM.bigSepM_sep_eq]
  apply BigSepM.bigSepM_mono
  intro k gp _
  iintro ⟨%c, Hp⟩
  ihave #Hc : sp.cmdIs γ (toCmdId k) c $$ [Hp]
  · unfold swift.propIs
    icases Hp with ⟨%p, %w, %mu, %addr, %ts, %vs, -, -, -, #Hc, -⟩
    iexact Hc
  isplitl [Hp]
  · iexists c; iexact Hp
  · iexists c; iexact Hc

/-- `proposes`' size (see the file header). -/
theorem swift.props_size (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName)
    (pm : Loc) (pM : GMap swift.CommandId Loc) :
    sp.inv γ γc γm γl ∗ swift.propsOwn γ pm pM ⊢
      |={E}=> swift.propsOwn γ pm pM ∗ ⌜GMap.size pM ≤ 2 ^ 62⌝ := by
  iintro ⟨#Hinv, Hp⟩
  unfold swift.propsOwn
  icases Hp with ⟨Hm, Hs⟩
  icases swift.props_cmdIs γ pM $$ Hs with ⟨Hs, #Hc⟩
  let l : List sp.CmdId := pM.toList.map (fun p => toCmdId p.1)
  have hnd : l.Nodup := by
    have h := GMap.toList_keys_nodup pM
    have : l = (pM.toList.map Prod.fst).map toCmdId := by simp [l, List.map_map]
    rw [this]
    exact List.Pairwise.map toCmdId (fun a b hab e => hab (swift.toCmdId_inj e)) h
  have hlen : l.length = GMap.size pM := by simp [l, GMap.size]
  ihave #Hl : □ ([∗list] x ∈ l, ∃ c, sp.cmdIs γ x c) $$ [Hc]
  · imodintro
    iapply BigSepL.bigSepL_forall_elim
    iintro %i %x %hx
    obtain ⟨⟨k, gp⟩, hk, rfl⟩ : ∃ p ∈ pM.toList, toCmdId p.1 = x := by
      have := List.mem_of_getElem? hx
      simpa [l] using this
    rw [GMap.mem_toList] at hk
    iapply (BigSepM.bigSepM_lookup hk) $$ Hc
  imod sp.cmdIs_list_len E hE l hnd $$ [Hinv Hl] with %Hb
  · iframe Hinv; iexact Hl
  imodintro
  iframe Hm Hs
  ipureintro
  omega

/-- The run loop's view and its epoch token agree (both halves against `nodeInvD`'s). -/
theorem swift.epoch_view_agree (γ : sp.Names) (γv γe γo : GName) {sn : swift.StN} (k : Nat) (w : swift.LView)
    (bc : Nat × Nat) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ ghostVar γv (1 : Qp).half w ∗
      swift.epochTok γe (1 : Qp).half bc ⊢
    |={⊤}=> ghostVar γv (1 : Qp).half w ∗ swift.epochTok γe (1 : Qp).half bc ∗
      ⌜bc = (w.1, w.2.1)⌝ := by
  iintro ⟨#Hninv, Hw, Hep⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  iunfold swift.epochTok at Hep
  ihave %Heq2 := ghostVar_agree γe bc (1 : Qp).half (swift.epochOf st) (1 : Qp).half $$ Hep He
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe
    ipureintro; exact Hok
  imodintro
  iunfold swift.epochTok
  iframe
  ipureintro
  subst Heq Heq2; rfl


end props

end Perennial.github_com.imdea_software.swiftpaxos
