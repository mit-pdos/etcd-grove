/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/StopDescsProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`stopDescs`** (round 18, sv-swb; notes/prove-swift.md §24) over the concrete descriptors'
state (`swift.descStateR … (swift.descGo …) g`, DescState.lean):

`swift.Replica.stopDescs.wp_specD`: from the descriptors' state and `cntL`'s mutex, the stopped
descriptors (`swift.descsDone`: the view, every entry at home, whole; `cntL`'s flag frozen; the
descriptors' epoch share back). Each round (P10, fork 28c218f): one fresh `WaitGroup` per
stop request (`sync.join`, one `Add` each), collected in the slice `wgs`, `IterCbVP` with the round's state (`roundI`), whose
closure lends each visited entry's state (`descInv_lend`), reads `active` and `seq`, returns it
(`descInv_return`) and, for an active non-sequential one, signals it (`go_signal`, `Add`, the
request on its `stopChan`, the wait group appended to `wgs`); after the `Wait`s, the round's
elements reset `γs` (`sig_reset`). The
exit: `routineCount <= 0` under `cntL` → `cntLGhost_freeze` → `descInv_take_frozen`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopRound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

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
variable [sync.Assumptions]

/-- **The stopped descriptors** (`stopDescs.wp_specD`'s post). -/
def swift.descsDone (γ : sp.Names) (rp : Loc) (x : swift.RunX) (DR : Loc → IProp netDistGF)
    (g : swift.DescG) : IProp netDistGF :=
  iprop(∃ (dm1 : GoSlice) (Mc : GMap GoString GoInterface),
    swift.fld rp go!"cmdDescs" ↦ dm1 ∗
    github_com.orcaman.concurrent_map.isCMapV dm1 g.γdc (swift.descR x.γd) ∗
    github_com.orcaman.concurrent_map.readerV dm1 g.γdc (swift.descR x.γd) ∗
    github_com.orcaman.concurrent_map.cmapView g.γdc Mc ∗
    ([∗map] k ↦ v ∈ Mc, swift.descEntH γ x.γd DR x.str k v) ∗
    swift.cntFrozen x.γn true ∗ swift.epochShare (x.epN rp) g.ev g.Qd ∗
    ghostVar g.γst (1 : Qp).half true ∗ ghostMapAuth x.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) ∗
    -- round 53 (D73 (4), 51-2 (a)): the commit record, kept for `epStopped`'s `stopPS`
    ▷ swift.incInv g Mc)

/-- The round's signalled keys as a ghost map (P10: `L` lists each request's wait group and
key, in the order of the requests). -/
def swift.sigMap (L : List (Loc × GoString)) : GMap GoString Bool :=
  L.foldl (fun m p => m.insert p.2 true) ∅

/-- **A round's state** (`IterCbVP`'s `I`; P10: the slice `wgs` at `wp` of the round's wait
groups, one per request): the requests `L` (wait group, key), their keys all visited and
distinct, `γs`'s authority at their map, each wait group's adder (one `Add`, its `P` the key's
element), `γb`'s authority at `0` (no state lent between visits), the run loop's `γst` half. -/
def swift.roundI (g : swift.DescG) (wp : Loc) (_obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) : IProp netDistGF :=
  iprop(∃ (L : List (Loc × GoString)) (sl : GoSlice), wp ↦ sl ∗ sl ↦* L.map Prod.fst ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ ghostMapAuth g.γs 1 (swift.sigMap L) ∗
    ⌜(∀ k ∈ L.map Prod.snd, k ∈ vis.map Prod.fst) ∧ (L.map Prod.snd).Nodup⌝ ∗
    ([∗list] p ∈ L, sync.join.ownAdder p.1 (W32 1)
      iprop(True ∗ ghostMapElem g.γs p.2 (DFrac.own 1) true)) ∗
    ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ ghostVar g.γst (1 : Qp).half false)

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

theorem swift.descGo_seq (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString)
    (d : Loc) (y : swift.CommandId) :
    swift.descGo γn g str d y ⊢
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗ True := by
  iintro H
  iunfold swift.descGo at H
  icases H with ⟨%j, %qj, %a, %sc, %γc, %γsg, %m, %γi, -, -, -, -, Hs, -⟩
  iframe Hs

theorem swift.descGo_elem (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString)
    (d : Loc) (y : swift.CommandId) :
    swift.descGo γn g str d y ⊢ ∃ (i : Nat) (q : Qp), ghostMapElem γn i (DFrac.own q) false := by
  iintro H
  iunfold swift.descGo at H
  icases H with ⟨%j, %qj, %a, %sc, %γc, %γsg, %m, %γi, Hel, -⟩
  iexists j, qj
  iexact Hel

theorem swift.list_snoc_ind {α : Type} {P : List α → Prop} (h0 : P [])
    (h1 : ∀ L a, P L → P (L ++ [a])) : ∀ L, P L := by
  intro L
  rw [← List.reverse_reverse L]
  induction L.reverse with
  | nil => exact h0
  | cons a l ih => rw [List.reverse_cons]; exact h1 _ _ ih

theorem swift.sigMap_snoc (L : List (Loc × GoString)) (p : Loc × GoString) :
    swift.sigMap (L ++ [p]) = (swift.sigMap L).insert p.2 true := by
  simp [swift.sigMap, List.foldl_append]

theorem swift.sigMap_lookup (L : List (Loc × GoString)) (k : GoString) :
    (swift.sigMap L !! k).isSome → k ∈ L.map Prod.snd := by
  induction L using swift.list_snoc_ind with
  | h0 => intro h; simp [swift.sigMap] at h
  | h1 L p ih =>
    intro h
    rw [swift.sigMap_snoc] at h
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton]
    by_cases hk : p.2 = k
    · exact Or.inr hk.symm
    · rw [GMap.lookup_insert_ne _ _ hk] at h
      exact Or.inl (ih h)

/-- **The round's reset** (P10): every request's element back, `γs`'s authority at `∅`. -/
theorem swift.sig_reset (γs : GName) : ∀ (L : List (Loc × GoString)),
    (L.map Prod.snd).Nodup →
    ghostMapAuth γs 1 (swift.sigMap L) ∗
      ([∗list] p ∈ L, ghostMapElem γs p.2 (DFrac.own 1) true) ⊢
      |==> ghostMapAuth γs 1 (∅ : GMap GoString Bool) := by
  intro L
  induction L using swift.list_snoc_ind with
  | h0 =>
    intro _
    rw [show swift.sigMap ([] : List (Loc × GoString)) = ∅ from rfl]
    iintro ⟨Ha, -⟩; imodintro; iexact Ha
  | h1 L p ih =>
    intro hnd
    simp only [List.map_append, List.map_cons, List.map_nil] at hnd
    have hnd' : (L.map Prod.snd).Nodup := hnd.sublist (List.sublist_append_left _ _)
    have hp : p.2 ∉ L.map Prod.snd := by
      intro h
      have := (List.nodup_append.1 hnd).2.2 _ h _ (List.mem_singleton_self _)
      exact this rfl
    have hk : swift.sigMap L !! p.2 = none := by
      cases h : swift.sigMap L !! p.2 with
      | none => rfl
      | some _ => exact absurd (swift.sigMap_lookup L p.2 (by simp [h])) hp
    iintro ⟨Ha, Hl⟩
    rw [swift.sigMap_snoc]
    icases (BigSepL.bigSepL_snoc).1 $$ Hl with ⟨Hl, Hx⟩
    imod ghost_map_delete (γ := γs) $$ Ha Hx with Ha
    rw [GMap.delete_insert _ _ _ hk]
    iapply ih hnd'
    iframe

theorem swift.Replica.stopDescs.wp_specD
    (γ : sp.Names) (rp : Loc) (x : swift.RunX) (DR : Loc → IProp netDistGF) (g : swift.DescG)
    (dmc : GoSlice) (dcap : w64) (hSq : swift.sqOk γ DR (swift.sqE g) g.mp) (c0 : swift.DC)
    (RC : Loc → w32 → IProp netDistGF) (hSo : swift.soOk γ DR c0 RC g) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp dmc x.γdl x.γn dcap) ∗
        swift.descStateR γ rp x DR (swift.descGo x.γn g x.str) g }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"stopDescs")) (Val #()))
    {{ RET #(); swift.descsDone γ rp x DR g }} := by
  wp_start as ⟨#HcntL, Hds⟩
  iunfold swift.descStateR at Hds
  icases Hds with ⟨%dm1, Hcd, #Hdm, Hrd, #HI, Hst, Hfz, HS, Hb, HSS, #HSI⟩
  wp_auto
  ihave HL : ("HSS" ∷ swift.seqStore g ∗ "Hcd" ∷ typedPointsto (swift.fld rp go!"cmdDescs") dm1 (DFrac.own (1 : Qp).half) ∗ "Hrd" ∷ github_com.orcaman.concurrent_map.readerV dm1 g.γdc (swift.descR x.γd) ∗
      "Hst" ∷ ghostVar g.γst (1 : Qp).half false ∗
      "Hfz" ∷ swift.cntFrozen x.γn false ∗ "HS" ∷ ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
      "Hb" ∷ ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ "r" ∷ r_ptr ↦ rp : IProp netDistGF) $$ [Hcd Hrd Hst Hfz HS Hb r HSS]
  · iframe
  wp_for HL
  wp_method_call
  try wp_auto
  wp_apply (SwiftKitDeps.iterCbVP dm1 g.γdc
      (swift.descR x.γd) _ (swift.roundI g wgs_ptr))
    $$ [Hrd HS Hb Hst wgs] as ⟨Hrd, %nsh, %obs, %vis, -, HR, -⟩
  · iframe Hrd
    isplitl [HS Hb Hst wgs]
    · iunfold swift.roundI
      iexists [], slice.nil
      iframe
      simp only [List.map_nil]
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · ipureintro; exact ⟨fun k hk => by simp at hk, List.nodup_nil⟩
      iempintro
    isplitr
    · imodintro
      iintro %obs %vis HR
      iunfold swift.roundI at HR
      icases HR with ⟨%L, %sl, Hwp, Hsl, Hcap, HS, %HSv, Had, Hb, Hst⟩
      imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.descN)
        swift.descN_sub) $$ HI with ⟨Hi, Hclose⟩
      iunfold swift.descInv at Hi
      icases Hi with ⟨%st, >Hst2, Hrest⟩
      icombine Hst Hst2 gives %Hc
      obtain ⟨-, Heq⟩ := Hc
      subst Heq
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrest with ⟨%Mc, Hrest⟩
      icases Hrest with ⟨%q0, Hrest⟩
      icases Hrest with ⟨%L', Hrest⟩
      icases Hrest with ⟨%dm2, Hrest⟩
      icases Hrest with ⟨%W, >Hview, Hrest⟩
      imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN)
        (E2 := ∅) (by simp)) with Hback
      imodintro
      iexists Mc
      iframe Hview
      iintro Hview
      imod Hback with -
      imod Hclose $$ [Hst2 Hview Hrest] with -
      · inext
        iunfold swift.descInv
        iexists false
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hst2
        iexists Mc, q0, L', dm2, W
        iframe
      imodintro
      iunfold swift.roundI
      iexists L, sl
      iframe
      ipureintro; exact HSv
    · imodintro
      iintro %obs %vis %k %v %π %Φ' %Hkv Hpin HRk HR HΦ'
      obtain ⟨-, hkv⟩ := Hkv
      iunfold swift.descR at HRk
      icases HRk with ⟨%d0, %Hv0, -⟩
      subst Hv0
      iunfold swift.roundI at HR
      icases HR with ⟨%L, %sl, Hwp, Hsl, Hcap, HS, %HSv, Had, Hb, Hst⟩
      wp_auto_lc 2
      -- round 37 (D37, G-lend): `k` is not yet in the round's map
      have hnot : k ∉ L.map Prod.snd := fun h => hkv (HSv.1 _ h)
      have hS : swift.sigMap L !! k = none := by
        cases h : swift.sigMap L !! k with
        | none => rfl
        | some _ => exact absurd (swift.sigMap_lookup L _ (by simp [h])) hnot
      -- lend the entry's state for the reads
      iapply fupd_wp
      imod swift.descInv_lend γ x.γd x.γn x.γout g (x.epN rp) DR (swift.descGo x.γn g x.str) x.str k _ π
        (swift.sigMap L) hS $$ [Hst Hpin Hb HS Hlc1] with ⟨Hst, Hpin, Hb, HS, %d, %y, %Hv, HE⟩
      · iframe HI; iframe
      have hd : d0 = d := swift.mkOk_desc_inj d0 d Hv.1
      subst hd
      obtain ⟨-, hky⟩ := Hv
      ihave ⟨HS, %a, %s, %qa, Hact, Hseq, Hback⟩ :=
        swift.entS_view γ DR x.γn g x.str hSq d0 y (swift.sigMap L) k hky $$ [HE HS]
      · iframe
      imodintro
      try wp_auto
      cases a
      · -- not active
        iapply wp_fupd
        try wp_auto
        ihave HE := Hback $$ Hact Hseq
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        imod swift.descInv_return γ x.γd x.γn x.γout g (x.epN rp) DR (swift.descGo x.γn g x.str) x.str
          (swift.descGo_seq x.γn g x.str) hSq k _ π d0 y ⟨rfl, hky⟩ _
          (ghostMapElem g.γs k (DFrac.own 1) false) .rfl $$ [Hst Hpin Hb Hlc2 HE]
          with ⟨Hst, Hpin, Hb, Hel⟩
        · iframe HI; iframe
          iintro HE Hel; imodintro; iframe
        imod ghost_map_delete (γ := g.γs) $$ HS Hel with HS
        rw [GMap.delete_insert _ k false hS]
        imodintro
        iapply HΦ' $$ Hpin
        iunfold swift.roundI
        iexists L, sl
        iframe
        ipureintro
        refine ⟨fun k' hk' => ?_, HSv.2⟩
        simp only [List.map_append, List.mem_append]
        exact Or.inl (HSv.1 k' hk')
      cases s
      · -- active, not sequential: signal
        try wp_auto
        ihave HG := Hback $$ Hact Hseq
        simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
        iunfold swift.goA at HG
        icases HG with ⟨%sc, %γc, %γsg, HG⟩
        ihave ⟨Hsc, #Hbag, HGb⟩ := swift.goAn_sc x.γn g x.str d0 y sc γc γsg $$ HG
        iapply fupd_wp
        imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ «$r0» with ⟨%γwg, Hwg1, Hwg2, Hwg3⟩
        imod sync.join.init _ γwg $$ [Hwg1 Hwg2 Hwg3] with Hadw
        · iframe
        imodintro
        try wp_auto
        wp_apply (sync.join.WaitGroup.wp_Add (ghostMapElem g.γs (x.str y) (DFrac.own 1) true)
          _ _ (W32 0)) $$ [Hadw] as ⟨Hadw, Hdone⟩
        · iframe; ipureintro; decide
        try wp_auto
        -- `desc.stopChan` read with the lent state; then its return with the signal (G-lend)
        ihave HG := HGb $$ Hsc
        iapply fupd_wp
        imod swift.descInv_return γ x.γd x.γn x.γout g (x.epN rp) DR (swift.descGo x.γn g x.str) x.str
          (swift.descGo_seq x.γn g x.str) hSq k _ π d0 y ⟨rfl, hky⟩
          (swift.goAn x.γn g x.str d0 y sc γc γsg)
          iprop(ghostMapAuth g.γs 1 ((swift.sigMap L).insert k true) ∗ swift.sgTok γsg ∗
            ghostMapElem g.γs (x.str y) (DFrac.own (1 : Qp).half) true)
          (swift.goAn_entS γ DR x.γn g x.str d0 y sc γc γsg) $$ [Hst Hpin Hb Hlc2 HG HS]
          with ⟨Hst, Hpin, Hb, HS, Hsg, Hhalf⟩
        · iframe HI; iframe
          iintro HG Hel
          rw [hky]
          imod swift.goA_signal x.γn g x.str d0 y sc γc γsg (swift.sigMap L) _ $$ [HG HS Hel]
            with ⟨HG, HS, Hsg, Hh⟩
          · iframe
          imodintro
          iframe HS Hsg Hh
          iapply swift.goAn_entS γ DR x.γn g x.str d0 y sc γc γsg $$ HG
        imodintro
        iunfold swift.stopBag at Hbag
        icases Hbag with ⟨%W, #Hbag, #HW⟩
        wp_apply (wp_bag_send (t := go.GoType.PointerType sync.WaitGroup.ty) γc sc _
          (fun wg => iprop(swift.stopMP g.γs γsg (x.str y) d0 sc wg ∗ □ W))) $$ [Hdone Hsg Hhalf]
        · iframe Hbag HW; iunfold swift.stopMP; iframe
        try wp_auto
        wp_apply wp_slice_literal (V := Loc) [_]
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨Hs1, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hsl Hcap Hs1] as %nsl ⟨Hsl, Hcap, -⟩
        · iframe
        try wp_auto
        iapply HΦ' $$ Hpin
        iunfold swift.roundI
        iexists (L ++ [(_, x.str y)]), nsl
        rw [swift.sigMap_snoc]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [← hky]
        iframe
        isplitr
        · ipureintro
          refine ⟨fun k' hk' => ?_, ?_⟩
          · simp only [List.map_append, List.mem_append, List.mem_cons, List.map_cons,
              List.map_nil, List.mem_singleton] at hk' ⊢
            rcases hk' with h | h
            · exact Or.inl (HSv.1 k' h)
            · right; simp at h; rw [h]; simp
          · exact List.nodup_append.2 ⟨HSv.2, by simp,
              fun a ha b hb h => hnot (by subst h; simp at hb; first | (rw [← hb]; exact ha) | (rw [hky, ← hb]; exact ha) | simp_all)⟩
        iapply (BigSepL.bigSepL_singleton).2
        rw [show (W32 0 + W32 1 : w32) = W32 1 from rfl]
        rw [hky]
        iexact Hadw
      · -- sequential
        iapply wp_fupd
        try wp_auto
        ihave HE := Hback $$ Hact Hseq
        simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        imod swift.descInv_return γ x.γd x.γn x.γout g (x.epN rp) DR (swift.descGo x.γn g x.str) x.str
          (swift.descGo_seq x.γn g x.str) hSq k _ π d0 y ⟨rfl, hky⟩ _
          (ghostMapElem g.γs k (DFrac.own 1) false) .rfl $$ [Hst Hpin Hb Hlc2 HE]
          with ⟨Hst, Hpin, Hb, Hel⟩
        · iframe HI; iframe
          iintro HE Hel; imodintro; iframe
        imod ghost_map_delete (γ := g.γs) $$ HS Hel with HS
        rw [GMap.delete_insert _ k false hS]
        imodintro
        iapply HΦ' $$ Hpin
        iunfold swift.roundI
        iexists L, sl
        iframe
        ipureintro
        refine ⟨fun k' hk' => ?_, HSv.2⟩
        simp only [List.map_append, List.mem_append]
        exact Or.inl (HSv.1 k' hk')
  iunfold swift.roundI at HR
  icases HR with ⟨%L, %sl, Hwp, Hsl, Hcap, HS, %HSv, Had, Hb, Hst⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  try wp_auto
  -- the `Wait`s, one per request
  ihave HW : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗ "wg" ∷ (∃ w : Loc, wg_ptr ↦ w) ∗ "Hsl" ∷ sl ↦* L.map Prod.fst ∗
      "Had" ∷ ([∗list] p ∈ L.drop (sint.nat i), sync.join.ownAdder p.1 (W32 1)
        iprop(True ∗ ghostMapElem g.γs p.2 (DFrac.own 1) true)) ∗
      "Hel" ∷ ([∗list] p ∈ L.take (sint.nat i),
        ▷ iprop(True ∗ ghostMapElem g.γs p.2 (DFrac.own 1) true)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp netDistGF)
    $$ [i wg Hsl Had]
  · iexists (W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    iframe
    isplitl [wg]
    · iexists _; iexact wg
    isplitr
    · iempintro
    ipureintro; exact ⟨by decide, by word⟩
  wp_for HW
  icases wg with ⟨%w0, wg⟩
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hiL : sint.nat i < L.length := by
      have := Hsll.1; simp only [List.length_map] at this; rw [this]; word
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, hlt⟩
    try rw [ite_eq_left hb]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType sync.WaitGroup.ty) sl (sint.Z i)
      (L.map Prod.fst) _ (L[sint.nat i]).1 Hi.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro
      simp only [List.getElem?_map]
      rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_eq_getElem hiL]; rfl
    try wp_auto
    rw [List.drop_eq_getElem_cons hiL]
    icases (BigSepL.bigSepL_cons).1 $$ Had with ⟨Hp, Had⟩
    wp_apply sync.join.WaitGroup.wp_Wait $$ [Hp] as ⟨HP, -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hi1, List.take_add_one, List.getElem?_eq_getElem hiL]
    simp only [Option.toList_some]
    iframe Had
    isplitl [i]
    · iexact i
    isplitl [wg]
    · iexists _; iexact wg
    isplitl [Hsl]
    · iexact Hsl
    isplitl [Hel HP]
    · iapply (BigSepL.bigSepL_snoc).2
      iframe HP
      iapply (BigSepL.bigSepL_mono (fun _ => later_intro)) $$ Hel
    ipureintro; exact ⟨by word, by word⟩
  -- after the `Wait`s: every request's element back
  have hiv : sint.nat i = L.length := by
    have := Hsll.1; simp only [List.length_map] at this; rw [this]
    have : ¬ sint.Z i < sint.Z sl.len := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    word
  have hnlt : ¬ sint.Z i < sint.Z sl.len := by
    first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
  have hf : (#(decide (sint.Z i < sint.Z sl.len)) : val) = #false := by rw [decide_eq_false hnlt]
  try simp only [decide_eq_true hf, ↓reduceIte]
  rw [hiv, List.take_length]
  iapply fupd_wp
  ihave Hel := (BigSepL.bigSepL_mono (fun _ => sep_elim_right)) $$ Hel
  imod swift.sig_reset g.γs L HSv.2 $$ [HS Hel] with HS
  · iframe
  imodintro
  try wp_auto
  wp_if_destruct
  · -- no descriptor signalled: read `routineCount`
    try wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hclk, HC⟩
    iunfold swift.cntLInvR at HC
    icases HC with ⟨%sq, %rc0, %T0, Hsq, Hrc0, HcG⟩
    wp_auto_lc 1
    by_cases hle : sint.Z rc0 ≤ 0
    · iapply fupd_wp
      imod swift.cntLGhost_freeze x.γn dmc x.γdl dcap rc0 T0 hle $$ [HcG Hfz] with ⟨%HcT, HcG, Hfz⟩
      · iframe
      obtain ⟨-, hT0⟩ := HcT
      subst hT0
      imod swift.descInv_take_frozen γ x.γd x.γn x.γout g (x.epN rp) DR (swift.descGo x.γn g x.str) x.str
        (swift.descGo_elem x.γn g x.str) c0 RC hSo dmc x.γdl dcap rc0 $$ [HI Hst HcG Hfz Hb HSS HS]
        with ⟨HcG, Hfz, Hb, Hst, Hsh, Hout, ⟨%dm1', Hcd2⟩, -, %Mc, Hview, Hents, HInc⟩
      · iframe HI Hst HcG Hfz Hb HSS HSI HS
      imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hents with Hents
      imodintro
      wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hsq Hrc0 HcG]
      · iunfold swift.cntLInvR; iexists _, _, []; iframe
      try wp_auto
      wp_if_destruct
      · wp_for_post
        iapply HΦ
        iunfold swift.descsDone
        iexists dm1, Mc
        rw [show (x.epN rp).rp = rp from rfl]
        ihave ⟨%hdm, Hcdw⟩ := typedPointsto_half_combine (swift.fld rp go!"cmdDescs") dm1 dm1' (1 : Qp)
          $$ [Hcd Hcd2]
        · iframe
        subst hdm
        iframe Hdm Hcdw
        iframe
      · exfalso; have h0 : sint.Z (W64 0) = 0 := rfl; omega
    · wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hclk Hsq Hrc0 HcG]
      · iunfold swift.cntLInvR; iexists _, _, _; iframe
      try wp_auto
      wp_if_destruct
      · exfalso; have h0 : sint.Z (W64 0) = 0 := rfl; omega
      · wp_for_post
        unfold named
        iframe
  · try wp_auto
    wp_for_post
    unfold named
    iframe

/-- A stopped entry: its descriptor for `handleSync`'s freeing. -/
theorem swift.descEntH_split (γ : sp.Names) (γd : GName) (DR : Loc → IProp netDistGF)
    (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface) :
    swift.descEntH γ γd DR str k v ⊢
      ∃ d : Loc, ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          swift.descFree (swift.descDF DR) d := by
  iintro H
  iunfold swift.descEntH at H
  icases H with ⟨%d, %y, %Hv, Hh⟩
  iunfold swift.descHome at Hh
  iexists d; iframe Hh; ipureintro; exact Hv.1

/-- A home entry's key fact (round 53, 51-2 (a)): its key is its command's. -/
theorem swift.descEntH_key (γ : sp.Names) (γd : GName) (DR : Loc → IProp netDistGF)
    (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface) :
    swift.descEntH γ γd DR str k v ⊢
      (∃ d : Loc, ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          swift.descFree (swift.descDF DR) d) ∗
        ∃ (d : Loc) (y : swift.CommandId),
          ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y⌝ := by
  iintro H
  iunfold swift.descEntH at H
  icases H with ⟨%d, %y, %Hv, Hh⟩
  iunfold swift.descHome at Hh
  isplitl [Hh]
  · iexists d; iframe Hh; ipureintro; exact Hv.1
  iexists d, y; ipureintro; exact Hv

/-- **`stopDescs`' result as `handleSync` wants it** (`descsStopped` at `DF := descDF DR`), the
frozen flag, the descriptors' epoch share (D16: no proposal halves). Round 53 (D73 (4)): with the
view's facts `swift.stopPS x` (the commit record, the keys' commands). Round B1 (D82 (4)): with
the epoch's free permit into `stopPS`, and the pool's context `descPoolCtxS` (its law needs the
permit spent). -/
theorem swift.descsDone_stopped (γ : sp.Names) (rp : Loc) (x : swift.RunX)
    (DR : Loc → IProp netDistGF) (g : swift.DescG) :
    swift.descsDone γ rp x DR g ∗ swift.descPoolCtxS (swift.descDF DR) (swift.stopPS x g.ev.b) rp ∗
      swift.cgG x g ∗ swift.freeP x.γcg g.ev.b ⊢
      swift.descsStopped x.γd (swift.descDF DR) (swift.stopPS x g.ev.b) rp ∗ swift.cntFrozen x.γn true ∗
      swift.epochShare (x.epN rp) g.ev g.Qd ∗ ghostVar g.γst (1 : Qp).half true ∗ ghostMapAuth x.γout (1 : Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Qp)) := by
  iintro ⟨H, #Hpool, #Hcg, Hfp⟩
  iunfold swift.descsDone at H
  icases H with ⟨%dm1, %Mc, Hcd, #Hdm, Hrd, Hview, Hents, Hfz, Hsh, Hst, Hout, HInc⟩
  ihave Hfs := (BigSepM.bigSepM_mono_of_forall (fun {k v} =>
    swift.descEntH_key γ x.γd DR x.str k v)) $$ Hents
  ihave ⟨Hfs, Hks⟩ := (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hfs
  iframe Hfz Hsh Hst Hout
  iunfold swift.descsStopped
  iexists dm1, g.γdc, Mc
  iframe Hcd Hdm Hrd Hview Hpool Hfs
  iunfold swift.stopPS
  iframe Hks Hfp
  inext
  iexists g
  iframe HInc Hcg
  ipureintro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
