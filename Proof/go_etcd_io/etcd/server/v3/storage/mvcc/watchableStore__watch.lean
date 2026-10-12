/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__watch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__cancelWatcher

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

/-- The state with a new live watcher `w` (synced if `b`, else unsynced). -/
def WsState.addW (σ : WsState) (b : Bool) (w : Loc) (r : WatchRange) (st0 : WatcherSt)
    (γw : WatcherNames) : WsState :=
  { σ with
    Ws := if b then <[w := r]> σ.Ws else σ.Ws
    Wu := if b then σ.Wu else <[w := r]> σ.Wu
    ST := <[w := st0]> σ.ST
    M := <[w := γw]> σ.M
    E := <[w := (([] : List EvM), γw.lo)]> σ.E }

section addW
variable (σ : WsState) (b : Bool) (w : Loc) (r : WatchRange) (st0 : WatcherSt) (γw : WatcherNames)
theorem WsState.addW_Lmu : (σ.addW b w r st0 γw).Lmu = σ.Lmu := rfl
theorem WsState.addW_Ws : (σ.addW b w r st0 γw).Ws = if b then <[w := r]> σ.Ws else σ.Ws := rfl
theorem WsState.addW_Wu : (σ.addW b w r st0 γw).Wu = if b then σ.Wu else <[w := r]> σ.Wu := rfl
theorem WsState.addW_ST : (σ.addW b w r st0 γw).ST = <[w := st0]> σ.ST := rfl
theorem WsState.addW_Wo : (σ.addW b w r st0 γw).Wo = σ.Wo := rfl
theorem WsState.addW_M : (σ.addW b w r st0 γw).M = <[w := γw]> σ.M := rfl
theorem WsState.addW_vs : (σ.addW b w r st0 γw).vs = σ.vs := rfl
theorem WsState.addW_vbs : (σ.addW b w r st0 γw).vbs = σ.vbs := rfl
theorem WsState.addW_VB : (σ.addW b w r st0 γw).VB = σ.VB := rfl
end addW

/-- A watcher without names is in no population. -/
theorem WsOk.fresh {σ : WsState} (h : WsOk σ) {w : Loc} (hM : σ.M !! w = none) :
    σ.ST !! w = none ∧ σ.Wo !! w = none ∧ ¬ σ.live w ∧ σ.Ws !! w = none ∧ σ.Wu !! w = none ∧
      σ.victimOf w = none ∧ σ.E !! w = none := by
  have hST : σ.ST !! w = none := by
    cases hs : σ.ST !! w with
    | none => rfl
    | some _ => have := h.st_m w (by rw [hs]; rfl); rw [hM] at this; cases this
  have hWo : σ.Wo !! w = none := by
    cases hs : σ.Wo !! w with
    | none => rfl
    | some _ => have := h.wo_m w (by rw [hs]; rfl); rw [hM] at this; cases this
  have hl : ¬ σ.live w := fun hl => by have := h.live_st w hl; rw [hST] at this; cases this
  unfold WsState.live at hl
  refine ⟨hST, hWo, by unfold WsState.live; exact hl, ?_, ?_, ?_, ?_⟩
  · cases hs : σ.Ws !! w with
    | none => rfl
    | some _ => exact absurd (Or.inl (by rw [hs]; rfl)) hl
  · cases hs : σ.Wu !! w with
    | none => rfl
    | some _ => exact absurd (Or.inr (Or.inl (by rw [hs]; rfl))) hl
  · cases hs : σ.victimOf w with
    | none => rfl
    | some _ => exact absurd (Or.inr (Or.inr (by rw [hs]; rfl))) hl
  · cases hs : σ.E !! w with
    | none => rfl
    | some _ => exact absurd ((h.live_e w).1 (by rw [hs]; rfl)) (by unfold WsState.live; exact hl)

theorem WsState.addW_live_ne (σ : WsState) (b : Bool) (w : Loc) (r : WatchRange) (st0 : WatcherSt)
    (γw : WatcherNames) {w' : Loc} (hne : w ≠ w') :
    (σ.addW b w r st0 γw).live w' ↔ σ.live w' := by
  unfold WsState.live WsState.addW WsState.victimOf
  cases b <;> simp [GMap.lookup_insert_ne _ _ hne, hne]

theorem WsState.addW_live (σ : WsState) (b : Bool) (w : Loc) (r : WatchRange) (st0 : WatcherSt)
    (γw : WatcherNames) : (σ.addW b w r st0 γw).live w := by
  unfold WsState.live WsState.addW
  cases b <;> simp [GMap.lookup_insert]

/-- The new watcher's state keeps the invariant's pure facts. -/
theorem WsOk.addW {σ : WsState} (h : WsOk σ) (b : Bool) (w : Loc) (r : WatchRange)
    (st0 : WatcherSt) (γw : WatcherNames) (hM : σ.M !! w = none)
    (hst : st0.compacted = false ∧ st0.restore = false ∧ st0.victim = false ∧ st0.ch ≠ null)
    (hd : b = true → σ.Lmu.length ≤ γw.lo) : WsOk (σ.addW b w r st0 γw) := by
  obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := h.fresh hM
  have hvo : (σ.addW b w r st0 γw).victimOf = σ.victimOf := rfl
  constructor
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; cases b <;> simp_all [WsState.addW]
    · cases b <;> simp_all [WsState.addW, GMap.lookup_insert_ne _ _ hw] <;> exact h.ws_wu w' h1
  · intro w' h1
    rw [hvo]
    by_cases hw : w = w'
    · subst hw; exact hv
    · cases b <;> simp_all [WsState.addW, GMap.lookup_insert_ne _ _ hw] <;> exact h.ws_v w' h1
  · intro w' h1
    rw [hvo]
    by_cases hw : w = w'
    · subst hw; exact hv
    · cases b <;> simp_all [WsState.addW, GMap.lookup_insert_ne _ _ hw] <;> exact h.wu_v w' h1
  · exact h.v_one
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW, GMap.lookup_insert]
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw]
      exact h.live_st w' ((σ.addW_live_ne b w r st0 γw hw).1 h1)
  · intro w'
    by_cases hw : w = w'
    · subst hw; simp only [WsState.addW, GMap.lookup_insert, Option.isSome_some, true_iff]
      exact σ.addW_live b w r st0 γw
    · rw [σ.addW_live_ne b w r st0 γw hw]
      simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw]
      exact h.live_e w'
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW, GMap.lookup_insert]
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h1 ⊢; exact h.st_m w' h1
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW, GMap.lookup_insert]
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h1 ⊢; exact h.wo_m w' h1
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW, GMap.lookup_insert]
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h1 ⊢; exact h.m_st w' h1
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW] at h1; rw [hWo] at h1; cases h1
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h1 ⊢; exact h.wo_st w' h1
  · intro w' h1
    by_cases hw : w = w'
    · subst hw; simp [WsState.addW] at h1; rw [hWo] at h1; cases h1
    · rw [σ.addW_live_ne b w r st0 γw hw]; exact h.wo_live w' h1
  · intro w' st' h1
    by_cases hw : w = w'
    · subst hw
      simp only [WsState.addW, GMap.lookup_insert, Option.some.injEq] at h1
      subst h1
      obtain ⟨h1, h2, h3, h4⟩ := hst
      refine ⟨h1, h2, fun _ => ?_, ?_⟩
      · rw [hvo, hv, h3]; simp
      · constructor
        · intro hc; exact absurd hc h4
        · intro hn; exact absurd (σ.addW_live b w r st0 γw) hn
    · simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h1
      obtain ⟨h1, h2, h3, h4⟩ := h.st_flags w' st' h1
      refine ⟨h1, h2, fun hl' => ?_, ?_⟩
      · rw [hvo]; exact h3 ((σ.addW_live_ne b w r st0 γw hw).1 hl')
      · rw [σ.addW_live_ne b w r st0 γw hw]; exact h4
  · intro w' st' h1
    exact h.wo_flags w' st' h1
  · intro w' γw' ed h1 h2 h3
    by_cases hw : w = w'
    · subst hw
      cases b
      · simp [WsState.addW, hWs] at h1
      · simp only [WsState.addW, GMap.lookup_insert, Option.some.injEq] at h2 h3
        subst h2 h3
        have := hd rfl
        show max γw.lo σ.Lmu.length ≤ γw.lo
        omega
    · have h1' : (σ.Ws !! w').isSome := by
        cases b <;> simp_all [WsState.addW, GMap.lookup_insert_ne _ _ hw]
      simp only [WsState.addW, GMap.lookup_insert_ne _ _ hw] at h2 h3
      exact h.synced_d w' γw' ed h1' h2 h3

end mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.slice_def_valid (l : Loc) (v : GoSlice) (dq : DFrac) :
    typedPointstoDef (GF := GF) l v dq ⊢ ⌜✓ dq⌝ :=
  heapPointsto_valid l dq #v

/-- Another watcher's resources are the same in the state with the new watcher. -/
theorem mvcc.memberRes_addW_ne (γ : mvcc.WsNames) (q : Qp) (σ : mvcc.WsState) (b : Bool) (w : Loc)
    (r : mvcc.WatchRange) (st0 : mvcc.WatcherSt) (γw : mvcc.WatcherNames) (w' : Loc)
    (st : mvcc.WatcherSt) (hne : w ≠ w') :
    mvcc.memberRes (GF := GF) γ q σ w' st = mvcc.memberRes γ q (σ.addW b w r st0 γw) w' st := by
  have hl : (σ.addW b w r st0 γw).live w' = σ.live w' :=
    propext (σ.addW_live_ne b w r st0 γw hne)
  have hM : (σ.addW b w r st0 γw).M !! w' = σ.M !! w' := GMap.lookup_insert_ne _ _ hne
  have hE : (σ.addW b w r st0 γw).E !! w' = σ.E !! w' := GMap.lookup_insert_ne _ _ hne
  have hWs : (σ.addW b w r st0 γw).Ws !! w' = σ.Ws !! w' := by
    cases b <;> simp [mvcc.WsState.addW, GMap.lookup_insert_ne _ _ hne, hne]
  have hWu : (σ.addW b w r st0 γw).Wu !! w' = σ.Wu !! w' := by
    cases b <;> simp [mvcc.WsState.addW, GMap.lookup_insert_ne _ _ hne, hne]
  have hv : (σ.addW b w r st0 γw).victimOf = σ.victimOf := rfl
  unfold mvcc.memberRes mvcc.popFacts
  simp only [hl, hM, hE, hWs, hWu, hv]

/-- A victim out keeps its facts in the state with the new watcher. -/
theorem mvcc.outRes_addW_ne (γ : mvcc.WsNames) (σ : mvcc.WsState) (b : Bool) (w : Loc)
    (r : mvcc.WatchRange) (st0 : mvcc.WatcherSt) (γw : mvcc.WatcherNames) (w' : Loc)
    (st : mvcc.WatcherSt) (hne : w ≠ w') :
    mvcc.outRes (GF := GF) γ σ w' st = mvcc.outRes γ (σ.addW b w r st0 γw) w' st := by
  have hM : (σ.addW b w r st0 γw).M !! w' = σ.M !! w' := GMap.lookup_insert_ne _ _ hne
  unfold mvcc.outRes
  simp only [hM]

/-- **The lock invariant with the new watcher** (synced if `b`, else unsynced, from its first
revision `γw.lo = minRev`, nothing delivered). -/
theorem mvcc.watch_close_body (s : Loc) (γ : mvcc.WsNames) (σ : mvcc.WsState) (b : Bool) (w : Loc)
    (r : mvcc.WatchRange) (fcs : GoSlice) (st0 : mvcc.WatcherSt) (γw : mvcc.WatcherNames)
    (C : mvcc.Log) (hok : mvcc.WsOk σ) (hM : σ.M !! w = none)
    (hst : st0.compacted = false ∧ st0.restore = false ∧ st0.victim = false ∧ st0.ch ≠ null)
    (hlo : (γw.lo : Int) = sint.Z st0.minRev) (hsr : sint.Z r.startRev ≤ γw.lo)
    (hd : b = true → σ.Lmu.length ≤ γw.lo) (hu : b = false → sint.Z st0.minRev < C.length) :
    ghostVar (GF := GF) γ.wst 1 σ ∗ ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗
      mvcc.idxCert γ.st.idx σ.Lmu ∗
      mvcc.ownWatcherGroup (mvcc.syncedAddr s) (if b then <[w := r]> σ.Ws else σ.Ws) ∗
      mvcc.ownWatcherGroup (mvcc.unsyncedAddr s) (if b then σ.Wu else <[w := r]> σ.Wu) ∗
      typedPointsto (mvcc.victimsAddr s) σ.vs (DFrac.own 1) ∗ ownSlice σ.vs σ.vbs (DFrac.own 1) ∗
      ownSliceCap GoMap σ.vs (DFrac.own 1) ∗ ⌜σ.vbs.length = σ.VB.length⌝ ∗
      ([∗list] x ∈ σ.vbs.zip σ.VB, mvcc.ownWatcherBatch x.1 x.2) ∗
      ([∗map] w' ↦ st ∈ σ.ST, mvcc.watcherOwn w' st) ∗ mvcc.watcherOwn w st0 ∗
      ([∗map] w' ↦ st ∈ σ.Wo, mvcc.watcherOwn w' st (1 : Qp).half) ∗
      ghostMapAuth γ.wmeta 1 (<[w := γw]> σ.M) ∗ mvcc.watchBudget γ 1 (<[w := γw]> σ.M) ∗
      □ ([∗map] w' ↦ _γw ∈ σ.M, ∃ (r' : mvcc.WatchRange) (fcs' : GoSlice),
        mvcc.watcherFixed w' r' fcs') ∗
      mvcc.watcherFixed w r fcs ∗
      ([∗map] w' ↦ st ∈ σ.ST, mvcc.memberRes γ 1 σ w' st) ∗
      □ ([∗map] w' ↦ st ∈ σ.Wo, mvcc.outRes γ σ w' st) ∗
      mvcc.watcherMeta γ w γw ∗ mvcc.watcherChan γ w γw st0.ch ∗ mvcc.filtersOk fcs ∗
      monoListAuthOwn γw.evs (1 : Qp).half ([] : List mvcc.EvM) ∗
      dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗ mvcc.idxCert γ.st.idx C ⊢
    |==> mvcc.watchStoreBody s γ 1 (σ.addW b w r st0 γw) := by
  obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := hok.fresh hM
  iintro ⟨Hσ, Hwlog, #Hcert, Hsy, Hun, Hvf, Hvs, Hvcap, %Hvlen, Hvbs, Hst, Hst0, Hwo, Hmeta,
    Hwt, #Hmfix, #Hfixed, Hmem, #Hout, #Hmw, #Hwc, #Hfo, He, Hl, #HC⟩
  imod ghostVar_update (σ.addW b w r st0 γw) γ.wst σ $$ Hσ with Hσ
  imodintro
  iunfold mvcc.watchStoreBody
  simp only [mvcc.WsState.addW_Lmu, mvcc.WsState.addW_Ws, mvcc.WsState.addW_Wu,
    mvcc.WsState.addW_ST, mvcc.WsState.addW_Wo, mvcc.WsState.addW_M, mvcc.WsState.addW_vs,
    mvcc.WsState.addW_vbs, mvcc.WsState.addW_VB, named]
  have hlb : ∀ (L : mvcc.Log), mvcc.watchEvents L r γw.lo γw.lo = [] :=
    fun L => mvcc.watchEvents_empty _ _ (Nat.le_refl _)
  ihave #Hlb : monoListLbOwn γ.st.idx.hist (mvcc.histOf C) $$ []
  · iunfold mvcc.idxCert at HC
    icases HC with ⟨H, -⟩
    iexact H
  iframe Hσ Hwlog Hvf Hvs Hvcap Hvbs Hwo Hmeta Hwt
  iframe #
  isplitl [Hsy]
  · cases b <;> iexact Hsy
  isplitl [Hun]
  · cases b <;> iexact Hun
  isplitr
  · ipureintro; exact Hvlen
  isplitl [Hst Hst0]
  · iapply (BigSepM.bigSepM_insert hST).2
    iframe Hst Hst0
  isplitr
  · iapply (BigSepM.bigSepM_insert hM).2
    iframe Hmfix
    iexists r, fcs
    iexact Hfixed
  isplitl [Hmem He Hl]
  · iapply (BigSepM.bigSepM_insert hST).2
    isplitl [He Hl]
    · iunfold mvcc.memberRes
      iexists γw, r, fcs
      isplitr
      · ipureintro; simp [mvcc.WsState.addW, GMap.lookup_insert]
      iframe Hmw Hfixed
      rw [ite_cond_eq_true _ _ (eq_true (σ.addW_live b w r st0 γw))]
      iframe Hwc Hfo He Hl
      isplitr
      · ipureintro; exact hsr
      iexists γw.lo
      isplitr
      · ipureintro; simp [mvcc.WsState.addW, GMap.lookup_insert]
      iunfold mvcc.popFacts
      cases b
      · simp only [mvcc.WsState.addW, GMap.lookup_insert, Option.isSome_some, ↓reduceIte,
          Bool.false_eq_true, hWs, Option.isSome_none]
        isplitr
        · ipureintro; refine ⟨by omega, ?_⟩
          rw [show sint.nat st0.minRev = (sint.Z st0.minRev).toNat from rfl]; omega
        isplitr
        · iunfold mvcc.evsWf; iexists C; iframe Hlb; ipureintro; exact ⟨(hlb C).symm, Or.inr (Nat.le_refl _)⟩
        iexists C
        iframe HC
        ipureintro; exact hu rfl
      · simp only [mvcc.WsState.addW, GMap.lookup_insert, Option.isSome_some, ↓reduceIte]
        isplitr
        · ipureintro; omega
        iunfold mvcc.evsWf; iexists C; iframe Hlb; ipureintro; exact ⟨(hlb C).symm, Or.inr (Nat.le_refl _)⟩
    iapply BigSepM.bigSepM_mono $$ Hmem
    intro w' st' hw'
    have hne : w ≠ w' := by
      rintro rfl; have h2 : σ.ST !! w = some st' := hw'; rw [hST] at h2; cases h2
    rw [mvcc.memberRes_addW_ne γ 1 σ b w r st0 γw w' st' hne]
  isplitr
  · iapply BigSepM.bigSepM_mono $$ Hout
    intro w' st' hw'
    have hne : w ≠ w' := by
      rintro rfl; have h2 : σ.Wo !! w = some st' := hw'; rw [hWo] at h2; cases h2
    rw [mvcc.outRes_addW_ne γ σ b w r st0 γw w' st' hne]
  ipureintro
  exact hok.addW b w r st0 γw hM hst hd

/-- The committed log's authority is above the notified log's certificate (kept). -/
theorem mvcc.watch_logAuth_prefix (γi : mvcc.IdxNames) (q : Qp) (C L : mvcc.Log) :
    mvcc.idxLogAuth (GF := GF) γi q C ∗ mvcc.idxCert γi L ⊢ mvcc.idxLogAuth γi q C ∗ ⌜L <+: C⌝ := by
  iintro H
  icases persistent_entails_right (mvcc.idxLogAuth_cert_prefix γi q C L) $$ H with ⟨%h, ⟨Ha, -⟩⟩
  iframe Ha
  ipureintro; exact h

/-- A channel is not `nil`. -/
theorem mvcc.isChan_ne_null (ch : Loc) (γc : ChanNames) :
    isChan (GF := GF) ch γc WatchResponse ⊢ ⌜ch ≠ null⌝ := by
  rw [isChan_unseal]
  unfold isChanDef
  iintro H
  iNamed H
  ipureintro; exact Hnotnull

/-- Filters each deciding some predicate decide a list of predicates. -/
theorem mvcc.filters_choose : ∀ (fps : List GoFunc),
    ([∗list] f ∈ fps, ∃ p : mvcc.EvM → Bool, mvcc.filterSpec (GF := GF) f p) ⊢
      ∃ ps : List (mvcc.EvM → Bool), ⌜fps.length = ps.length⌝ ∗
        [∗list] x ∈ fps.zip ps, mvcc.filterSpec x.1 x.2
  | [] => by
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    simp only [List.zip_nil_left]
    iapply BigSepL.bigSepL_nil.2; itrivial
  | f :: fps => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%p, Hp⟩, H⟩
    icases mvcc.filters_choose fps $$ H with ⟨%ps, %Hl, H⟩
    iexists (p :: ps)
    isplitr
    · ipureintro; simp [Hl]
    simp only [List.zip_cons_cons]
    iapply BigSepL.bigSepL_cons.2
    iframe Hp H

theorem mvcc.filtersOk_of (fcs : GoSlice) (fps : List GoFunc) :
    fcs ↦*□ fps ∗ ([∗list] f ∈ fps, ∃ p : mvcc.EvM → Bool, mvcc.filterSpec (GF := GF) f p) ⊢
      mvcc.filtersOk fcs := by
  iintro ⟨#Hs, H⟩
  icases mvcc.filters_choose fps $$ H with ⟨%ps, %Hl, H⟩
  iunfold mvcc.filtersOk
  iexists ps
  iunfold mvcc.filtersImpl
  iexists fps
  iframe Hs H
  ipureintro; exact Hl

/-- A field owned in full is not a field of a watcher with fixed fields (freshness). -/
theorem mvcc.watch_key_fresh (w : Loc) (ks : GoSlice) (r : mvcc.WatchRange) (fcs : GoSlice) :
    typedPointsto (GF := GF) (structFieldRef watcher go!"key" w) ks (DFrac.own 1) ∗
      mvcc.watcherFixed w r fcs ⊢ False := by
  iintro ⟨H1, H2⟩
  iunfold mvcc.watcherFixed at H2
  icases H2 with ⟨-, %ks', %es, H2, -⟩
  icombine H1 H2 gives %Heq
  subst Heq
  ihave H : typedPointsto (structFieldRef watcher go!"key" w) ks
      (DFrac.own 1 • DFrac.discard) $$ [H1 H2]
  · iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
    iframe H1 H2
  ihave H := typedPointsto_split _ _ _ $$ H
  ihave %Hv := (mvcc.slice_def_valid _ _ _) $$ H
  exfalso
  have := DFrac.valid_own_op_discard.1 Hv
  simp at this

/-- **Registering a new watcher** (ghost): its names (fresh: the watcher's key field is owned in
full, so no watcher with names, no registered watcher and no response is of it), registered on
its channel (the close right's watchers grow), its fixed fields persisted. -/
theorem mvcc.watch_register (γ : mvcc.WsNames) (M : GMap Loc mvcc.WatcherNames) (w ch : Loc)
    (ks : GoSlice) (r : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) (C : mvcc.Log) (L : List Loc) :
    £ 1 ∗ ghostMapAuth γ.wmeta 1 M ∗
      □ ([∗map] w' ↦ _γw ∈ M, ∃ (r' : mvcc.WatchRange) (fcs' : GoSlice),
        mvcc.watcherFixed w' r' fcs') ∗
      (∃ γc : mvcc.WatchChanNames, isChan ch γc.ch WatchResponse ∗
        inv mvcc.watchN (mvcc.watchChanInv γ ch γc) ∗ ghostVar γc.regl (1 : Qp).half L) ∗
      mvcc.idxCert γ.st.idx C ∗
      typedPointsto (GF := GF) (structFieldRef watcher go!"key" w) ks (DFrac.own 1) ∗
      □ (typedPointsto (structFieldRef watcher go!"key" w) ks DFrac.discard -∗
        mvcc.watcherFixed w r fcs) ⊢
    |={⊤}=> ∃ γw : mvcc.WatcherNames, ⌜M !! w = none ∧ γw.lo = lo⌝ ∗
      ghostMapAuth γ.wmeta 1 (M.insert w γw) ∗ mvcc.watcherMeta γ w γw ∗
      mvcc.watcherFixed w r fcs ∗ mvcc.watcherChan γ w γw ch ∗
      ghostVar γw.wc.regl (1 : Qp).half (w :: L) ∗
      monoListAuthOwn γw.evs (1 : Qp).half ([] : List mvcc.EvM) ∗
      dghostVar γw.live (DFrac.own (1 : Qp).half) true := by
  iintro ⟨Hlc, Hmeta, #Hmfix, ⟨%γc, #Hch, #Hinv, Hregl0⟩, #Hcert, Hkey, #Hfix⟩
  -- freshness of the names
  have hM : M !! w = none ∨ ∃ γw', M !! w = some γw' := by
    cases M !! w <;> simp
  ihave %hM : ⌜M !! w = none⌝ $$ [Hkey]
  · rcases hM with hM | ⟨γw', hM⟩
    · ipureintro; exact hM
    icases (BigSepM.bigSepM_lookup_acc hM).1 $$ Hmfix with ⟨⟨%r', %fcs', Hf⟩, -⟩
    iexfalso
    iapply mvcc.watch_key_fresh $$ [$Hkey $Hf]
  -- the watcher's ghosts
  imod mono_list_own_alloc (GF := GF) ([] : List mvcc.EvM) with ⟨%γe, He, -⟩
  have hfe := (monoListAuthOwn_fractional (GF := GF) γe ([] : List mvcc.EvM)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hfe
  icases hfe.1 $$ He with ⟨He1, He2⟩
  imod dghostVar_alloc (GF := GF) true with ⟨%γl, Hl⟩
  ihave Hl : dghostVar γl (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half) true $$ [Hl]
  · rw [← mvcc.own_half_half (1 : Qp)]; iexact Hl
  icases dghostVar_split γl true _ _ $$ Hl with ⟨Hl1, Hl2⟩
  let γw : mvcc.WatcherNames := ⟨γe, γl, γc, lo⟩
  -- the channel
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑mvcc.watchN) $$ Hlc Hi with Hi
  iunfold mvcc.watchChanInv at Hi
  icases Hi with ⟨%s0, %sent, %recv, %vs, %L', Hi⟩
  iNamed Hi
  ihave %HL := ghostVar_agree _ _ _ _ _ $$ Hregl0 Hregl
  subst HL
  ihave %Hopen : ⌜chanIsClosed s0 = false⌝ $$ [Hcl Hregl0 Hregl]
  · cases hcl : mvcc.chanIsClosed s0
    · ipureintro; rfl
    simp only [hcl, ↓reduceIte]
    icombine Hregl0 Hregl as H2
    ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ H2 Hcl
    exfalso
    try rw [Qp.half_add_half] at Hv
    exact absurd Hv.1 (qp_one_add_not_le _)
  rw [Hopen]
  -- `w` is not registered, and no response is of it
  by_cases HwL : w ∈ L
  · icases BigSepL.bigSepL_mem_acc HwL $$ Hws with ⟨Hw, -⟩
    iunfold mvcc.chanWatcher at Hw
    icases Hw with ⟨%γw', %r', %fcs', %evsw', %D', %d', #Hm', -⟩
    iunfold mvcc.watcherMeta at Hm'
    ihave %Hl := ghost_map_lookup $$ Hmeta Hm'
    exfalso
    rw [hM] at Hl
    cases Hl
  by_cases Hsent : ∃ x ∈ sent, x.w = w
  · obtain ⟨x, hx, hxw⟩ := Hsent
    icases BigSepL.bigSepL_mem_acc hx $$ Hok with ⟨Hx, -⟩
    iunfold mvcc.respOk at Hx
    icases Hx with ⟨-, %rr, %fcs', Hf, -⟩
    rw [hxw]
    iexfalso
    iapply mvcc.watch_key_fresh $$ [$Hkey $Hf]
  have Hsent' : sent.filter (fun x => decide (x.w = w)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx; simp only [decide_eq_true_eq]; exact fun h => Hsent ⟨x, hx, h⟩
  -- the fixed fields, the names, the registration
  ipersist Hkey
  ihave #Hfixed := Hfix $$ Hkey
  imod ghost_map_insert_persist w γw hM $$ Hmeta with ⟨Hmeta, #Hmw⟩
  have hreg : (mvcc.regMap L).lookup w = none := by
    have := mt (mvcc.regMap_lookup L w).1 HwL
    cases h : (mvcc.regMap L).lookup w with
    | none => rfl
    | some _ => exact absurd (by rw [show (mvcc.regMap L !! w) = (mvcc.regMap L).lookup w from rfl, h]; rfl) this
  imod ghost_map_insert_persist w () hreg $$ Hreg with ⟨Hreg, #Hrw⟩
  imod ghostVar_update_halves (w :: L) γc.regl _ _ $$ Hregl0 Hregl with ⟨Hregl0, Hregl⟩
  ihave #Hlb : monoListLbOwn γ.st.idx.hist (mvcc.histOf C) $$ []
  · iunfold mvcc.idxCert at Hcert
    icases Hcert with ⟨H, -⟩
    iexact H
  imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws He2 Hl2] with -
  · inext
    iunfold mvcc.watchChanInv
    iexists s0, sent, recv, vs, (w :: L)
    simp only [named]
    rw [Hopen]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hch Hrecv Hregl
    iframe #
    isplitr
    · ipureintro; exact Hpre
    isplitr
    · ipureintro; exact Hinfl
    isplitr
    · itrivial
    isplitl [Hreg]
    · have hrm : mvcc.regMap (w :: L) = (mvcc.regMap L).insert w () := rfl
      rw [hrm]; iexact Hreg
    isplitr
    · ipureintro; exact ⟨List.nodup_cons.2 ⟨HwL, Hnd.1⟩, fun x hx => List.mem_cons_of_mem _ (Hnd.2 x hx)⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Hws
    iunfold mvcc.chanWatcher
    iexists γw, r, fcs, [], [], lo
    iframe He2 Hfixed
    isplitr
    · iunfold mvcc.watcherMeta; iexact Hmw
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨rfl, by rw [Hsent']; rfl⟩
    isplitr
    · imodintro
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      iunfold mvcc.delivsCut
      iintro !> %k %hk
      simp only [List.length_nil, Nat.le_zero] at hk
      subst hk
      iexists lo
      iunfold mvcc.evsWf
      iexists C
      iframe Hlb
      ipureintro
      exact ⟨(mvcc.watchEvents_empty _ _ (Nat.le_refl _)).symm, Or.inr (Nat.le_refl _)⟩
    isplitr
    · iunfold mvcc.evsWf
      iexists C
      iframe Hlb
      ipureintro
      exact ⟨(mvcc.watchEvents_empty _ _ (Nat.le_refl _)).symm, Or.inr (Nat.le_refl _)⟩
    ileft
    iframe Hl2
    ipureintro; rfl
  imodintro
  iexists γw
  iframe Hmeta Hfixed Hregl0 He1 Hl1
  isplitr
  · ipureintro; exact ⟨hM, rfl⟩
  isplitr
  · iunfold mvcc.watcherMeta; iexact Hmw
  iunfold mvcc.watcherChan
  iframe Hch Hinv Hrw

theorem mvcc.watchableStore.watch.wp_proof
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG))
    (hCancel : mvcc.watchableStore.cancelWatcher.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.watch.spec (GF := GF) (hG := hG) := by
  have hAdd := mvcc.watcherGroup.add.spec_group hAdd
  intro s st γ key endk fcs k e fs startRev id ch L
  simp only [mvcc.storeWatchParams]
  wp_start as ⟨#Hws, #Hk, #He, #Hfcs, #Hfs, -, HCR, HR, Htok, %Hsr⟩
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%gw, #Hgw, #HgwS⟩,
    ⟨%gs, #Hgs, #HgsS⟩, -⟩
  iunfold gaugeSpec at HgwS HgsS
  icases HgwS with ⟨#HgwI, -, -⟩
  icases HgsS with ⟨#HgsI, -, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  iunfold mvcc.storeReader at Hsr0
  iNamedSuffix Hsr0 "R"
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  icases mvcc.watchBudget_bound _ _ _ $$ Hwt with ⟨Hwt, %HMb⟩
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrl, HQ⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv st γ.st sync.rfrac)) $$ Hlc1 HQ with HQ
  iunfold mvcc.revMuInv at HQ
  icases HQ with ⟨%C, %ntok, HQ⟩
  iNamedSuffix HQ "Q"
  icases persistent_entails_right (typedPointsto_not_null _ _ _) $$ «$r0» with ⟨%Hwnn, «$r0»⟩
  iStructNamed «$r0»
  -- the committed log `C` read: the notified log is a prefix of it
  icases mvcc.watch_logAuth_prefix _ _ _ _ $$ [$HlogQ $Hcert] with ⟨HlogQ, %HpC⟩
  ihave %HCwf : ⌜C.length < 2 ^ 63⌝ $$ [HcertQ]
  · iunfold mvcc.idxCert at HcertQ
    icases HcertQ with ⟨-, -, %H, -⟩
    ipureintro; exact H.2.1
  -- the watcher's range, first revision, and fixed fields
  generalize hw : «$r0_ptr» = w at *
  let r : mvcc.WatchRange :=
    { key := k, end? := if endk = slice.nil then none else some e, startRev := startRev, id := id }
  let synced : Bool :=
    decide (sint.Z (W64 ((C.length : Int) - 1)) < sint.Z startRev) || decide (startRev = W64 0)
  let lo : Nat := if synced then max C.length (sint.nat startRev) else sint.nat startRev
  ipersist end'
  ipersist startRev
  ipersist id
  ipersist fcs
  ihave #Hfix : □ (typedPointsto (structFieldRef watcher go!"key" w) key DFrac.discard -∗
      mvcc.watcherFixed w r fcs) $$ []
  · imodintro
    iintro #Hkey
    iunfold mvcc.watcherFixed
    isplitr
    · ipureintro; exact Hwnn
    iexists key, endk
    iframe Hkey Hk end' startRev id fcs
    by_cases hn : endk = slice.nil
    · simp only [r, hn, ↓reduceIte]
      first | (ipureintro; exact hn) | itrivial | (ipureintro; trivial)
    · simp only [r, hn, ↓reduceIte]
      iframe He
      ipureintro; exact hn
  imod mvcc.watch_register γ σ.M w ch key r fcs lo C L $$ [$Hlc2 $Hmeta $Hmfix $HCR $HcertQ $key $Hfix]
    with ⟨%γw, ⟨%hM, %hlo⟩, Hmeta, #Hmw, #Hfixed, #Hwc, HCR, He, Hl⟩
  -- the registration's token spent
  imod mvcc.watchBudget_spend γ σ.M w γw hM $$ [$Hwt $Htok] with Hwt
  have hCne : 1 ≤ C.length := List.length_pos_iff.2 HneQ
  have hcur : sint.Z (W64 ((C.length : Int) - 1)) = (C.length : Int) - 1 := by word
  wp_auto
  have hcur1 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) = (C.length : Int) := by word
  have hLmu : σ.Lmu.length ≤ C.length := HpC.length_le
  -- the synced cases end with `minRev = m` for an `m` that is the first revision
  by_cases hs : sint.Z (W64 ((C.length : Int) - 1)) < sint.Z startRev
  · rw [decide_eq_true hs]
    wp_auto
    have hsy : synced = true := by simp only [synced, decide_eq_true hs, Bool.true_or]
    by_cases h2 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) < sint.Z startRev
    · rw [decide_eq_true h2]
      wp_auto
      have hm : (lo : Int) = sint.Z startRev := by
        simp only [lo, hsy, ↓reduceIte]
        rw [show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega
      obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := Hok.fresh hM
      wp_apply hAdd $$ [$Hsynced] as Hsynced
      · iframe Hfixed; ipureintro; exact ⟨hWs, by have := Hok.ws_size; omega⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ] as HrevMuR
      · inext
        iunfold mvcc.revMuInv
        iexists C, ntok
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨HneQ, HbudgetQ⟩
      (try wp_auto)
      -- the lock invariant with the new unsynced watcher
      ihave %Hchnn : ⌜ch ≠ null⌝ $$ []
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, -⟩
        iapply mvcc.isChan_ne_null $$ Hic
      ihave #Hfo := mvcc.filtersOk_of fcs fs $$ [$Hfcs $Hfs]
      let st0 : mvcc.WatcherSt := ⟨startRev, false, false, false, ch⟩
      have hlomax : lo = max C.length (sint.nat startRev) := by simp only [lo, hsy]; rfl
      imod mvcc.watch_close_body s γ σ true w r fcs st0 γw C Hok hM
          ⟨rfl, rfl, rfl, Hchnn⟩
          (by show ((γw.lo : Nat) : Int) = sint.Z (startRev); rw [hlo]; exact hm)
          (by show sint.Z startRev ≤ ((γw.lo : Nat) : Int)
              rw [hlo, hlomax, show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega)
          (fun _ => by rw [hlo, hlomax]; omega) (fun h => by cases h)
        $$ [Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst minRev victim compacted restore ch
          Hwo Hmeta Hwt Hmem He Hl]
        with Hbody
      · simp only [↓reduceIte]
        iframe Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem He Hl
        iframe #
        iunfold mvcc.watcherOwn
        iframe minRev victim compacted restore ch
        ipureintro; exact Hvlen
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
      · inext
        iunfold mvcc.watchStoreInv
        iexists _
        iexact Hbody
      (try wp_auto)
      ipersist wa
      ipersist s
      wp_apply HgwI
      (try wp_auto)
      simp only [recv_eq_func_mk]
      iapply HΦ
      isplitr
      · ipureintro; exact Hwnn
      isplitr
      · iexists γw, r, fcs
        iframe Hmw Hfixed
        ipureintro; exact Hsr
      isplitr
      · iunfold mvcc.cancelSpec
        imodintro
        imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply (hCancel s st γ w) $$ [] as HWC
        · iframe #
          simp only [mvcc.storeWatchParams]
          iexists γw, r, fcs
          iframe Hmw Hfixed
          ipureintro; exact Hsr
        (try wp_auto)
        iapply HΦ'
        simp only [mvcc.storeWatchParams] at *
        iexact HWC
      isplitl [HCR]
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, Hinv, -⟩
        iexists γw.wc
        iframe Hic Hinv HCR
      iunfold mvcc.watchReader
      iframe Hmur
      iunfold mvcc.storeReader
      iexists ti
      simp only [named]
      iframe HmuR HrevMuR HtiR
      iframe #
    · rw [decide_eq_false h2]
      wp_auto
      have hm : (lo : Int) = sint.Z (W64 ((C.length : Int) - 1) + W64 1) := by
        simp only [lo, hsy, ↓reduceIte]
        rw [show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega
      obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := Hok.fresh hM
      wp_apply hAdd $$ [$Hsynced] as Hsynced
      · iframe Hfixed; ipureintro; exact ⟨hWs, by have := Hok.ws_size; omega⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ] as HrevMuR
      · inext
        iunfold mvcc.revMuInv
        iexists C, ntok
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨HneQ, HbudgetQ⟩
      (try wp_auto)
      -- the lock invariant with the new unsynced watcher
      ihave %Hchnn : ⌜ch ≠ null⌝ $$ []
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, -⟩
        iapply mvcc.isChan_ne_null $$ Hic
      ihave #Hfo := mvcc.filtersOk_of fcs fs $$ [$Hfcs $Hfs]
      let st0 : mvcc.WatcherSt := ⟨W64 ((C.length : Int) - 1) + W64 1, false, false, false, ch⟩
      have hlomax : lo = max C.length (sint.nat startRev) := by simp only [lo, hsy]; rfl
      imod mvcc.watch_close_body s γ σ true w r fcs st0 γw C Hok hM
          ⟨rfl, rfl, rfl, Hchnn⟩
          (by show ((γw.lo : Nat) : Int) = sint.Z (W64 ((C.length : Int) - 1) + W64 1); rw [hlo]; exact hm)
          (by show sint.Z startRev ≤ ((γw.lo : Nat) : Int)
              rw [hlo, hlomax, show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega)
          (fun _ => by rw [hlo, hlomax]; omega) (fun h => by cases h)
        $$ [Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst minRev victim compacted restore ch
          Hwo Hmeta Hwt Hmem He Hl]
        with Hbody
      · simp only [↓reduceIte]
        iframe Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem He Hl
        iframe #
        iunfold mvcc.watcherOwn
        iframe minRev victim compacted restore ch
        ipureintro; exact Hvlen
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
      · inext
        iunfold mvcc.watchStoreInv
        iexists _
        iexact Hbody
      (try wp_auto)
      ipersist wa
      ipersist s
      wp_apply HgwI
      (try wp_auto)
      simp only [recv_eq_func_mk]
      iapply HΦ
      isplitr
      · ipureintro; exact Hwnn
      isplitr
      · iexists γw, r, fcs
        iframe Hmw Hfixed
        ipureintro; exact Hsr
      isplitr
      · iunfold mvcc.cancelSpec
        imodintro
        imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply (hCancel s st γ w) $$ [] as HWC
        · iframe #
          simp only [mvcc.storeWatchParams]
          iexists γw, r, fcs
          iframe Hmw Hfixed
          ipureintro; exact Hsr
        (try wp_auto)
        iapply HΦ'
        simp only [mvcc.storeWatchParams] at *
        iexact HWC
      isplitl [HCR]
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, Hinv, -⟩
        iexists γw.wc
        iframe Hic Hinv HCR
      iunfold mvcc.watchReader
      iframe Hmur
      iunfold mvcc.storeReader
      iexists ti
      simp only [named]
      iframe HmuR HrevMuR HtiR
      iframe #
  · rw [decide_eq_false hs]
    wp_auto
    by_cases h0 : startRev = W64 0
    · rw [decide_eq_true h0]
      wp_auto
      have hsy : synced = true := by simp only [synced, decide_eq_true h0, Bool.or_true]
      by_cases h2 : sint.Z (W64 ((C.length : Int) - 1) + W64 1) < sint.Z startRev
      · exfalso; rw [h0] at h2; have : sint.Z (W64 0) = 0 := rfl; omega
      · rw [decide_eq_false h2]
        wp_auto
        have hm : (lo : Int) = sint.Z (W64 ((C.length : Int) - 1) + W64 1) := by
          simp only [lo, hsy, ↓reduceIte]
          rw [show sint.nat startRev = (sint.Z startRev).toNat from rfl, h0]
          have : sint.Z (W64 0) = 0 := rfl
          omega
        obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := Hok.fresh hM
        wp_apply hAdd $$ [$Hsynced] as Hsynced
        · iframe Hfixed; ipureintro; exact ⟨hWs, by have := Hok.ws_size; omega⟩
        (try wp_auto)
        wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ] as HrevMuR
        · inext
          iunfold mvcc.revMuInv
          iexists C, ntok
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨HneQ, HbudgetQ⟩
        (try wp_auto)
        -- the lock invariant with the new unsynced watcher
        ihave %Hchnn : ⌜ch ≠ null⌝ $$ []
        · iunfold mvcc.watcherChan at Hwc
          icases Hwc with ⟨Hic, -⟩
          iapply mvcc.isChan_ne_null $$ Hic
        ihave #Hfo := mvcc.filtersOk_of fcs fs $$ [$Hfcs $Hfs]
        let st0 : mvcc.WatcherSt := ⟨W64 ((C.length : Int) - 1) + W64 1, false, false, false, ch⟩
        have hlomax : lo = max C.length (sint.nat startRev) := by simp only [lo, hsy]; rfl
        imod mvcc.watch_close_body s γ σ true w r fcs st0 γw C Hok hM
            ⟨rfl, rfl, rfl, Hchnn⟩
            (by show ((γw.lo : Nat) : Int) = sint.Z (W64 ((C.length : Int) - 1) + W64 1); rw [hlo]; exact hm)
            (by show sint.Z startRev ≤ ((γw.lo : Nat) : Int)
                rw [hlo, hlomax, show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega)
            (fun _ => by rw [hlo, hlomax]; omega) (fun h => by cases h)
          $$ [Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst minRev victim compacted restore ch
            Hwo Hmeta Hwt Hmem He Hl]
          with Hbody
        · simp only [↓reduceIte]
          iframe Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem He Hl
          iframe #
          iunfold mvcc.watcherOwn
          iframe minRev victim compacted restore ch
          ipureintro; exact Hvlen
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
        · inext
          iunfold mvcc.watchStoreInv
          iexists _
          iexact Hbody
        (try wp_auto)
        ipersist wa
        ipersist s
        wp_apply HgwI
        (try wp_auto)
        simp only [recv_eq_func_mk]
        iapply HΦ
        isplitr
        · ipureintro; exact Hwnn
        isplitr
        · iexists γw, r, fcs
          iframe Hmw Hfixed
          ipureintro; exact Hsr
        isplitr
        · iunfold mvcc.cancelSpec
          imodintro
          imodintro
          iintro %Φ' - HΦ'
          wp_auto
          wp_apply (hCancel s st γ w) $$ [] as HWC
          · iframe #
            simp only [mvcc.storeWatchParams]
            iexists γw, r, fcs
            iframe Hmw Hfixed
            ipureintro; exact Hsr
          (try wp_auto)
          iapply HΦ'
          simp only [mvcc.storeWatchParams] at *
          iexact HWC
        isplitl [HCR]
        · iunfold mvcc.watcherChan at Hwc
          icases Hwc with ⟨Hic, Hinv, -⟩
          iexists γw.wc
          iframe Hic Hinv HCR
        iunfold mvcc.watchReader
        iframe Hmur
        iunfold mvcc.storeReader
        iexists ti
        simp only [named]
        iframe HmuR HrevMuR HtiR
        iframe #
    · rw [decide_eq_false h0]
      wp_auto
      have hsy : synced = false := by simp only [synced, decide_eq_false hs, decide_eq_false h0, Bool.or_false]
      have hlo' : lo = sint.nat startRev := by simp only [lo, hsy]; rfl
      obtain ⟨hST, hWo, hl, hWs, hWu, hv, hE⟩ := Hok.fresh hM
      wp_apply HgsI
      (try wp_auto)
      wp_apply hAdd $$ [$Hunsynced] as Hunsynced
      · iframe Hfixed; ipureintro; exact ⟨hWu, by have := Hok.wu_size; omega⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ] as HrevMuR
      · inext
        iunfold mvcc.revMuInv
        iexists C, ntok
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨HneQ, HbudgetQ⟩
      (try wp_auto)
      -- the lock invariant with the new unsynced watcher
      ihave %Hchnn : ⌜ch ≠ null⌝ $$ []
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, -⟩
        iapply mvcc.isChan_ne_null $$ Hic
      ihave #Hfo := mvcc.filtersOk_of fcs fs $$ [$Hfcs $Hfs]
      let st0 : mvcc.WatcherSt := ⟨startRev, false, false, false, ch⟩
      imod mvcc.watch_close_body s γ σ false w r fcs st0 γw C Hok hM
          ⟨rfl, rfl, rfl, Hchnn⟩
          (by show ((γw.lo : Nat) : Int) = sint.Z startRev
              rw [hlo, hlo', show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega)
          (by show sint.Z startRev ≤ ((γw.lo : Nat) : Int)
              rw [hlo, hlo', show sint.nat startRev = (sint.Z startRev).toNat from rfl]; omega)
          (fun h => by cases h) (fun _ => by show sint.Z startRev < _; omega)
        $$ [Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst minRev victim compacted restore ch
          Hwo Hmeta Hwt Hmem He Hl]
        with Hbody
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hσ Hwlog Hunsynced Hsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem He Hl
        iframe #
        iunfold mvcc.watcherOwn
        iframe minRev victim compacted restore ch
        ipureintro; exact Hvlen
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
      · inext
        iunfold mvcc.watchStoreInv
        iexists _
        iexact Hbody
      (try wp_auto)
      ipersist wa
      ipersist s
      wp_apply HgwI
      (try wp_auto)
      simp only [recv_eq_func_mk]
      iapply HΦ
      isplitr
      · ipureintro; exact Hwnn
      isplitr
      · iexists γw, r, fcs
        iframe Hmw Hfixed
        ipureintro; exact Hsr
      isplitr
      · iunfold mvcc.cancelSpec
        imodintro
        imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply (hCancel s st γ w) $$ [] as HWC
        · iframe #
          simp only [mvcc.storeWatchParams]
          iexists γw, r, fcs
          iframe Hmw Hfixed
          ipureintro; exact Hsr
        (try wp_auto)
        iapply HΦ'
        simp only [mvcc.storeWatchParams] at *
        iexact HWC
      isplitl [HCR]
      · iunfold mvcc.watcherChan at Hwc
        icases Hwc with ⟨Hic, Hinv, -⟩
        iexists γw.wc
        iframe Hic Hinv HCR
      iunfold mvcc.watchReader
      iframe Hmur
      iunfold mvcc.storeReader
      iexists ti
      simp only [named]
      iframe HmuR HrevMuR HtiR
      iframe #

end proof

end EtcdGrove
end Perennial
