/-
Proof of `Spec/.../mvcc/watchableStore__cancelWatcher.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__cancelWatcher
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

/-! ## The state after a cancel (pure) -/

/-- The state with the live watcher `wa` (state `st`) cancelled: out of its population (the new
groups and victim batches given), its events dropped, its channel `nil`. -/
def cancelState (σ : WsState) (wa : Loc) (st : WatcherSt) (Ws Wu : GMap Loc WatchRange)
    (VB : List (GMap Loc EventBatch)) : WsState :=
  { σ with Ws := Ws, Wu := Wu, VB := VB, E := GMap.delete wa σ.E,
           ST := <[wa := { st with ch := null }]> σ.ST }

theorem lookup_delete' {V : Type} (m : GMap Loc V) (k w : Loc) :
    GMap.delete k m !! w = if w = k then none else m !! w := by
  by_cases h : w = k
  · subst h; simp [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ (Ne.symm h)]; simp [h]

theorem lookup_insert' {V : Type} (m : GMap Loc V) (k w : Loc) (v : V) :
    (<[k := v]> m) !! w = if w = k then some v else m !! w := by
  by_cases h : w = k
  · subst h; simp [GMap.lookup_insert]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h]

theorem delete_none {V : Type} (m : GMap Loc V) (k : Loc) (h : m !! k = none) :
    GMap.delete k m = m :=
  GMap.map_eq fun w => by rw [lookup_delete']; split <;> simp_all

theorem zip_set_right {α β : Type} : ∀ (l1 : List α) (l2 : List β) (n : Nat) (a : α) (b : β),
    l1[n]? = some a → (l1.zip l2).set n (a, b) = l1.zip (l2.set n b)
  | [], _, n, a, b, h => by simp at h
  | _ :: _, [], n, a, b, _ => by simp
  | x :: l1, y :: l2, 0, a, b, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp
  | x :: l1, y :: l2, n + 1, a, b, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.zip_cons_cons, List.set_cons_succ]
    rw [zip_set_right l1 l2 n a b h]

theorem findSome?_none_of {α β : Type} (g : α → Option β) (l : List α)
    (h : ∀ (j : Nat) (x : α), l[j]? = some x → g x = none) : l.findSome? g = none := by
  rw [List.findSome?_eq_none_iff]
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  exact h j x hj

theorem findSome?_isSome_of {α β : Type} (g : α → Option β) (l : List α) (n : Nat) (x : α)
    (hn : l[n]? = some x) (hx : (g x).isSome) : (l.findSome? g).isSome := by
  cases h : l.findSome? g with
  | some _ => rfl
  | none =>
    rw [List.findSome?_eq_none_iff] at h
    rw [h x (List.mem_of_getElem? hn)] at hx
    cases hx

theorem findSome?_set_eq {α β : Type} (g : α → Option β) : ∀ (l : List α) (k : Nat) (x x' : α),
    l[k]? = some x → g x' = g x → (l.set k x').findSome? g = l.findSome? g
  | [], k, x, x', h, _ => by simp at h
  | y :: l, 0, x, x', h, hg => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.set_cons_zero, List.findSome?_cons, hg]
  | y :: l, k + 1, x, x', h, hg => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.findSome?_cons]
    rw [findSome?_set_eq g l k x x' h hg]

theorem vb_delete (σ : WsState) (hok : WsOk σ) (k : Nat) (B : GMap Loc EventBatch) (wa : Loc)
    (hk : σ.VB[k]? = some B) (hwa : (B !! wa).isSome) :
    (∀ w, (σ.VB.set k (GMap.delete wa B)).findSome? (· !! w) =
      if w = wa then none else σ.victimOf w) ∧
    (∀ (i j : Nat) (B1 B2 : GMap Loc EventBatch) (w : Loc),
      (σ.VB.set k (GMap.delete wa B))[i]? = some B1 →
      (σ.VB.set k (GMap.delete wa B))[j]? = some B2 → (B1 !! w).isSome → (B2 !! w).isSome →
      i = j) := by
  have hget : ∀ i B1 w, (σ.VB.set k (GMap.delete wa B))[i]? = some B1 → (B1 !! w).isSome →
      ∃ B0, σ.VB[i]? = some B0 ∧ (B0 !! w).isSome ∧ (i = k → w ≠ wa) := by
    intro i B1 w h hw
    rw [List.getElem?_set] at h
    by_cases hik : k = i
    · subst hik
      simp only [ite_true] at h
      have hlt : k < σ.VB.length := (List.getElem?_eq_some_iff.1 hk).1
      simp only [hlt, ite_true, Option.some.injEq] at h
      subst h
      rw [lookup_delete'] at hw
      by_cases hww : w = wa
      · simp [hww] at hw
      · rw [if_neg hww] at hw
        exact ⟨B, hk, hw, fun _ => hww⟩
    · rw [if_neg hik] at h
      exact ⟨B1, h, hw, fun e => absurd e.symm hik⟩
  refine ⟨fun w => ?_, ?_⟩
  · by_cases hw : w = wa
    · subst hw
      rw [if_pos rfl]
      apply findSome?_none_of
      intro j x hj
      cases hx : x !! w with
      | none => rfl
      | some _ =>
        obtain ⟨B0, hB0, hB0w, hne⟩ := hget j x w hj (by rw [hx]; rfl)
        have := hok.v_one j k B0 B w hB0 hk hB0w hwa
        exact absurd rfl (hne this)
    · rw [if_neg hw]
      unfold WsState.victimOf
      exact findSome?_set_eq _ σ.VB k B _ hk (lookup_delete' B wa w ▸ by simp [hw])
  · intro i j B1 B2 w h1 h2 hw1 hw2
    obtain ⟨B1o, h1o, hw1o, -⟩ := hget i B1 w h1 hw1
    obtain ⟨B2o, h2o, hw2o, -⟩ := hget j B2 w h2 hw2
    exact hok.v_one i j B1o B2o w h1o h2o hw1o hw2o

theorem cancelState_ok (σ : WsState) (hok : WsOk σ) (wa : Loc) (st : WatcherSt)
    (hst : σ.ST !! wa = some st) (hlive : σ.live wa) (Ws Wu : GMap Loc WatchRange)
    (VB : List (GMap Loc EventBatch))
    (hWs : ∀ w, Ws !! w = if w = wa then none else σ.Ws !! w)
    (hWu : ∀ w, Wu !! w = if w = wa then none else σ.Wu !! w)
    (hV : ∀ w, VB.findSome? (· !! w) = if w = wa then none else σ.victimOf w)
    (hone : ∀ (i j : Nat) (B B' : GMap Loc EventBatch) (w : Loc), VB[i]? = some B →
      VB[j]? = some B' → (B !! w).isSome → (B' !! w).isSome → i = j) :
    WsOk (cancelState σ wa st Ws Wu VB) := by
  have hv' : ∀ w, (cancelState σ wa st Ws Wu VB).victimOf w =
      if w = wa then none else σ.victimOf w := hV
  have hlv : ∀ w, (cancelState σ wa st Ws Wu VB).live w ↔ (w ≠ wa ∧ σ.live w) := by
    intro w
    unfold WsState.live
    show ((Ws !! w).isSome ∨ (Wu !! w).isSome ∨ (VB.findSome? (· !! w)).isSome) ↔ _
    rw [hWs, hWu, hV]
    by_cases h : w = wa <;> simp [h, WsState.live]
  have hstn : ∀ w, (cancelState σ wa st Ws Wu VB).ST !! w =
      if w = wa then some { st with ch := null } else σ.ST !! w := fun w => lookup_insert' _ _ _ _
  have hE : ∀ w, (cancelState σ wa st Ws Wu VB).E !! w = if w = wa then none else σ.E !! w :=
    fun w => lookup_delete' _ _ _
  obtain ⟨ws_wu, ws_v, wu_v, _, live_st, live_e, st_m, wo_m, m_st, wo_st, wo_live, st_flags,
    wo_flags, synced_d⟩ := hok
  have hwa_m : (σ.M !! wa).isSome := st_m wa (by rw [hst]; rfl)
  refine ⟨?_, ?_, ?_, hone, ?_, ?_, ?_, wo_m, ?_, ?_, ?_, ?_, wo_flags, ?_⟩
  · intro w h
    show Wu !! w = none
    have h' : (Ws !! w).isSome := h
    rw [hWs] at h'; rw [hWu]
    split at h'
    · simp at h'
    · rw [if_neg (by assumption)]; exact ws_wu w h'
  · intro w h
    have h' : (Ws !! w).isSome := h
    rw [hWs] at h'; rw [hv']
    split at h'
    · simp at h'
    · rw [if_neg (by assumption)]; exact ws_v w h'
  · intro w h
    have h' : (Wu !! w).isSome := h
    rw [hWu] at h'; rw [hv']
    split at h'
    · simp at h'
    · rw [if_neg (by assumption)]; exact wu_v w h'
  · intro w h
    rw [hlv] at h
    rw [hstn, if_neg h.1]; exact live_st w h.2
  · intro w
    rw [hE, hlv]
    by_cases h : w = wa
    · simp [h]
    · rw [if_neg h, live_e]; simp [h]
  · intro w h
    rw [hstn] at h
    show (σ.M !! w).isSome
    split at h
    · subst w; exact hwa_m
    · exact st_m w h
  · intro w h
    rcases m_st w h with h1 | h1
    · left; rw [hstn]; split
      · rfl
      · exact h1
    · right; exact h1
  · intro w h
    rw [hstn]
    have := wo_st w h
    have hne : w ≠ wa := by intro e; subst e; rw [hst] at this; cases this
    rw [if_neg hne]; exact this
  · intro w h
    rw [hlv]
    exact fun h' => wo_live w h h'.2
  · intro w st' h
    rw [hstn] at h
    split at h
    · rename_i e
      subst e
      cases h
      obtain ⟨h1, h2, -, -⟩ := st_flags w st hst
      refine ⟨h1, h2, fun h' => absurd rfl ((hlv w).1 h').1, ?_⟩
      simp [hlv]
    · rename_i hne
      obtain ⟨h1, h2, h3, h4⟩ := st_flags w st' h
      refine ⟨h1, h2, ?_, ?_⟩
      · intro hl
        rw [hv', if_neg hne]
        exact h3 ((hlv w).1 hl).2
      · rw [h4, hlv]; simp [hne]
  · intro w γw ed hw hm he
    have hw' : (Ws !! w).isSome := hw
    rw [hWs] at hw'
    rw [hE] at he
    split at hw'
    · simp at hw'
    · rw [if_neg (by assumption)] at he
      exact synced_d w γw ed hw' hm he

end mvcc

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

namespace mvcc

theorem memberRes_live_elim (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt)
    (h : σ.live w) :
    memberRes (GF := GF) γ q σ w st ⊢ ∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
      (evsw : List EvM) (d : Nat),
      ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      watcherChan γ w γw st.ch ∗ ⌜σ.E !! w = some (evsw, d)⌝ ∗
      monoListAuthOwn γw.evs q.half evsw ∗ dghostVar γw.live (DFrac.own q.half) true := by
  unfold memberRes
  simp only [h, ↓reduceIte]
  iintro ⟨%γw, %r, %fcs, %hm, #Hm, #Hf, #Hc, -, -, %evsw, %d, %he, Hev, Hl, -⟩
  iexists γw, r, fcs, evsw, d
  iframe Hev Hl
  iframe #
  ipureintro; exact ⟨hm, he⟩

theorem memberRes_dead_elim (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt)
    (h : ¬ σ.live w) :
    memberRes (GF := GF) γ q σ w st ⊢ ∃ γw : WatcherNames, watcherMeta γ w γw ∗ cancelled γw := by
  unfold memberRes
  simp only [h, ↓reduceIte]
  iintro ⟨%γw, %r, %fcs, %hm, #Hm, #Hf, #Hc⟩
  iexists γw
  iframe #

theorem memberRes_cancel_intro (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt)
    (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (h : ¬ σ.live w)
    (hm : σ.M !! w = some γw) :
    watcherMeta (GF := GF) γ w γw ∗ watcherFixed w r fcs ∗ cancelled γw ⊢ memberRes γ q σ w st := by
  unfold memberRes
  simp only [h, ↓reduceIte]
  iintro ⟨#Hm, #Hf, #Hc⟩
  iexists γw, r, fcs
  iframe #
  ipureintro; exact hm

theorem memberRes_congr (γ : WsNames) (q : Qp) (σ σ' : WsState) (w : Loc) (st : WatcherSt)
    (hM : σ'.M = σ.M) (hWs : (σ'.Ws !! w).isSome = (σ.Ws !! w).isSome)
    (hWu : (σ'.Wu !! w).isSome = (σ.Wu !! w).isSome) (hV : σ'.victimOf w = σ.victimOf w)
    (hE : σ'.E !! w = σ.E !! w) :
    memberRes (GF := GF) γ q σ w st ⊢ memberRes γ q σ' w st := by
  have hl : σ'.live w = σ.live w := by unfold WsState.live; rw [hWs, hWu, hV]
  unfold memberRes popFacts
  simp only [hM, hl, hWs, hWu, hV, hE]
  exact .rfl

theorem state_acc (σ : WsState) (wa : Loc) (st0 : WatcherSt) (qf : Qp)
    (h : (σ.ST !! wa = some st0 ∧ qf = 1) ∨ (σ.Wo !! wa = some st0 ∧ qf = (1 : Qp).half)) :
    ([∗map] w ↦ st ∈ σ.ST, watcherOwn (GF := GF) w st) ∗
      ([∗map] w ↦ st ∈ σ.Wo, watcherOwn w st (1 : Qp).half) ⊢
    watcherOwn wa st0 qf ∗ (watcherOwn wa st0 qf -∗
      ([∗map] w ↦ st ∈ σ.ST, watcherOwn w st) ∗
      ([∗map] w ↦ st ∈ σ.Wo, watcherOwn w st (1 : Qp).half)) := by
  iintro ⟨Hst, Hwo⟩
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · icases (BigSepM.bigSepM_lookup_acc (m := σ.ST) h).1 $$ Hst with ⟨Hw, Hb⟩
    iframe Hw
    iintro Hw
    iframe Hwo
    iapply Hb $$ Hw
  · icases (BigSepM.bigSepM_lookup_acc (m := σ.Wo) h).1 $$ Hwo with ⟨Hw, Hb⟩
    iframe Hw
    iintro Hw
    iframe Hst
    iapply Hb $$ Hw

theorem body_cancel (s : Loc) (γ : WsNames) (σ σ' : WsState) (hok : WsOk σ) (wa : Loc)
    (st : WatcherSt) (hst : σ.ST !! wa = some st) (hlive : σ.live wa)
    (Ws Wu : GMap Loc WatchRange) (VB : List (GMap Loc EventBatch))
    (hWs : ∀ w, Ws !! w = if w = wa then none else σ.Ws !! w)
    (hWu : ∀ w, Wu !! w = if w = wa then none else σ.Wu !! w)
    (hV : ∀ w, VB.findSome? (· !! w) = if w = wa then none else σ.victimOf w)
    (hone : ∀ (i j : Nat) (B B' : GMap Loc EventBatch) (w : Loc), VB[i]? = some B →
      VB[j]? = some B' → (B !! w).isSome → (B' !! w).isSome → i = j)
    (hσ' : σ' = cancelState σ wa st Ws Wu VB)
    (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (hm : σ.M !! wa = some γw) :
    ghostVar (GF := GF) γ.wst 1 σ' ∗ ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗ idxCert γ.st.idx σ.Lmu ∗
      ownWatcherGroup (syncedAddr s) Ws ∗ ownWatcherGroup (unsyncedAddr s) Wu ∗
      typedPointsto (victimsAddr s) σ.vs (DFrac.own 1) ∗ ownSlice σ.vs σ.vbs (DFrac.own 1) ∗
      ownSliceCap GoMap σ.vs (DFrac.own 1) ∗ ⌜σ.vbs.length = VB.length⌝ ∗
      ([∗list] x ∈ σ.vbs.zip VB, ownWatcherBatch x.1 x.2) ∗
      ([∗map] w ↦ st ∈ GMap.delete wa σ.ST, watcherOwn w st) ∗
      watcherOwn wa { st with ch := null } ∗
      ([∗map] w ↦ st ∈ σ.Wo, watcherOwn w st (1 : Qp).half) ∗ ghostMapAuth γ.wmeta 1 σ.M ∗
      ([∗map] w ↦ _γw ∈ σ.M, ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs) ∗
      ([∗map] w ↦ st ∈ GMap.delete wa σ.ST, memberRes γ 1 σ w st) ∗
      watcherMeta γ wa γw ∗ watcherFixed wa r fcs ∗ cancelled γw ∗
      ([∗map] w ↦ st ∈ σ.Wo, outRes γ σ w st) ⊢
    watchStoreBody s γ 1 σ' := by
  have hok' : WsOk σ' := hσ' ▸ cancelState_ok σ hok wa st hst hlive Ws Wu VB hWs hWu hV hone
  have hlv' : ¬ σ'.live wa := by
    rw [hσ']; unfold WsState.live
    show ¬ ((Ws !! wa).isSome ∨ (Wu !! wa).isSome ∨ (VB.findSome? (· !! wa)).isSome)
    rw [hWs, hWu, hV]; simp
  have hM : σ'.M = σ.M := by rw [hσ']; rfl
  have hL : σ'.Lmu = σ.Lmu := by rw [hσ']; rfl
  have hWs' : σ'.Ws = Ws := by rw [hσ']; rfl
  have hWu' : σ'.Wu = Wu := by rw [hσ']; rfl
  have hvs : σ'.vs = σ.vs := by rw [hσ']; rfl
  have hvbs : σ'.vbs = σ.vbs := by rw [hσ']; rfl
  have hVB : σ'.VB = VB := by rw [hσ']; rfl
  have hST : σ'.ST = <[wa := { st with ch := null }]> σ.ST := by rw [hσ']; rfl
  have hWo : σ'.Wo = σ.Wo := by rw [hσ']; rfl
  iintro ⟨Hσ, Hwlog, #Hcert, Hsynced, Hunsynced, Hvf, Hvs, Hvcap, %Hvlen, Hvbs, Hst, Hwa, Hwo,
    Hmeta, #Hmfix, Hmem, #Hm, #Hf, #Hc, #Hout⟩
  unfold watchStoreBody
  rw [hL, hWs', hWu', hvs, hvbs, hVB, hST, hWo, hM]
  simp only [named]
  iframe Hσ Hwlog Hcert Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hwo Hmeta Hmfix
  isplitr
  · ipureintro; exact Hvlen
  isplitl [Hst Hwa]
  · iapply (BigSepM.bigSepM_insert_delete (m := σ.ST) (i := wa) (x := { st with ch := null })).2
    iframe Hwa Hst
  isplitl [Hmem]
  · iapply (BigSepM.bigSepM_insert_delete (m := σ.ST) (i := wa) (x := { st with ch := null })).2
    isplitr
    · iapply memberRes_cancel_intro γ 1 σ' wa _ γw r fcs hlv' (by rw [hM]; exact hm)
      iframe #
    iapply (BigSepM.bigSepM_mono (fun {k v} hk => ?_)) $$ Hmem
    have hk' : k ≠ wa := by
      intro e; subst e
      have : (GMap.delete k σ.ST) !! k = some v := hk
      rw [GMap.lookup_delete] at this; cases this
    apply memberRes_congr γ 1 σ σ' k v hM
    · rw [hWs', hWs, if_neg hk']
    · rw [hWu', hWu, if_neg hk']
    · show σ'.VB.findSome? (· !! k) = _
      rw [hVB, hV, if_neg hk']
    · rw [hσ']
      show GMap.delete wa σ.E !! k = _
      rw [GMap.lookup_delete_ne _ (Ne.symm hk')]
  isplitr
  · iapply (BigSepM.bigSepM_mono (fun {k v} _ => ?_)) $$ Hout
    unfold outRes; rw [hM]
  ipureintro; exact hok'

end mvcc

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Cancelling a live watcher's ghost** (a ghost step, one later credit): the lock's half of
its live ghost and its channel entry's half, set to `false` for good. -/
theorem mvcc.cancel_ghost (γ : mvcc.WsNames) (wa : Loc) (γw : mvcc.WatcherNames) (ch : Loc) :
    ⊢ £ 1 -∗ mvcc.watcherMeta γ wa γw -∗ mvcc.watcherChan γ wa γw ch -∗
      dghostVar γw.live (DFrac.own (1 : Qp).half) true ={⊤}=∗ mvcc.cancelled γw := by
  iintro Hlc #Hm #Hc Hlive
  iunfold mvcc.watcherChan at Hc
  icases Hc with ⟨#Hisch, #Hinv, #Hreg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iunfold mvcc.watchChanInv at Hi
  icases Hi with ⟨%cs, %sent, %recv, %vs, %L, Hi⟩
  iNamed Hi
  ihave %Hlk := ghost_map_lookup $$ Hreg Hreg
  have hmem : wa ∈ L := (mvcc.regMap_lookup L wa).1 (by rw [Hlk]; rfl)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hws with ⟨He, Hback⟩
  iunfold mvcc.chanWatcher at He
  icases He with ⟨%γw', %r', %fcs', %evsw, %D, %d, #Hm', %Hwc, #Hf', Hevs, %HD, #HDf, #Hwf, Hl⟩
  ihave #Hm0 := Hm
  iunfold mvcc.watcherMeta at Hm0 Hm'
  ihave %Heq := ghostMapElem_agree $$ Hm0 Hm'
  subst Heq
  icases Hl with (⟨%Hcl, Hl⟩ | #Hcan)
  · imod dghostVar_update_halves false _ _ _ $$ Hlive Hl with ⟨H1, -⟩
    imod dghostVar_persist $$ H1 with #Hcan
    ihave Hws := Hback $$ [Hevs]
    · iunfold mvcc.chanWatcher
      iexists γw, r', fcs', evsw, D, d
      isplitr
      · iexact Hm
      isplitr
      · ipureintro; exact Hwc
      isplitr
      · iexact Hf'
      isplitl [Hevs]
      · iexact Hevs
      isplitr
      · ipureintro; exact HD
      isplitr
      · iexact HDf
      isplitr
      · iexact Hwf
      iright
      iunfold mvcc.cancelled
      iexact Hcan
    rw [mvcc.set_same hi]
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold mvcc.watchChanInv
      iexists cs, sent, recv, vs, L
      simp only [named]
      iframe Hch Hrecv Hregl Hcl Hreg Hws
      iframe #
      ipureintro; exact ⟨Hpre, Hinfl, Hnd⟩
    imodintro
    iunfold mvcc.cancelled
    iexact Hcan
  · iunfold mvcc.cancelled at Hcan
    ihave %Hbad := dghostVar_agree $$ Hlive Hcan
    cases Hbad

theorem mvcc.watchableStore.cancelWatcher.wp_proof
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.cancelWatcher.spec (GF := GF) (hG := hG) := by
  intro s st γ wa
  wp_start as ⟨#Hws, #HIW⟩
  simp only [mvcc.storeWatchParams]
  icases HIW with ⟨%γw, %r, %fcs, #HmW, #Hfix, %Hsr⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%wg, #Hwg, #HwgS⟩,
    ⟨%sg, #Hsg, #HsgS⟩, -⟩
  iunfold gaugeSpec at HwgS HsgS
  icases HwgS with ⟨-, #HwgDec, -⟩
  icases HsgS with ⟨-, #HsgDec, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hws0 := Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  wp_auto
  wp_for
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  iNamed HP
  wp_apply hDel $$ [$Hunsynced $Hfix] as Hunsynced
  cases hwu : σ.Wu !! wa with
  | some ru =>
    simp only [Option.isSome_some]
    wp_auto_lc 1
    wp_apply HsgDec
    wp_apply HwgDec
    wp_for_post
    have hlive : σ.live wa := Or.inr (Or.inl (by rw [hwu]; rfl))
    obtain ⟨st0, hst⟩ : ∃ st0, σ.ST !! wa = some st0 :=
      Option.isSome_iff_exists.1 (Hok.live_st wa hlive)
    icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hst with ⟨Hwa, Hst⟩
    icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hmem with ⟨Hmwa, Hmem⟩
    icases mvcc.memberRes_live_elim γ 1 σ wa st0 hlive $$ Hmwa with
      ⟨%γw', %r', %fcs', %evsw, %d, %hm, #Hm', #Hf', #Hch, %he, -, Hlive⟩
    ihave #HmW0 := HmW
    ihave #Hm0 := Hm'
    iunfold mvcc.watcherMeta at HmW0 Hm0
    ihave %Heq := ghostMapElem_agree $$ HmW0 Hm0
    subst Heq
    imod mvcc.cancel_ghost γ wa γw st0.ch $$ Hlc1 HmW Hch Hlive with #Hcan
    iunfold mvcc.watcherOwn at Hwa
    icases Hwa with ⟨Hmin, Hvic, Hcomp, Hres, Hchf⟩
    wp_auto
    have hWs0 : σ.Ws !! wa = none := by
      cases h : σ.Ws !! wa with
      | none => rfl
      | some _ => have := Hok.ws_wu wa (by rw [h]; rfl); rw [hwu] at this; cases this
    have hv0 : σ.victimOf wa = none := Hok.wu_v wa (by rw [hwu]; rfl)
    imod ghostVar_update (mvcc.cancelState σ wa st0 σ.Ws (GMap.delete wa σ.Wu) σ.VB) γ.wst σ
      $$ Hσ with Hσ
    ihave HP : mvcc.watchStoreInv s γ 1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem Hmin Hvic Hcomp Hres Hchf]
    · iunfold mvcc.watchStoreInv
      iexists _
      iapply mvcc.body_cancel s γ σ _ Hok wa st0 hst hlive σ.Ws (GMap.delete wa σ.Wu) σ.VB
        (fun w => by by_cases h : w = wa <;> simp [h, hWs0])
        (fun w => mvcc.lookup_delete' _ _ _)
        (fun w => by
          by_cases h : w = wa
          · subst h; simp only [ite_true]; exact hv0
          · simp only [h, ite_false]; rfl)
        Hok.v_one rfl γw r' fcs' hm
      iframe Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem
      iframe #
      isplitr
      · ipureintro; exact Hvlen
      iunfold mvcc.watcherOwn
      iframe
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
    iapply HΦ
    iexists γw
    iframe #
  | none =>
    simp only [Option.isSome_none]
    rw [mvcc.delete_none _ _ hwu]
    wp_auto
    wp_apply hDel $$ [$Hsynced $Hfix] as Hsynced
    cases hws : σ.Ws !! wa with
    | some rs =>
      simp only [Option.isSome_some]
      wp_auto_lc 1
      wp_apply HwgDec
      wp_for_post
      have hlive : σ.live wa := Or.inl (by rw [hws]; rfl)
      obtain ⟨st0, hst⟩ : ∃ st0, σ.ST !! wa = some st0 :=
        Option.isSome_iff_exists.1 (Hok.live_st wa hlive)
      icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hst with ⟨Hwa, Hst⟩
      icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hmem with ⟨Hmwa, Hmem⟩
      icases mvcc.memberRes_live_elim γ 1 σ wa st0 hlive $$ Hmwa with
        ⟨%γw', %r', %fcs', %evsw, %d, %hm, #Hm', #Hf', #Hch, %he, -, Hlive⟩
      ihave #HmW0 := HmW
      ihave #Hm0 := Hm'
      iunfold mvcc.watcherMeta at HmW0 Hm0
      ihave %Heq := ghostMapElem_agree $$ HmW0 Hm0
      subst Heq
      imod mvcc.cancel_ghost γ wa γw st0.ch $$ Hlc1 HmW Hch Hlive with #Hcan
      iunfold mvcc.watcherOwn at Hwa
      icases Hwa with ⟨Hmin, Hvic, Hcomp, Hres, Hchf⟩
      wp_auto
      have hv0 : σ.victimOf wa = none := Hok.ws_v wa (by rw [hws]; rfl)
      imod ghostVar_update (mvcc.cancelState σ wa st0 (GMap.delete wa σ.Ws) σ.Wu σ.VB) γ.wst σ
        $$ Hσ with Hσ
      ihave HP : mvcc.watchStoreInv s γ 1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem Hmin Hvic Hcomp Hres Hchf]
      · iunfold mvcc.watchStoreInv
        iexists _
        iapply mvcc.body_cancel s γ σ _ Hok wa st0 hst hlive (GMap.delete wa σ.Ws) σ.Wu σ.VB
          (fun w => mvcc.lookup_delete' _ _ _)
          (fun w => by by_cases h : w = wa <;> simp [h, hwu])
          (fun w => by
            by_cases h : w = wa
            · subst h; simp only [ite_true]; exact hv0
            · simp only [h, ite_false]; rfl)
          Hok.v_one rfl γw r' fcs' hm
        iframe Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem
        iframe #
        isplitr
        · ipureintro; exact Hvlen
        iunfold mvcc.watcherOwn
        iframe
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
      iapply HΦ
      iexists γw
      iframe #
    | none =>
      simp only [Option.isSome_none]
      rw [mvcc.delete_none _ _ hws]
      ihave #HmW0 := HmW
      iunfold mvcc.watcherMeta at HmW0
      ihave %HmM := ghost_map_lookup $$ Hmeta HmW0
      have hnl : ¬ σ.live wa → σ.victimOf wa = none := by
        intro h; unfold WsState.live at h; rw [hws, hwu] at h; simpa using h
      obtain ⟨st0, qf, hsrc⟩ : ∃ st0 qf, (σ.ST !! wa = some st0 ∧ qf = 1) ∨
          (σ.Wo !! wa = some st0 ∧ qf = (1 : Qp).half) := by
        rcases Hok.m_st wa (by rw [HmM]; rfl) with h | h
        · obtain ⟨st0, h⟩ := Option.isSome_iff_exists.1 h; exact ⟨st0, 1, Or.inl ⟨h, rfl⟩⟩
        · obtain ⟨st0, h⟩ := Option.isSome_iff_exists.1 h
          exact ⟨st0, (1 : Qp).half, Or.inr ⟨h, rfl⟩⟩
      have hcomp : st0.compacted = false := by
        rcases hsrc with ⟨h, -⟩ | ⟨h, -⟩
        · exact (Hok.st_flags wa st0 h).1
        · exact (Hok.wo_flags wa st0 h).1
      icases mvcc.state_acc σ wa st0 qf hsrc $$ [$Hst $Hwo] with ⟨Hwa, Hback⟩
      iunfold mvcc.watcherOwn at Hwa
      icases Hwa with ⟨Hmin, Hvic, Hcomp, Hres, Hchf⟩
      wp_auto
      wp_if_destruct
      · -- already cancelled
        have hST : σ.ST !! wa = some st0 ∧ qf = 1 := by
          rcases hsrc with h | ⟨h, -⟩
          · exact h
          · exact absurd Hif (Hok.wo_flags wa st0 h).2.2.2
        obtain ⟨hst, rfl⟩ := hST
        have hnl : ¬ σ.live wa := (Hok.st_flags wa st0 hst).2.2.2.1 Hif
        icases (BigSepM.bigSepM_lookup_acc (m := σ.ST) hst).1 $$ Hmem with ⟨Hmwa, Hmback⟩
        ihave #Hdead := mvcc.memberRes_dead_elim γ 1 σ wa st0 hnl $$ Hmwa
        ihave Hmem := Hmback $$ [Hmwa]
        · iexact Hmwa
        wp_for_post
        ihave Hown := Hback $$ [Hmin Hvic Hcomp Hres Hchf]
        · iunfold mvcc.watcherOwn
          rw [Hif]
          iframe
        icases Hown with ⟨Hst, Hwo⟩
        ihave HP : mvcc.watchStoreInv s γ 1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem]
        · iunfold mvcc.watchStoreInv
          iexists σ
          iunfold mvcc.watchStoreBody
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hvlen, Hok⟩
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
        iapply HΦ
        iexact Hdead
      rw [hcomp]
      wp_auto
      have hvic : st0.victim = true := by
        rcases hsrc with ⟨h, -⟩ | ⟨h, -⟩
        · have hl : σ.live wa := Classical.byContradiction fun hn =>
            Hif ((Hok.st_flags wa st0 h).2.2.2.2 hn)
          refine ((Hok.st_flags wa st0 h).2.2.1 hl).2 ?_
          unfold WsState.live at hl
          rw [hws, hwu] at hl
          simpa using hl
        · exact (Hok.wo_flags wa st0 h).2.2.1
      rw [hvic]
      wp_auto
      ihave Hown := Hback $$ [Hmin Hvic Hcomp Hres Hchf]
      · iunfold mvcc.watcherOwn
        rw [hvic, hcomp]
        iframe
      icases Hown with ⟨Hst, Hwo⟩
      ihave %Hvsl := ownSlice_len $$ Hvs
      ihave IH2 : iprop(∃ (n : w64) (wbv : GoMap),
          "i" ∷ i_ptr ↦ n ∗ "wb" ∷ wb_ptr ↦ wbv ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (σ.vbs.length : Int) ∧
            ∀ j B, j < sint.nat n → σ.VB[j]? = some B → B !! wa = none⌝) $$ [i wb]
      · iexists W64 0, _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, fun j B hj _ => ?_⟩
        exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
      wp_for IH2
      wp_if_destruct
      · have Hlt : sint.nat n < σ.vbs.length := by word
        obtain ⟨wbv', Hwb⟩ : ∃ x, σ.vbs[sint.nat n]? = some x :=
          ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨B, HB⟩ : ∃ B, σ.VB[sint.nat n]? = some B :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hvlen]; exact Hlt)⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z σ.vs.len := ⟨Hn.1, by word⟩
        rw [ite_eq_left Hbnd]
        icases ownSlice_elem_acc (sint.Z n) wbv' σ.vs (DFrac.own 1) σ.vbs Hn.1 Hwb $$ Hvs
          with ⟨Hel, Hvsback⟩
        wp_auto
        ihave Hvs := Hvsback $$ %wbv' Hel
        rw [mvcc.set_same Hwb]
        have Hz : (σ.vbs.zip σ.VB)[sint.nat n]? = some (wbv', B) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨Hwb, HB⟩
        icases (BigSepL.bigSepL_lookup_acc Hz).1 $$ Hvbs with ⟨Hwbo, Hvbsback⟩
        iunfold mvcc.ownWatcherBatch at Hwbo
        icases Hwbo with ⟨%PB, Hm, %HBm, Hbs⟩
        wp_apply wp_map_lookup1 $$ Hm as Hm
        cases hp : PB !! wa with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          rw [show (zero_val Loc) = null from rfl, _root_.decide_eq_true rfl]
          wp_auto
          wp_for_post
          ihave Hvbs := Hvbsback $$ %(wbv', B) [Hm Hbs]
          · iunfold mvcc.ownWatcherBatch
            iexists PB
            iframe Hm Hbs
            ipureintro; exact HBm
          rw [mvcc.set_same Hz]
          iframe
          iexists n + W64 1, wbv'
          simp only [named]
          iframe
          ipureintro
          refine ⟨by word, by word, fun j B' hj hB' => ?_⟩
          by_cases hjn : j < sint.nat n
          · exact Hn.2.2 j B' hjn hB'
          · have : j = sint.nat n := by
              have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
              omega
            subst this
            rw [HB] at hB'; cases hB'
            have HBm' : B = GMap.fmap Prod.snd PB := HBm
            rw [HBm', GMap.lookup_fmap, hp]; rfl
        | some pe =>
          obtain ⟨p0, eb0⟩ := pe
          icases (BigSepM.bigSepM_lookup_acc (m := PB) hp).1 $$ Hbs with ⟨⟨%Hp0, Heb⟩, Hbsback⟩
          simp only [Option.map_some, Option.getD_some]
          rw [_root_.decide_eq_false Hp0]
          wp_auto
          wp_for_post
          ihave %Hwbnn := ownMap_not_nil $$ Hm
          rw [_root_.decide_eq_false Hwbnn]
          wp_auto_lc 1
          wp_apply HsgDec
          wp_apply HwgDec
          rw [go.delete_underlying, go.is_underlying (t := watcherBatch.ty)]
          wp_apply wp_mapDelete $$ Hm as Hm
          wp_for_post
          -- the victim: cancelled out of its batch
          have HBm' : B = GMap.fmap Prod.snd PB := HBm
          have hBwa : B !! wa = some eb0 := by rw [HBm', GMap.lookup_fmap, hp]; rfl
          have hlive : σ.live wa := Or.inr (Or.inr
            (mvcc.findSome?_isSome_of _ σ.VB (sint.nat n) B HB (by rw [hBwa]; rfl)))
          obtain ⟨hV, hone⟩ := mvcc.vb_delete σ Hok (sint.nat n) B wa HB (by rw [hBwa]; rfl)
          obtain ⟨st1, hst⟩ : ∃ st1, σ.ST !! wa = some st1 :=
            Option.isSome_iff_exists.1 (Hok.live_st wa hlive)
          icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hst with ⟨Hwa, Hst⟩
          icases (BigSepM.bigSepM_delete (m := σ.ST) hst).1 $$ Hmem with ⟨Hmwa, Hmem⟩
          icases mvcc.memberRes_live_elim γ 1 σ wa st1 hlive $$ Hmwa with
            ⟨%γw', %r', %fcs', %evsw, %d, %hm, #Hm', #Hf', #Hch, %he, -, Hlive⟩
          ihave #Hm0 := Hm'
          iunfold mvcc.watcherMeta at Hm0
          ihave %Heq := ghostMapElem_agree $$ HmW0 Hm0
          subst Heq
          imod mvcc.cancel_ghost γ wa γw st1.ch $$ Hlc1 HmW Hch Hlive with #Hcan
          iunfold mvcc.watcherOwn at Hwa
          icases Hwa with ⟨Hmin1, Hvic1, Hcomp1, Hres1, Hchf1⟩
          wp_auto
          ihave Hbs := Hbsback $$ [Heb]
          · iframe Heb; ipureintro; exact Hp0
          icases (BigSepM.bigSepM_delete (m := PB) hp).1 $$ Hbs with ⟨-, Hbs⟩
          ihave Hvbs := Hvbsback $$ %(wbv', GMap.delete wa B) [Hm Hbs]
          · iunfold mvcc.ownWatcherBatch
            iexists GMap.delete wa PB
            rw [GMap.fmap_delete]
            iframe Hm Hbs
            ipureintro; rw [GMap.fmap_delete, ← HBm']
          rw [mvcc.zip_set_right _ _ _ _ _ Hwb]
          imod ghostVar_update (mvcc.cancelState σ wa st1 σ.Ws σ.Wu
            (σ.VB.set (sint.nat n) (GMap.delete wa B))) γ.wst σ $$ Hσ with Hσ
          ihave HP : mvcc.watchStoreInv s γ 1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem Hmin1 Hvic1 Hcomp1 Hres1 Hchf1]
          · iunfold mvcc.watchStoreInv
            iexists _
            iapply mvcc.body_cancel s γ σ _ Hok wa st1 hst hlive σ.Ws σ.Wu
              (σ.VB.set (sint.nat n) (GMap.delete wa B))
              (fun w => by by_cases h : w = wa <;> simp [h, hws])
              (fun w => by by_cases h : w = wa <;> simp [h, hwu])
              hV hone rfl γw r' fcs' hm
            iframe Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem
            iframe #
            isplitr
            · ipureintro; rw [List.length_set]; exact Hvlen
            iunfold mvcc.watcherOwn
            iframe
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
          iapply HΦ
          iexists γw
          iframe #
      · -- not found (the victim is out with the mover): retry
        ihave HP : mvcc.watchStoreInv s γ 1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem]
        · iunfold mvcc.watchStoreInv
          iexists σ
          iunfold mvcc.watchStoreBody
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hvlen, Hok⟩
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
        wp_apply time.wp_Sleep
        wp_for_post
        iframe

end proof

end EtcdGrove
end Perennial
