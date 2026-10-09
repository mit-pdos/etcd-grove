/-
Proof of `Spec/demux__resyncLaggingWatchers.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__resyncLaggingWatchers
public import Spec.go_etcd_io.etcd.cache.v3.watcher__Compact
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__AscendGreaterOrEqual
public import Spec.go_etcd_io.etcd.cache.v3.watcher__enqueueResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## The batches a lagging watcher is resent -/

theorem demuxRLW_split_lt {V : Type} (revOf : V → w64) (p : w64) :
    ∀ (h : List V), RevSorted revOf h →
      (∀ x ∈ h.take (ltCount revOf p h), sint.Z (revOf x) < sint.Z p) ∧
      (∀ x ∈ h.drop (ltCount revOf p h), sint.Z p ≤ sint.Z (revOf x))
  | [], _ => by simp
  | a :: l, hs => by
    unfold RevSorted at hs
    rw [List.pairwise_cons] at hs
    by_cases ha : sint.Z (revOf a) < sint.Z p
    · have h1 : ltCount revOf p (a :: l) = ltCount revOf p l + 1 := by
        unfold ltCount; rw [List.countP_cons]; simp [ha]
      rw [h1, List.take_succ_cons, List.drop_succ_cons]
      obtain ⟨ih1, ih2⟩ := demuxRLW_split_lt revOf p l hs.2
      refine ⟨fun x hx => ?_, ih2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact ih1 x hx
    · have hl : ∀ x ∈ l, ¬ sint.Z (revOf x) < sint.Z p := fun x hx => by
        have := hs.1 x hx; omega
      have h0 : ltCount revOf p (a :: l) = 0 := by
        unfold ltCount; rw [List.countP_eq_zero]
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simpa using ha
        · simpa using hl x hx
      rw [h0, List.take_zero, List.drop_zero]
      refine ⟨fun x hx => by simp at hx, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := hl x hx; omega

/-- From `n ≥ minRev` on, the stream is a prefix below `n` followed by the batches
`AscendGreaterOrEqual(n)` visits. -/
theorem demuxRLW_stream_split {cap : Nat} {c : DemuxCore} (hinv : DemuxInv cap c) {n : w64}
    (hn : ¬ sint.Z n < sint.Z c.minRev) :
    ∃ pre, c.stream = pre ++ ascendGeVisited batchRev n c.history ∧
      (∀ b ∈ pre, sint.Z (batchRev b) < sint.Z n) := by
  obtain ⟨h0, heq⟩ := hinv.hist_suffix
  have hs : RevSorted batchRev c.stream := hinv.stream_ok.sorted
  rw [← heq] at hs
  have hs' := hs
  unfold RevSorted at hs'
  rw [List.pairwise_append] at hs'
  obtain ⟨-, hhs, hcross⟩ := hs'
  obtain ⟨hlt, -⟩ := demuxRLW_split_lt batchRev n c.history hhs
  refine ⟨h0 ++ c.history.take (ltCount batchRev n c.history), ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, heq]
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · by_cases hge : sint.Z (batchRev b) < sint.Z n
      · exact hge
      · exfalso
        have hin : b ∈ c.history :=
          hinv.hist_complete b (heq ▸ List.mem_append_left _ hb) (by omega)
        have := hcross b hb b hin
        omega
    · exact hlt b hb

theorem demuxRLW_vis_ge {c : DemuxCore} {n : w64} (hs : RevSorted batchRev c.history) :
    ∀ b ∈ ascendGeVisited batchRev n c.history, sint.Z n ≤ sint.Z (batchRev b) :=
  (demuxRLW_split_lt batchRev n c.history hs).2

theorem demuxRLW_hist_sorted {cap : Nat} {c : DemuxCore} (hinv : DemuxInv cap c) :
    RevSorted batchRev c.history := by
  obtain ⟨h0, heq⟩ := hinv.hist_suffix
  have hs : RevSorted batchRev c.stream := hinv.stream_ok.sorted
  rw [← heq] at hs
  unfold RevSorted at hs ⊢
  exact (List.pairwise_append.1 hs).2.1

theorem demuxRLW_vis_sorted {c : DemuxCore} {n : w64} (hs : RevSorted batchRev c.history) :
    RevSorted batchRev (ascendGeVisited batchRev n c.history) :=
  List.Pairwise.sublist (List.drop_sublist _ _) hs

theorem demuxRLW_next_ge (n : w64) (vis : List Batch) (hge : ∀ b ∈ vis, sint.Z n ≤ sint.Z (batchRev b))
    (hbd : ∀ b ∈ vis, sint.Z (batchRev b) < 2 ^ 63 - 1) :
    ∀ j, sint.Z n ≤ sint.Z (resyncNext n vis j)
  | 0 => Int.le_refl _
  | j + 1 => by
    cases hb : vis[j]? with
    | none => simp [resyncNext, hb]
    | some b =>
      simp only [resyncNext, hb]
      have h1 := hge b (List.mem_of_getElem? hb)
      have h2 := hbd b (List.mem_of_getElem? hb)
      have : sint.Z (batchRev b + W64 1) = sint.Z (batchRev b) + 1 := by word
      omega

theorem demuxRLW_next_le (n : w64) (vis : List Batch) (hs : RevSorted batchRev vis)
    (hge : ∀ b ∈ vis, sint.Z n ≤ sint.Z (batchRev b))
    (hbd : ∀ b ∈ vis, sint.Z (batchRev b) < 2 ^ 63 - 1) (j : Nat) (b : Batch)
    (hb : vis[j]? = some b) : sint.Z (resyncNext n vis j) ≤ sint.Z (batchRev b) := by
  cases j with
  | zero => exact hge b (List.mem_of_getElem? hb)
  | succ j =>
    have hj : j < vis.length := by
      have := (List.getElem?_eq_some_iff.1 hb).1; omega
    obtain ⟨a, ha⟩ : ∃ a, vis[j]? = some a := ⟨_, List.getElem?_eq_getElem hj⟩
    have hlt := hs.lt ha hb (by omega)
    have h2 := hbd a (List.mem_of_getElem? ha)
    simp only [resyncNext, ha]
    have : sint.Z (batchRev a + W64 1) = sint.Z (batchRev a) + 1 := by word
    omega

theorem demuxRLW_next_succ (n : w64) (vis : List Batch) (j : Nat) (b : Batch)
    (hb : vis[j]? = some b) : resyncNext n vis (j + 1) = batchRev b + W64 1 := by
  simp [resyncNext, hb]

/-- Resending the `j`-th visited batch is sending the stream's range from the next revision
to just past it. -/
theorem demuxRLW_range_one (n : w64) (pre vis : List Batch)
    (hpre : ∀ b ∈ pre, sint.Z (batchRev b) < sint.Z n) (hs : RevSorted batchRev vis)
    (hge : ∀ b ∈ vis, sint.Z n ≤ sint.Z (batchRev b))
    (hbd : ∀ b ∈ vis, sint.Z (batchRev b) < 2 ^ 63 - 1) (j : Nat) (b : Batch)
    (hb : vis[j]? = some b) :
    streamRange (resyncNext n vis j) (batchRev b + W64 1) (pre ++ vis) = [b] := by
  have hlo := demuxRLW_next_ge n vis hge hbd j
  have hhi := demuxRLW_next_le n vis hs hge hbd j b hb
  have hbb := hbd b (List.mem_of_getElem? hb)
  have hsucc : sint.Z (batchRev b + W64 1) = sint.Z (batchRev b) + 1 := by word
  have hj : j < vis.length := (List.getElem?_eq_some_iff.1 hb).1
  have hvis : pre ++ vis = pre ++ (vis.take j ++ b :: vis.drop (j + 1)) := by
    congr 1
    conv => lhs; rw [← List.take_append_drop j vis]
    rw [List.drop_eq_getElem_cons hj, (List.getElem?_eq_some_iff.1 hb).2]
  unfold streamRange
  rw [hvis, List.filter_append, List.filter_append, List.filter_cons]
  have e1 : pre.filter (fun b' => decide (sint.Z (resyncNext n vis j) ≤ sint.Z (batchRev b') ∧
      sint.Z (batchRev b') < sint.Z (batchRev b + W64 1))) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; have := hpre x hx; simp; omega
  have e2 : (vis.take j).filter (fun b' => decide (sint.Z (resyncNext n vis j) ≤ sint.Z (batchRev b') ∧
      sint.Z (batchRev b') < sint.Z (batchRev b + W64 1))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    rw [List.getElem?_take] at hi
    split at hi
    · rename_i hij
      simp only [decide_eq_true_eq, not_and, Int.not_lt]
      intro hle
      exfalso
      cases j with
      | zero => omega
      | succ j' =>
        obtain ⟨a, ha⟩ : ∃ a, vis[j']? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hna : resyncNext n vis (j' + 1) = batchRev a + W64 1 := demuxRLW_next_succ n vis j' a ha
        have h2 := hbd a (List.mem_of_getElem? ha)
        have hsa : sint.Z (batchRev a + W64 1) = sint.Z (batchRev a) + 1 := by word
        rw [hna, hsa] at hle
        rcases Nat.lt_or_ge i j' with h | h
        · have := hs.lt hi ha h; omega
        · have : i = j' := by omega
          subst this; rw [hi] at ha; cases ha; omega
    · simp at hi
  have e3 : (vis.drop (j + 1)).filter (fun b' => decide (sint.Z (resyncNext n vis j) ≤ sint.Z (batchRev b') ∧
      sint.Z (batchRev b') < sint.Z (batchRev b + W64 1))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    rw [List.getElem?_drop] at hi
    have := hs.lt hb hi (by omega)
    simp only [decide_eq_true_eq, not_and, Int.not_lt]
    intro _; omega
  rw [e1, e2, e3]
  have hp : decide (sint.Z (resyncNext n vis j) ≤ sint.Z (batchRev b) ∧
      sint.Z (batchRev b) < sint.Z (batchRev b + W64 1)) = true := by
    simp only [decide_eq_true_eq]; omega
  rw [hp]; rfl

/-- After resending every visited batch, no stream batch is at or above the next revision. -/
theorem demuxRLW_all_below (n : w64) (pre vis : List Batch)
    (hpre : ∀ b ∈ pre, sint.Z (batchRev b) < sint.Z n) (hs : RevSorted batchRev vis)
    (hge : ∀ b ∈ vis, sint.Z n ≤ sint.Z (batchRev b))
    (hbd : ∀ b ∈ vis, sint.Z (batchRev b) < 2 ^ 63 - 1) :
    ∀ b ∈ pre ++ vis, sint.Z (batchRev b) < sint.Z (resyncNext n vis vis.length) := by
  have hlo := demuxRLW_next_ge n vis hge hbd vis.length
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · have := hpre b hb; omega
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    have hil : i < vis.length := (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨L, hL⟩ : ∃ L, vis.length = L + 1 := ⟨vis.length - 1, by omega⟩
    obtain ⟨a, ha⟩ : ∃ a, vis[L]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hL, demuxRLW_next_succ n vis L a ha]
    have h2 := hbd a (List.mem_of_getElem? ha)
    have hsa : sint.Z (batchRev a + W64 1) = sint.Z (batchRev a) + 1 := by word
    rw [hsa]
    rcases Nat.lt_or_ge i L with h | h
    · have := hs.lt hi ha h; omega
    · have : i = L := by omega
      subst this; rw [hi] at ha; cases ha; omega

/-! ## Tracking the outcomes -/

/-- The keys visited so far (`keys.take i`) have views following `ResyncOutcome` from `views`;
the others are unchanged. -/
def demuxRLW_done (c : DemuxCore) (views : GMap Loc View) (keys : List Loc) (i : Nat)
    (views' : GMap Loc View) : Prop :=
  ∀ w v, views !! w = some v →
    if w ∈ keys.take i then ∃ v', views' !! w = some v' ∧ ResyncOutcome c v v'
    else views' !! w = some v

theorem demuxRLW_not_mem_take {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {x : α}
    (hx : l[i]? = some x) : x ∉ l.take i := by
  intro hm
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  rw [hsplit] at h
  have hdrop : x ∈ l.drop i := by
    apply List.mem_of_getElem? (i := 0)
    rw [List.getElem?_drop]; simpa using hx
  exact (List.nodup_append.1 h).2.2 x hm x hdrop rfl

theorem demuxRLW_done_cur {c : DemuxCore} {views views' : GMap Loc View} {keys : List Loc} {i : Nat}
    (hd : demuxRLW_done c views keys i views') (hnd : keys.Nodup) {key : Loc} {v : View}
    (hk : keys[i]? = some key) (hv : views !! key = some v) : views' !! key = some v := by
  have := hd key v hv
  rw [ite_eq_right_of_eq_false _ _ (eq_false (demuxRLW_not_mem_take hnd hk))] at this
  exact this

theorem demuxRLW_done_step {c : DemuxCore} {views views' : GMap Loc View} {keys : List Loc}
    {i : Nat} (hd : demuxRLW_done c views keys i views') {key : Loc} {v v' : View}
    (hk : keys[i]? = some key) (hv : views !! key = some v) (ho : ResyncOutcome c v v') :
    demuxRLW_done c views keys (i + 1) (GMap.insert key v' views') := by
  have htake : keys.take (i + 1) = keys.take i ++ [key] := by
    rw [List.take_add_one, hk]; rfl
  intro w u hu
  rw [htake]
  by_cases hw : w = key
  · subst hw
    rw [hv] at hu; cases hu
    rw [ite_eq_left_of_eq_true _ _ (eq_true (List.mem_append_right _ (List.mem_singleton.2 rfl)))]
    exact ⟨v', GMap.lookup_insert _ _ _, ho⟩
  · have hmem : (w ∈ keys.take i ++ [key]) ↔ w ∈ keys.take i := by
      simp [hw]
    have := hd w u hu
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hw)]
    by_cases hin : w ∈ keys.take i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hmem.2 hin))]; rw [ite_eq_left_of_eq_true _ _ (eq_true hin)] at this; exact this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hin (hmem.1 h)))]; rw [ite_eq_right_of_eq_false _ _ (eq_false hin)] at this; exact this

theorem demuxRLW_done_final {c : DemuxCore} {views views' : GMap Loc View} {keys : List Loc}
    (hd : demuxRLW_done c views keys keys.length views')
    (hkeys : ∀ k, k ∈ keys ↔ (lagOf views !! k).isSome) (hmin : ¬ c.minRev = W64 0)
    (hdom : ∀ w, (views !! w).isSome = (views' !! w).isSome) : ResyncStep c views views' := by
  refine ⟨hdom, fun w v hv => ?_⟩
  have h := hd w v hv
  rw [List.take_length] at h
  have hlag : w ∈ keys ↔ v.phase = .lagging := by
    rw [hkeys, lagOf_lookup, hv]; by_cases hp : v.phase = .lagging <;> simp [hp]
  by_cases hp : v.phase = .lagging
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h'; rcases h' with h' | h'; exact hmin h'; exact h' hp))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (hlag.2 hp))] at h; exact h
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr hp))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hp (hlag.1 h')))] at h; exact h

theorem demuxRLW_out_compact (c : DemuxCore) (v : View) (nv : w64) (hn : v.n = nv)
    (h : sint.Z nv < sint.Z c.minRev) : ResyncOutcome c v { v with phase := .closed (some nv) } := by
  subst hn; unfold ResyncOutcome; simp [h]

theorem demuxRLW_out_fail (c : DemuxCore) (v : View) (nv : w64) (hn : v.n = nv)
    (hph : v.phase = .lagging) (h : ¬ sint.Z nv < sint.Z c.minRev) (j : Nat)
    (hj : j < (ascendGeVisited batchRev nv c.history).length) :
    ResyncOutcome c v { v with n := resyncNext nv (ascendGeVisited batchRev nv c.history) j } := by
  subst hn; unfold ResyncOutcome; simp only [h, ite_false]
  refine ⟨trivial, trivial, Or.inr ⟨hph, j, hj, rfl⟩⟩

theorem demuxRLW_out_ok (c : DemuxCore) (v : View) (nv nf : w64) (hn : v.n = nv)
    (h : ¬ sint.Z nv < sint.Z c.minRev)
    (hnf : nf = resyncNext nv (ascendGeVisited batchRev nv c.history)
        (ascendGeVisited batchRev nv c.history).length ∨
      (sint.Z (resyncNext nv (ascendGeVisited batchRev nv c.history)
        (ascendGeVisited batchRev nv c.history).length) < sint.Z c.maxRev ∧ nf = c.maxRev + W64 1)) :
    ResyncOutcome c v { v with n := nf, phase := .active } := by
  subst hn; unfold ResyncOutcome; simp only [h, ite_false]
  refine ⟨trivial, trivial, Or.inl ⟨trivial, ?_⟩⟩
  simpa using hnf

/-- A start `0` or above the base, initialized: the start condition holds for any view. -/
theorem demuxRLW_startOk_of {c : DemuxCore} {ri : RegInfo} (h : ri.s = W64 0 ∨ c.base < sint.Z ri.s)
    (hm : c.minRev ≠ W64 0) (v' : View) : StartOk c ri v' := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hm, h⟩)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.resyncLaggingWatchers.wp_proof
    (wp_Compact : watcher.Compact.spec (GF := GF) (hG := hG))
    (wp_AscendGreaterOrEqual : ringBuffer.AscendGreaterOrEqual.spec (GF := GF) (hG := hG))
    (wp_enqueueResponse : watcher.enqueueResponse.spec (GF := GF) (hG := hG)) :
    demux.resyncLaggingWatchers.spec (GF := GF) (hG := hG) := by
  intro d γd cap C
  wp_start as ⟨#Hd, Hh⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlocked, HP⟩
  icombine Hlc1 Hlc2 as Hlc
  imod demux_lock_acquire d γd cap $$ [$Hd $HP $Hlc] with ⟨%c, %regs, %views, Hcore, Hlk, %Hinv⟩
  iNamed Hlk
  wp_auto
  wp_if_destruct
  · -- not initialized: nothing to do
    imod demux_lock_release d γd cap c regs views $$ [Hd Hcore Hregs Hviews HminRev HmaxRev HactF
      HlagF Hact Hlag Hhist Hres Hlc3] with HP
    · iframe Hd Hcore Hlc3
      isplitl
      · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #
        ipureintro; exact ⟨Hok, Hstart⟩
      ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hh
    iapply HΦ
    iframe Hh
    ipureintro
    exact ⟨c, views, views, Hinv, fun w => rfl, fun w v hv => by simp [Hif, hv]⟩
  have Hmin := Hif
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_mut_keys (fun (keys : List Loc) (i : Nat) (m' : GMap Loc w64) =>
      iprop(∃ (views_i : GMap Loc View) (x : w64) (y : Loc),
        "d" ∷ d_ptr ↦ d ∗ "nextRev" ∷ nextRev_ptr ↦ x ∗ "w" ∷ w_ptr ↦ y ∗
        "Hviews" ∷ ghostMapAuth γd.views 1 views_i ∗
        "Hact" ∷ actP ↦$ actOf views_i ∗
        "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes C γd w ri) ∗
        "HminRev" ∷ demuxMinRevAddr d ↦ c.minRev ∗
        "HmaxRev" ∷ demuxMaxRevAddr d ↦ c.maxRev ∗
        "HactF" ∷ demuxActAddr d ↦ actP ∗
        "HlagF" ∷ demuxLagAddr d ↦ lagP ∗
        "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history ∗
        "%Hm'" ∷ ⌜m' = lagOf views_i⌝ ∗
        "%Hok_i" ∷ ⌜RegsOk c c.stream.length regs views_i⌝ ∗
        "%Hrs" ∷ ⌜RegsStart c regs views_i⌝ ∗
        "%Hdone" ∷ ⌜demuxRLW_done c views keys i views_i⌝))) $$ Hlag
  iintro %keys ⟨%Hkeys, %Hklen, %Hnodup⟩
  isplitl [d nextRev w Hviews Hact Hres HminRev HmaxRev HactF HlagF Hhist]
  · iexists views, _, _; simp only [named]; iframe; ipureintro
    exact ⟨trivial, Hok, Hstart, fun w v hv => by simp [hv]⟩
  isplitr
  · imodintro
    iintro %i %key %nv %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hlagm
    iNamed HP
    subst Hm'
    -- the watcher at `key`: lagging, with view `v0` and registration `ri`
    have Hlk : lagOf views_i !! key = some nv := by rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    rw [lagOf_lookup] at Hlk
    obtain ⟨v0, Hv0, Hph, Hn⟩ : ∃ v0, views_i !! key = some v0 ∧ v0.phase = .lagging ∧ v0.n = nv := by
      cases h : views_i !! key with
      | none => simp [h] at Hlk
      | some v0 =>
        rw [h] at Hlk
        by_cases hp : v0.phase = .lagging
        · simp [hp] at Hlk; exact ⟨v0, rfl, hp, Hlk⟩
        · simp [hp] at Hlk
    obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
      have := Hok_i.dom key
      rw [Hv0] at this
      exact Option.isSome_iff_exists.1 (by simpa using this)
    obtain ⟨Hst, Hmx⟩ := Hok_i.mapped key v0 Hv0 (by rw [Hph]; rfl)
    icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
    iNamed Hr
    icombine Hviews Hview gives %Hvv
    have Hvv0 : v = v0 := by
      have : views_i !! key = some v := Hvv
      rw [Hv0] at this; exact (Option.some.inj this).symm
    subst Hvv0
    have HSO := Hrs.get Hri Hv0 (by rw [Hph]; rfl)
    have Hsr := Hrs.sr_ok key ri Hri
    have Hvinit : views !! key = some v := by
      have h1 := Hv
      rw [lagOf_lookup] at h1
      cases hu : views !! key with
      | none => simp [hu] at h1
      | some u =>
        have := demuxRLW_done_cur Hdone Hnodup Hkey hu
        rw [Hv0] at this
        rw [Option.some.inj this]
    simp only [Hph, RegPhase.toWatcher, watcherAt]
    wp_auto
    have Hnot_act : actOf views_i !! key = none := by
      rw [actOf_lookup, Hv0]; simp [Hph]
    wp_if_destruct
    · -- `nextRev < minRev`: compacted at `nv`
      ihave #Hcp := pub_close (C := C) pred ri.sr ri.s v sent (some nv) c.base Hsr Hdel HSO.cond
        (fun m hm => by cases hm; exact Hn.symm) $$ [Hcerts]
      · rw [Hst]; iexact Hcerts
      wp_apply wp_Compact key ri.γ pred (demuxPub C pred ri.sr) sent .opened nv $$ [Hwat] as #Hcl
      · iframe Hw; simp only [watcherAt, watcherClosePub, demuxPub]; iframe Hwat
        iexact Hcp
      let v' : View := { v with phase := .closed (some nv) }
      imod ghost_map_update v' $$ Hviews Hview with ⟨Hviews, Hview⟩
      wp_apply wp_mapDelete $$ Hlagm as Hlagm
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists GMap.delete key (lagOf views_i)
      iframe Hlagm
      have Hlag' : lagOf (GMap.insert key v' views_i) = GMap.delete key (lagOf views_i) := by
        rw [lagOf_insert]; simp [v']
      have Hact' : actOf (GMap.insert key v' views_i) = actOf views_i := by
        rw [actOf_insert]; simp [v', GMap.delete_notin _ _ Hnot_act]
      isplitl
      · iexists GMap.insert key v' views_i, nv, key
        simp only [named]
        rw [Hact']
        iframe
        isplitl
        · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
          iframe Hres
          unfold regRes
          iexists sent, v', pred
          simp only [named]
          iframe Hw Hpred Hview Huniq
          simp only [v', RegPhase.toWatcher, watcherAt, WatcherPhase.cancelAfter]
          iframe Hcl
          ipureintro
          exact Hdel.phase _ (fun m hm => by cases hm; exact Hn.symm)
        ipureintro
        refine ⟨Hlag'.symm, ?_, ?_, ?_⟩
        · exact Hok_i.insert (by rw [Hri]; rfl) v' (fun h => by simp [v', RegPhase.mapped] at h)
            (fun h => by simp [v'] at h)
        · exact Hrs.insert Hri v' (fun h => by simp [v', RegPhase.mapped] at h)
        · exact demuxRLW_done_step Hdone Hkey Hvinit (demuxRLW_out_compact c v nv Hn Hif)
      ipureintro
      intro k hk
      exact GMap.lookup_delete_ne _ (Ne.symm hk)
    -- `nextRev ≥ minRev`: resend the history from `nv` on
    have Hge : ¬ sint.Z nv < sint.Z c.minRev := Hif
    have HSOr := HSO.resync Hinv.base_minRev Hmin (by rw [Hn]; omega)
    obtain ⟨pre, Hpre_eq, Hpre⟩ := demuxRLW_stream_split Hinv Hge
    have Hhs := demuxRLW_hist_sorted Hinv
    have Hvs : RevSorted batchRev (ascendGeVisited batchRev nv c.history) := demuxRLW_vis_sorted Hhs
    have Hvge : ∀ b ∈ ascendGeVisited batchRev nv c.history, sint.Z nv ≤ sint.Z (batchRev b) :=
      demuxRLW_vis_ge Hhs
    have Hvmem : ∀ b ∈ ascendGeVisited batchRev nv c.history, b ∈ c.stream := fun b hb => by
      rw [Hpre_eq]; exact List.mem_append_right _ hb
    have Hvle : ∀ b ∈ ascendGeVisited batchRev nv c.history,
        sint.Z (batchRev b) ≤ sint.Z c.maxRev := fun b hb => Hinv.stream_le b (Hvmem b hb)
    have Hvbd : ∀ b ∈ ascendGeVisited batchRev nv c.history, sint.Z (batchRev b) < 2 ^ 63 - 1 :=
      fun b hb => by have := Hvle b hb; have := Hinv.maxRev_lt; omega
    generalize Hvis : ascendGeVisited batchRev nv c.history = vis at Hvs Hvge Hvmem Hvle Hvbd Hpre_eq
    have Hv_eq : { v with n := resyncNext nv vis 0 } = v := by
      show { v with n := nv } = v; rw [← Hn]
    wp_apply (wp_AscendGreaterOrEqual (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
      (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history nv _
      (fun j => iprop(∃ sent',
        "Hopen" ∷ watcherOpen ri.γ sent' ∗ "nextRev" ∷ nextRev_ptr ↦ resyncNext nv vis j ∗
        "rs" ∷ resyncSuccess_ptr ↦ true ∗ "w" ∷ w_ptr ↦ key ∗
        "%Hd" ∷ ⌜Delivered pred ri.s { v with n := resyncNext nv vis j } sent'⌝))
      iprop(∃ (j : Nat) (sent' : List RespModel), "%Hj" ∷ ⌜j < vis.length⌝ ∗
        "Hopen" ∷ watcherOpen ri.γ sent' ∗ "nextRev" ∷ nextRev_ptr ↦ resyncNext nv vis j ∗
        "rs" ∷ resyncSuccess_ptr ↦ false ∗ "w" ∷ w_ptr ↦ key ∗
        "%Hd" ∷ ⌜Delivered pred ri.s { v with n := resyncNext nv vis j } sent'⌝))
      $$ [Hhist Hwat nextRev resyncSuccess w] as ⟨Hhist, Hpost⟩
    · iframe Hhist
      isplitl [Hwat nextRev resyncSuccess w]
      · iexists sent; simp only [named]; iframe; ipureintro; rw [Hv_eq]; exact Hdel
      rw [Hvis]
      unfold iterSpec
      iintro %j %p %b %Hb
      wp_start_folded as ⟨HPj, #Hbat⟩
      icases HPj with ⟨%sent0, HPj⟩
      iNamed HPj
      wp_auto
      unfold batchAt
      icases Hbat with ⟨#Hev, %Hbok⟩
      have Hb_mem : b ∈ vis := List.mem_of_getElem? Hb
      have Hrange : streamRange (resyncNext nv vis j) (batchRev b + W64 1) v.stream = [b] := by
        rw [Hst, Hpre_eq]; exact demuxRLW_range_one nv pre vis Hpre Hvs Hvge Hvbd j b Hb
      have Hlo := demuxRLW_next_le nv vis Hvs Hvge Hvbd j b Hb
      have Hbb := Hvbd b Hb_mem
      have Hbm := Hvle b Hb_mem
      have hsucc : sint.Z (batchRev b + W64 1) = sint.Z (batchRev b) + 1 := by word
      have Hnext : ∀ r', filterResp pred (eventsResp b) = some r' →
          ∃ n' : w64, Delivered pred ri.s { { v with n := resyncNext nv vis j } with n := n' }
            (sent0 ++ [r']) := by
        intro r' hr'
        exact ⟨batchRev b + W64 1, (Hd.enqueue_events (n' := batchRev b + W64 1)
          (by simp [Hph, RegPhase.mapped]) (by simp only; omega) (by simp only; rw [Hmx]; omega)
          (by simp only; rw [Hrange]; simpa using Hbok.1)
          (by simp only; rw [Hrange]; simpa using enqueueResult_some sent0 hr')).1 rfl⟩
      ihave #Hpub := pub_send (C := C) pred ri.sr ri.s { v with n := resyncNext nv vis j } sent0
        (eventsResp b) c.base Hsr HSOr Hnext $$ [Hcerts]
      · simp only; rw [Hst]; iexact Hcerts
      wp_apply wp_enqueueResponse key ri.γ pred (demuxPub C pred ri.sr) sent0 _ (eventsResp b)
        $$ [Hopen] as %ok ⟨%sent'', Hopen, %Henq⟩
      · iframe Hw Hopen
        isplitl
        · unfold respAt hdrAt eventsResp
          iframe Hev
          isplitl
          · ileft; ipureintro; exact ⟨rfl, rfl⟩
          ipureintro; exact ⟨rfl, rfl, rfl⟩
        simp only [demuxPub]; iexact Hpub
      obtain ⟨HEok, HEfail⟩ := Hd.enqueue_events (n' := batchRev b + W64 1)
        (by simp [Hph, RegPhase.mapped]) (by simp only; omega) (by simp only; rw [Hmx]; omega)
        (by simp only; rw [Hrange]; simpa using Hbok.1)
        (by simp only; rw [Hrange]; simpa using Henq)
      cases ok
      · -- the send failed: stop, still lagging at batch `j`
        have Hs := HEfail rfl
        subst Hs
        wp_auto
        iapply HΦ
        simp only [Bool.false_eq_true, ite_false]
        iexists j, sent''
        simp only [named]
        iframe
        ipureintro
        exact ⟨(List.getElem?_eq_some_iff.1 Hb).1, Hd⟩
      · -- sent: go on with `j + 1`
        wp_auto
        iapply HΦ
        simp only [ite_true]
        iexists sent''
        simp only [named]
        rw [demuxRLW_next_succ nv vis j b Hb]
        iframe
        ipureintro
        exact HEok rfl
    rw [Hvis]
    icases Hpost with (HQ | HPv)
    · -- a send failed at batch `j`: still lagging, at `resyncNext nv vis j`
      icases HQ with ⟨%j, %sent1, HQ⟩
      iNamed HQ
      let v' : View := { v with n := resyncNext nv vis j }
      imod ghost_map_update v' $$ Hviews Hview with ⟨Hviews, Hview⟩
      wp_auto
      wp_apply wp_mapInsert $$ Hlagm as Hlagm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists GMap.insert key (resyncNext nv vis j) (lagOf views_i)
      iframe Hlagm
      have Hlag' : lagOf (GMap.insert key v' views_i) =
          GMap.insert key (resyncNext nv vis j) (lagOf views_i) := by
        rw [lagOf_insert]; simp [v', Hph]
      have Hact' : actOf (GMap.insert key v' views_i) = actOf views_i := by
        rw [actOf_insert]; simp [v', Hph, GMap.delete_notin _ _ Hnot_act]
      isplitl
      · iexists GMap.insert key v' views_i, resyncNext nv vis j, key
        simp only [named]
        rw [Hact']
        iframe
        isplitl
        · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
          iframe Hres
          unfold regRes
          iexists sent1, v', pred
          simp only [named]
          iframe Hw Hpred Hview Huniq
          simp only [v', Hph, RegPhase.toWatcher, watcherAt]
          iframe Hopen
          ipureintro; rw [Hph] at Hd; exact Hd
        ipureintro
        refine ⟨Hlag'.symm, ?_, ?_, ?_⟩
        · exact Hok_i.insert (by rw [Hri]; rfl) v' (fun _ => ⟨Hst, Hmx⟩)
            (fun h => by simp [v', Hph] at h)
        · exact Hrs.insert Hri v' (fun _ => demuxRLW_startOk_of HSOr Hmin v')
        · have Ho := demuxRLW_out_fail c v nv Hn Hph Hge j (by rw [Hvis]; exact Hj)
          rw [Hvis] at Ho
          exact demuxRLW_done_step Hdone Hkey Hvinit Ho
      ipureintro
      intro k hk
      exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
    -- every batch resent: active
    icases HPv with ⟨%sent1, HPv⟩
    iNamed HPv
    have Hall := demuxRLW_all_below nv pre vis Hpre Hvs Hvge Hvbd
    rw [← Hpre_eq] at Hall
    wp_auto
    ihave %Hhnn := typedPointsto_not_null $$ «$v0»
    iStructNamed «$v0»
    ipersist Revision
    have Hmr := Hinv.maxRev_lt
    wp_join iprop(∃ (nf : w64) (sent2 : List RespModel),
        "d" ∷ d_ptr ↦ d ∗ "w" ∷ w_ptr ↦ key ∗ "HmaxRev" ∷ demuxMaxRevAddr d ↦ c.maxRev ∗
        "nextRev" ∷ nextRev_ptr ↦ nf ∗ "Hopen" ∷ watcherOpen ri.γ sent2 ∗
        "%Hnf" ∷ ⌜Delivered pred ri.s { v with n := nf } sent2 ∧
          (nf = resyncNext nv vis vis.length ∨
            (sint.Z (resyncNext nv vis vis.length) < sint.Z c.maxRev ∧ nf = c.maxRev + W64 1))⌝)
      with [d w HmaxRev nextRev Hopen resp] as HR
    · -- below `maxRev`: a progress notification at `maxRev`
      have Hlt := Hif
      have hsucc : sint.Z (c.maxRev + W64 1) = sint.Z c.maxRev + 1 := by word
      have Hnext : ∀ r', filterResp pred (progressResp c.maxRev) = some r' →
          ∃ n' : w64, Delivered pred ri.s
            { { v with n := resyncNext nv vis vis.length } with n := n' } (sent1 ++ [r']) := by
        intro r' hr'
        exact ⟨c.maxRev + W64 1, (Hd.enqueue_progress (n' := c.maxRev + W64 1)
          (by simp [Hph, RegPhase.mapped]) (by simp only; rw [Hst]; exact Hall)
          (by simp only; omega) (by simp only; rw [Hmx]; omega)
          (by simp only; rw [Hmx]; exact enqueueResult_some sent1 hr')).2 rfl⟩
      ihave #Hpub := pub_send (C := C) pred ri.sr ri.s { v with n := resyncNext nv vis vis.length }
        sent1 (progressResp c.maxRev) c.base Hsr HSOr Hnext $$ [Hcerts]
      · simp only; rw [Hst]; iexact Hcerts
      wp_apply wp_enqueueResponse key ri.γ pred (demuxPub C pred ri.sr) sent1 _
        (progressResp c.maxRev) $$ [Hopen] as %ok ⟨%sent2, Hopen, %Henq⟩
      · iframe Hw Hopen
        isplitl
        · unfold respAt hdrAt eventsAt progressResp
          isplitl
          · iexists ([] : List Loc)
            isplitr
            · iapply ownSlice_nil
            isplitr
            · ipureintro; rfl
            imodintro
            iintro %i' %ev %e %h
            simp at h
          isplitl
          · iright
            isplitr
            · ipureintro; exact Hhnn
            iexact Revision
          ipureintro; exact ⟨rfl, rfl, rfl⟩
        simp only [demuxPub]; iexact Hpub
      obtain ⟨HP1, HP2⟩ := Hd.enqueue_progress (n' := c.maxRev + W64 1)
        (by simp [Hph, RegPhase.mapped]) (by simp only; rw [Hst]; exact Hall)
        (by simp only; omega) (by simp only; rw [Hmx]; omega) (by simp only; rw [Hmx]; exact Henq)
      cases ok
      · wp_auto
        wp_join_done
        iexists resyncNext nv vis vis.length, sent2
        simp only [named]
        iframe
        ipureintro; exact ⟨HP1, Or.inl trivial⟩
      · wp_auto
        wp_join_done
        iexists c.maxRev + W64 1, sent2
        simp only [named]
        iframe
        ipureintro; exact ⟨HP2 rfl, Or.inr ⟨Hlt, trivial⟩⟩
    · -- no notification
      iexists resyncNext nv vis vis.length, sent1
      simp only [named]
      iframe
      ipureintro; exact ⟨Hd, Or.inl trivial⟩
    icases HR with ⟨%nf, %sent2, HR⟩
    iNamed HR
    obtain ⟨Hdn, Hnfc⟩ := Hnf
    let v' : View := { v with n := nf, phase := .active }
    imod ghost_map_update v' $$ Hviews Hview with ⟨Hviews, Hview⟩
    wp_auto
    wp_apply wp_mapDelete $$ Hlagm as Hlagm
    wp_apply wp_mapInsert $$ Hact as Hact
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists GMap.delete key (lagOf views_i)
    iframe Hlagm
    have Hlag' : lagOf (GMap.insert key v' views_i) = GMap.delete key (lagOf views_i) := by
      rw [lagOf_insert]; simp [v']
    have Hact' : actOf (GMap.insert key v' views_i) = GMap.insert key nf (actOf views_i) := by
      rw [actOf_insert]; simp [v']
    have Hup : ∀ b ∈ c.stream.take c.stream.length, sint.Z (batchRev b) < sint.Z nf := by
      rw [List.take_length]
      intro b hb
      rcases Hnfc with rfl | ⟨-, rfl⟩
      · exact Hall b hb
      · have := Hinv.stream_le b hb
        have : sint.Z (c.maxRev + W64 1) = sint.Z c.maxRev + 1 := by word
        omega
    isplitl
    · iexists GMap.insert key v' views_i, nf, key
      simp only [named]
      rw [Hact']
      iframe
      isplitl
      · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
        iframe Hres
        unfold regRes
        iexists sent2, v', pred
        simp only [named]
        iframe Hw Hpred Hview Huniq
        simp only [v', RegPhase.toWatcher, watcherAt]
        iframe Hopen
        ipureintro
        exact Hdn.phase .active (fun m h => by cases h)
      ipureintro
      refine ⟨Hlag'.symm, ?_, ?_, ?_⟩
      · exact Hok_i.insert (by rw [Hri]; rfl) v' (fun _ => ⟨Hst, Hmx⟩) (fun _ => Hup)
      · exact Hrs.insert Hri v' (fun _ => demuxRLW_startOk_of HSOr Hmin v')
      · have Ho := demuxRLW_out_ok c v nv nf Hn Hge (by rw [Hvis]; exact Hnfc)
        exact demuxRLW_done_step Hdone Hkey Hvinit Ho
    ipureintro
    intro k hk
    exact GMap.lookup_delete_ne _ (Ne.symm hk)
  iintro %m' HP Hlagm
  iNamed HP
  subst Hm'
  wp_auto
  imod demux_lock_release d γd cap c regs views_i $$ [Hd Hcore Hregs Hviews HminRev HmaxRev HactF
    HlagF Hact Hlagm Hhist Hres Hlc3] with HP
  · iframe Hd Hcore Hlc3
    isplitl
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #
      ipureintro; exact ⟨Hok_i, Hrs⟩
    ipureintro; exact Hinv
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hh
  iapply HΦ
  iframe Hh
  ipureintro
  exact ⟨c, views, views_i, Hinv, demuxRLW_done_final Hdone Hkeys Hmin
    (fun w => by rw [← Hok.dom w, Hok_i.dom w])⟩

end proof

end EtcdGrove
end Perennial
