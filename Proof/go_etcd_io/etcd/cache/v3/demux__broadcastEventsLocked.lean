/-
Proof of `Spec/demux__broadcastEventsLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastEventsLocked
public import Spec.go_etcd_io.etcd.cache.v3.watcher__enqueueResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-- An event of a batch of `splitBatches xs` is an event of `xs`, and the batch's revision is
one of its events'. -/
theorem demuxBEL_batch_mem {xs : List EvModel} {b : Batch} (hb : b ∈ splitBatches xs) :
    ∃ e ∈ xs, batchRev b = e.rev := by
  have hok := splitBatches_ok xs b hb
  cases b with
  | nil => exact absurd rfl hok.1
  | cons e es =>
    refine ⟨e, ?_, rfl⟩
    rw [← splitBatches_flatten xs]
    exact List.mem_flatten.2 ⟨e :: es, hb, List.mem_cons_self ..⟩

theorem demuxBEL_mem_take {xs : List EvModel} {n : Nat} {e : EvModel} (h : e ∈ xs.take n) :
    ∃ j, j < n ∧ xs[j]? = some e := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_take] at hj
  split at hj
  · exact ⟨j, by omega, hj⟩
  · simp at hj

theorem demuxBEL_mem_drop {xs : List EvModel} {n : Nat} {e : EvModel} (h : e ∈ xs.drop n) :
    ∃ j, n ≤ j ∧ xs[j]? = some e := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_drop] at hj
  exact ⟨n + j, by omega, hj⟩

theorem demuxBEL_sorted_le {xs : List EvModel} (hs : EvRevSorted xs) {i j : Nat} {a b : EvModel}
    (ha : xs[i]? = some a) (hb : xs[j]? = some b) (hij : i ≤ j) : sint.Z a.rev ≤ sint.Z b.rev := by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · unfold EvRevSorted at hs
    rw [List.pairwise_iff_getElem] at hs
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    exact hs i j hi hj h
  · rw [ha] at hb; cases hb; exact Int.le_refl _

theorem demuxBEL_le_last {xs : List EvModel} (hs : EvRevSorted xs) {eL : EvModel}
    (hL : xs[xs.length - 1]? = some eL) {e : EvModel} (he : e ∈ xs) :
    sint.Z e.rev ≤ sint.Z eL.rev := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
  have := (List.getElem?_eq_some_iff.1 hj).1
  exact demuxBEL_sorted_le hs hj hL (by omega)

/-- The events sent (`events[sendStart:]`) are the stream's batches from `n` on. -/
theorem demuxBEL_send (st old : List Batch) (evs : List EvModel) (hst : st = old ++ splitBatches evs)
    (hs : EvRevSorted evs) (n : w64) (hold : ∀ b ∈ old, sint.Z (batchRev b) < sint.Z n)
    (eL : EvModel) (hL : evs[evs.length - 1]? = some eL) (hLb : sint.Z eL.rev < 2 ^ 63 - 1)
    (ss : Nat) (hss : ss < evs.length)
    (hbefore : ∀ j e, j < ss → evs[j]? = some e → sint.Z e.rev < sint.Z n)
    (hat : ∀ e, evs[ss]? = some e → sint.Z n ≤ sint.Z e.rev) :
    (streamRange n (eL.rev + W64 1) st).flatten = evs.drop ss := by
  have hL1 : sint.Z (eL.rev + W64 1) = sint.Z eL.rev + 1 := by word
  obtain ⟨es, hes⟩ : ∃ es, evs[ss]? = some es := ⟨_, List.getElem?_eq_getElem hss⟩
  have hsplit : splitBatches evs = splitBatches (evs.take ss) ++ splitBatches (evs.drop ss) := by
    conv => lhs; rw [← List.take_append_drop ss evs]
    apply splitBatches_append
    intro x y hx hy
    rw [List.getLast?_eq_getElem?] at hx
    rw [List.length_take, show min ss evs.length = ss by omega] at hx
    rw [List.head?_drop] at hy
    cases ss with
    | zero => simp at hx
    | succ m =>
      rw [List.getElem?_take] at hx
      simp only [Nat.add_sub_cancel, Nat.lt_add_one, ↓reduceIte] at hx
      have h1 := hbefore m x (by omega) hx
      have h2 := hat y hy
      intro heq; rw [heq] at h1; omega
  rw [hst, hsplit, streamRange, List.filter_append, List.filter_append]
  have hf1 : old.filter (fun b => decide (sint.Z n ≤ sint.Z (batchRev b) ∧
      sint.Z (batchRev b) < sint.Z (eL.rev + W64 1))) = [] := by
    apply List.filter_eq_nil_iff.2
    intro b hb; have := hold b hb; simp only [decide_eq_true_eq]; intro h; omega
  have hf2 : (splitBatches (evs.take ss)).filter (fun b => decide (sint.Z n ≤ sint.Z (batchRev b) ∧
      sint.Z (batchRev b) < sint.Z (eL.rev + W64 1))) = [] := by
    apply List.filter_eq_nil_iff.2
    intro b hb
    obtain ⟨e, he, hr⟩ := demuxBEL_batch_mem hb
    obtain ⟨j, hj, hje⟩ := demuxBEL_mem_take he
    have := hbefore j e hj hje
    simp only [decide_eq_true_eq]; rw [hr]; intro h; omega
  have hf3 : (splitBatches (evs.drop ss)).filter (fun b => decide (sint.Z n ≤ sint.Z (batchRev b) ∧
      sint.Z (batchRev b) < sint.Z (eL.rev + W64 1))) = splitBatches (evs.drop ss) := by
    apply List.filter_eq_self.2
    intro b hb
    obtain ⟨e, he, hr⟩ := demuxBEL_batch_mem hb
    obtain ⟨j, hj, hje⟩ := demuxBEL_mem_drop he
    have h1 := hat es hes
    have h2 := demuxBEL_sorted_le hs hes hje hj
    have h3 := demuxBEL_le_last hs hL (List.mem_of_getElem? hje)
    simp only [decide_eq_true_eq]
    rw [hr, hL1]; omega
  rw [hf1, hf2, hf3, List.nil_append, List.nil_append, splitBatches_flatten]

/-- Nothing sent: every event below `n`, so every stream batch is. -/
theorem demuxBEL_none (st old : List Batch) (evs : List EvModel) (hst : st = old ++ splitBatches evs)
    (n : w64) (hold : ∀ b ∈ old, sint.Z (batchRev b) < sint.Z n)
    (hev : ∀ e ∈ evs, sint.Z e.rev < sint.Z n) :
    ∀ b ∈ st, sint.Z (batchRev b) < sint.Z n := by
  intro b hb
  rw [hst] at hb
  rcases List.mem_append.1 hb with h | h
  · exact hold b h
  · obtain ⟨e, he, hr⟩ := demuxBEL_batch_mem h
    rw [hr]; exact hev e he

/-- Every stream batch is at or below the last event. -/
theorem demuxBEL_le_lastRev (st old : List Batch) (evs : List EvModel)
    (hst : st = old ++ splitBatches evs) (hsorted : RevSorted batchRev st) (hs : EvRevSorted evs)
    (hne : evs ≠ []) (eL : EvModel) (hL : evs[evs.length - 1]? = some eL) :
    ∀ b ∈ st, sint.Z (batchRev b) ≤ sint.Z eL.rev := by
  have hbs : ∀ b ∈ splitBatches evs, sint.Z (batchRev b) ≤ sint.Z eL.rev := by
    intro b hb
    obtain ⟨e, he, hr⟩ := demuxBEL_batch_mem hb
    rw [hr]; exact demuxBEL_le_last hs hL he
  obtain ⟨b1, hb1⟩ : ∃ b1, b1 ∈ splitBatches evs := by
    cases h : splitBatches evs with
    | nil => exact absurd ((splitBatches_eq_nil_iff evs).1 h) hne
    | cons b _ => exact ⟨b, List.mem_cons_self ..⟩
  intro b hb
  rw [hst] at hb hsorted
  rcases List.mem_append.1 hb with h | h
  · unfold RevSorted at hsorted
    have := (List.pairwise_append.1 hsorted).2.2 b h b1 hb1
    have := hbs b1 hb1
    omega
  · exact hbs b h

theorem demuxBEL_regsOk_full {c : DemuxCore} {k : Nat} {regs : GMap Loc RegInfo}
    {views : GMap Loc View} (h : RegsOk c k regs views)
    (hf : ∀ w v, views !! w = some v → v.phase = .active →
      ∀ b ∈ c.stream, sint.Z (batchRev b) < sint.Z v.n) :
    RegsOk c c.stream.length regs views where
  dom := h.dom
  mapped := h.mapped
  active_up w v hv ha b hb := hf w v hv ha b (by rw [List.take_length] at hb; exact hb)

/-- An active watcher's start condition does not depend on its view. -/
theorem demuxBEL_startOk_active {c : DemuxCore} {ri : RegInfo} {v : View} (h : StartOk c ri v)
    (hph : v.phase = .active) (v' : View) : StartOk c ri v' := by
  rcases h with h1 | h2 | ⟨h4, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rw [hph] at h4; cases h4

/-- The "processed" fact after one more key. -/
theorem demuxBEL_processed_step {keys : List Loc} {i : Nat} {key : Loc} (hkey : keys[i]? = some key)
    {views views' : GMap Loc View} {P : View → Prop}
    (h : ∀ w v, views !! w = some v → v.phase = .active → w ∉ keys.drop i → P v)
    (hother : ∀ w, w ≠ key → views' !! w = views !! w)
    (hkey' : ∀ v, views' !! key = some v → v.phase = .active → P v) :
    ∀ w v, views' !! w = some v → v.phase = .active → w ∉ keys.drop (i + 1) → P v := by
  intro w v hv ha hn
  by_cases hw : w = key
  · subst hw; exact hkey' v hv ha
  · rw [hother w hw] at hv
    apply h w v hv ha
    have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hkey).1
    rw [List.drop_eq_getElem_cons hi, (List.getElem?_eq_some_iff.1 hkey).2]
    intro hm
    rcases List.mem_cons.1 hm with h1 | h1
    · exact hw h1
    · exact hn h1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demuxBEL_eventsAt_drop (sl : GoSlice) (evs : List EvModel) (j : w64)
    (hj : 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len) :
    eventsAt (GF := GF) sl evs ⊢ eventsAt (slice.slice sl Loc j sl.len) (evs.drop (sint.nat j)) := by
  unfold eventsAt
  iintro ⟨%ls, #Hsl, %Hlen, #Hev⟩
  ihave %HslLen := ownSlice_len _ _ _ $$ Hsl
  ihave ⟨-, #Hmid, -⟩ := (ownSlice_slice j sl.len sl DFrac.discard ls ⟨hj.1, hj.2, Int.le_refl _⟩).1 $$ Hsl
  iexists ls.drop (sint.nat j)
  isplitl
  · rw [subslice_def, ← HslLen.1, List.take_length] at *
    iexact Hmid
  isplitl
  · ipureintro; simp [Hlen]
  imodintro
  iintro %i %ev %e %Hi %He
  rw [List.getElem?_drop] at Hi He
  iapply Hev $$ %(sint.nat j + i) %ev %e %Hi %He

theorem demuxBEL_delete_none {V : Type} (m : GMap Loc V) (k : Loc) (h : m !! k = none) :
    GMap.delete k m = m := by
  apply GMap.ext; intro k'
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_delete, h]
  · rw [GMap.lookup_delete_ne _ hk]

theorem demux.broadcastEventsLocked.wp_proof
    (wp_enqueueResponse : watcher.enqueueResponse.spec (GF := GF) (hG := hG)) :
    demux.broadcastEventsLocked.spec (GF := GF) (hG := hG) := by
  intro d γd cap C c k regs views evSl evs
  wp_start as ⟨Hl, #Hevs, % ⟨Hinv, Hne, Hsorted, Hst⟩⟩
  iunfold demuxLocked at Hl
  iNamed Hl
  ihave #Hevs' := Hevs
  iunfold eventsAt at Hevs'
  icases Hevs' with ⟨%ls, #Hsl, %HlsLen, #Hev⟩
  ihave %HslLen := ownSlice_len _ _ _ $$ Hsl
  have Hlen1 : 0 < evs.length := List.length_pos_iff.2 Hne
  have Hl0 : 0 < sint.Z evSl.len := by
    have h1 := HslLen.1; have h2 := HslLen.2
    have : 0 < sint.nat evSl.len := by omega
    word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z evSl.len
    from ⟨by word, by word⟩))]
  list_elem ls 0 as evp0
  list_elem evs 0 as e0
  wp_apply wp_load_slice_index evSl (sint.Z (W64 0)) ls DFrac.discard evp0 (by decide) $$ [] as -
  · iframe Hsl; ipureintro; exact Hevp0_lookup
  ihave He0 := Hev $$ %0 %evp0 %e0 %Hevp0_lookup %He0_lookup
  iunfold eventAt at He0
  icases He0 with ⟨%keySl0, #Htyp0, #Hkv0, #Hkey0, #Hks0, #Hmod0⟩
  wp_auto
  have HlastZ : 0 ≤ sint.Z (evSl.len - W64 1) ∧ sint.Z (evSl.len - W64 1) < sint.Z evSl.len := by
    constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true HlastZ)]
  have Hlastn : (sint.Z (evSl.len - W64 1)).toNat = evs.length - 1 := by
    have h1 := HslLen.1
    have : sint.Z (evSl.len - W64 1) = sint.Z evSl.len - 1 := by word
    rw [this]; have : sint.Z evSl.len = (sint.nat evSl.len : Int) := by word
    omega
  list_elem ls (evs.length - 1) as evpL
  list_elem evs (evs.length - 1) as eL
  wp_apply wp_load_slice_index evSl (sint.Z (evSl.len - W64 1)) ls DFrac.discard evpL HlastZ.1 $$ [] as -
  · iframe Hsl; ipureintro; rw [Hlastn]; exact HevpL_lookup
  ihave HeL := Hev $$ %(evs.length - 1) %evpL %eL %HevpL_lookup %HeL_lookup
  iunfold eventAt at HeL
  icases HeL with ⟨%keySlL, #HtypL, #HkvL, #HkeyL, #HksL, #HmodL⟩
  wp_auto
  -- the pure facts about the response
  have HgetL : evs.getLast? = some eL := by rw [List.getLast?_eq_getElem?]; exact HeL_lookup
  have HeLmax : sint.Z eL.rev ≤ sint.Z c.maxRev := by
    obtain ⟨b, hb, hr⟩ := splitBatches_last_rev evs eL HgetL
    have hbm : b ∈ c.stream := by
      rw [Hst]; exact List.mem_append_right _ (List.mem_of_getLast? hb)
    rw [← hr]; exact Hinv.stream_le b hbm
  have HeLb : sint.Z eL.rev < 2 ^ 63 - 1 := by have := Hinv.maxRev_lt; omega
  have HeL1 : sint.Z (eL.rev + W64 1) = sint.Z eL.rev + 1 := by word
  have Hall := demuxBEL_le_lastRev c.stream (c.stream.take k) evs Hst Hinv.stream_ok.sorted
    Hsorted Hne eL HeL_lookup
  ipersist d
  ipersist events
  ipersist firstRev
  ipersist lastRev
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (keys : List Loc) (i : Nat) (m' : GMap Loc w64) =>
      iprop(∃ (x : w64) (y : Loc) (views' : GMap Loc View),
      "nextRev" ∷ nextRev_ptr ↦ x ∗
      "w" ∷ w_ptr ↦ y ∗
      "HactF" ∷ demuxActAddr d ↦ actP ∗
      "HlagF" ∷ demuxLagAddr d ↦ lagP ∗
      "Hviews" ∷ ghostMapAuth γd.views 1 views' ∗
      "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes C γd w ri) ∗
      "Hlag" ∷ lagP ↦$ lagOf views' ∗
      "%Hm" ∷ ⌜m' = actOf views'⌝ ∗
      "%Hok" ∷ ⌜RegsOk c k regs views'⌝ ∗
      "%Hrs" ∷ ⌜RegsStart c regs views'⌝ ∗
      "%Hdone" ∷ ⌜∀ w v, views' !! w = some v → v.phase = .active → w ∉ keys.drop i →
        ∀ b ∈ c.stream, sint.Z (batchRev b) < sint.Z v.n⌝)) $$ Hact
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [nextRev w HactF HlagF Hviews Hres Hlag]
  · iexists _, _, views
    simp only [named]
    iframe
    ipureintro
    refine ⟨trivial, Hok, Hstart, ?_⟩
    intro w v hv ha hn
    exfalso; apply hn
    rw [List.drop_zero, Hkset, actOf_lookup, hv]; simp [ha]
  isplitr
  · imodintro
    iintro %i %key %nv %m' ⟨%Hkey, %Hnv, %Hagree⟩ HP Hm
    iNamed HP
    subst Hm
    have Hcur : actOf views' !! key = some nv := by
      rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hnv
    rw [actOf_lookup] at Hcur
    obtain ⟨v, Hvw, Hvact, Hvn⟩ : ∃ v, views' !! key = some v ∧ v.phase = .active ∧ v.n = nv := by
      cases h : views' !! key with
      | none => simp [h] at Hcur
      | some v =>
        simp only [h, Option.bind_some] at Hcur
        split at Hcur
        · exact ⟨v, rfl, by assumption, by simpa using Hcur⟩
        · simp at Hcur
    obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
      have := Hok.dom key
      rw [Hvw] at this
      cases h : regs !! key with
      | none => simp [h] at this
      | some ri => exact ⟨ri, rfl⟩
    have Hmv := Hok.mapped key v Hvw (by rw [Hvact]; rfl)
    have Hold : ∀ b ∈ c.stream.take k, sint.Z (batchRev b) < sint.Z nv := by
      rw [← Hvn]; exact Hok.active_up key v Hvw Hvact
    subst Hvn
    have Hmapped : v.phase.mapped = true := by rw [Hvact]; rfl
    have HSO := Hrs.get Hri Hvw Hmapped
    wp_auto
    wp_if_destruct
    rotate_left
    wp_if_destruct
    · -- `nextRev != 0 && firstRev > nextRev`: the watcher becomes lagging
      icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
      iNamed Hr
      ihave %Hv := ghost_map_lookup $$ Hviews Hview
      rw [Hvw] at Hv
      cases Hv
      imod ghost_map_update { v with phase := .lagging } $$ Hviews Hview with ⟨Hviews, Hview⟩
      wp_apply wp_mapInsert $$ Hlag as Hlag
      wp_apply wp_mapDelete $$ Hm as Hm
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _, GMap.insert key { v with phase := .lagging } views'
        simp only [named]
        iframe
        isplitl [Hres Hview Hwat Huniq]
        · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
          iframe Hres
          iunfold regRes
          iexists sent, { v with phase := .lagging }, pred
          simp only [named]
          iframe Hw Hpred Hview Huniq
          isplitl
          · simp only [Hvact, RegPhase.toWatcher]; iexact Hwat
          ipureintro
          exact Hdel.phase .lagging (fun m h => by cases h)
        isplitl
        · rw [lagOf_insert]; simp only [↓reduceIte]; iexact Hlag
        ipureintro
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [actOf_insert]; simp
        · apply Hok.insert (by rw [Hri]; rfl)
          · intro _; exact Hmv
          · intro h; cases h
        · exact Hrs.insert Hri _ (fun _ => demuxBEL_startOk_active HSO Hvact _)
        · apply demuxBEL_processed_step Hkey Hdone
          · intro w hw; exact GMap.lookup_insert_ne _ _ (Ne.symm hw)
          · intro v' hv' ha
            rw [GMap.lookup_insert] at hv'; cases hv'; cases ha
      ipureintro; intro k hk
      exact GMap.lookup_delete_ne _ (Ne.symm hk)
    all_goals
      rename_i gi_ptr
      irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
      ihave HI : iprop(∃ (j : w64) (evv : Loc) (gi : w64),
          "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗ "Hgi" ∷ gi_ptr ↦ gi ∗
          "sendStart" ∷ sendStart_ptr ↦ evSl.len ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ evs.length ∧
            ∀ t e, t < sint.nat j → evs[t]? = some e → sint.Z e.rev < sint.Z v.n⌝)
        $$ [i ev Hgi sendStart]
      · iexists W64 0, _, _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro t e ht; exfalso; have : sint.nat (W64 0) = 0 := by word
        omega
      wp_for HI
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z evSl.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have Hjl : sint.nat j < evs.length := by
          have h1 := HslLen.1; have h2 := HslLen.2; word
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z evSl.len
          from ⟨Hj.1, Hlt⟩))]
        list_elem ls (sint.nat j) as evpj
        list_elem evs (sint.nat j) as ej
        wp_apply wp_load_slice_index evSl (sint.Z j) ls DFrac.discard evpj Hj.1 $$ [] as -
        · iframe Hsl; ipureintro; exact Hevpj_lookup
        ihave Hej := Hev $$ %(sint.nat j) %evpj %ej %Hevpj_lookup %Hej_lookup
        iunfold eventAt at Hej
        icases Hej with ⟨%keySlj, #Htypj, #Hkvj, #Hkeyj, #Hksj, #Hmodj⟩
        wp_auto
        wp_if_destruct
        · -- found: break and send
          wp_for_post
          have Hjne : j ≠ evSl.len := by intro h; rw [h] at Hlt; omega
          rw [decide_eq_false Hjne]
          ihave %Hwf := ownSlice_wf $$ Hsl
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z evSl.len ∧
            sint.Z evSl.len ≤ sint.Z evSl.cap from ⟨Hj.1, by omega, Hwf.2⟩))]
          wp_auto
          -- the watcher
          icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
          iNamed Hr
          ihave %Hv := ghost_map_lookup $$ Hviews Hview
          rw [Hvw] at Hv
          cases Hv
          rw [Hvact]
          simp only [RegPhase.toWatcher, watcherAt]
          ihave #Hresp : respAt (GF := GF)
              ({ Header' := null, Events' := slice.slice evSl Loc j evSl.len, CompactRevision' := 0,
                 Canceled' := false, Created' := false, closeErr' := GoInterface.nil,
                 CancelReason' := [] } : go_etcd_io.etcd.client.v3.WatchResponse)
              (eventsResp (evs.drop (sint.nat j))) $$ []
          · unfold respAt
            isplitl
            · dsimp only [eventsResp]
              iapply demuxBEL_eventsAt_drop evSl evs j ⟨Hj.1, by omega⟩ $$ Hevs
            isplitl
            · unfold hdrAt; ileft; ipureintro; exact ⟨rfl, rfl⟩
            ipureintro; exact ⟨rfl, rfl, rfl⟩
          -- the facts
          have Hejle := demuxBEL_le_last Hsorted HeL_lookup (List.mem_of_getElem? Hej_lookup)
          have Hdrop : evs.drop (sint.nat j) = (streamRange v.n (eL.rev + W64 1) v.stream).flatten := by
            rw [Hmv.1]
            refine (demuxBEL_send c.stream (c.stream.take k) evs Hst Hsorted v.n Hold eL HeL_lookup HeLb
              (sint.nat j) Hjl ?_ ?_).symm
            · intro t e ht he; exact Hj.2.2 t e ht he
            · intro e he; rw [Hej_lookup] at he; cases he; exact Hif
          have Hnemp : (streamRange v.n (eL.rev + W64 1) v.stream).flatten ≠ [] := by
            rw [← Hdrop]; intro h
            have := List.drop_eq_nil_iff.1 h; omega
          have Hnext : ∀ r', filterResp pred (eventsResp (evs.drop (sint.nat j))) = some r' →
              ∃ n' : w64, Delivered pred ri.s { v with n := n' } (sent ++ [r']) := by
            intro r' hr'
            rw [Hdrop] at hr'
            exact ⟨eL.rev + W64 1, (Delivered.enqueue_events (n' := eL.rev + W64 1) Hdel Hmapped
              (by rw [HeL1]; omega) (by rw [HeL1, Hmv.2]; omega) Hnemp
              (enqueueResult_some sent hr')).1 rfl⟩
          ihave #Hpub := pub_send (C := C) pred ri.sr ri.s v sent (eventsResp (evs.drop (sint.nat j)))
            c.base (Hrs.sr_ok key ri Hri) (HSO.active Hvact) Hnext $$ [Hcerts] [Hprog]
          · rw [Hmv.1]; iexact Hcerts
          · rw [Hmv.2]; iexact Hprog
          wp_apply wp_enqueueResponse key ri.γ pred (demuxPub C pred ri.sr) sent _
            (eventsResp (evs.drop (sint.nat j))) $$ [Hwat] as %ok ⟨%sent', Hwat, %Henq⟩
          · iframe Hwat Hw Hresp
            simp only [demuxPub]; iexact Hpub
          rw [Hdrop] at Henq
          obtain ⟨HD1, HD2⟩ := Delivered.enqueue_events (n' := eL.rev + W64 1) Hdel Hmapped
            (by rw [HeL1]; omega) (by rw [HeL1, Hmv.2]; omega) Hnemp Henq
          cases ok
          · -- the send failed: lagging
            try wp_auto
            have Hs' := HD2 rfl
            subst Hs'
            imod ghost_map_update { v with phase := .lagging } $$ Hviews Hview with ⟨Hviews, Hview⟩
            wp_apply wp_mapInsert $$ Hlag as Hlag
            wp_apply wp_mapDelete $$ Hm as Hm
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            iframe Hm
            isplitl
            · iexists _, _, GMap.insert key { v with phase := .lagging } views'
              simp only [named]
              iframe
              isplitl [Hres Hview Hwat Huniq]
              · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
                iframe Hres
                iunfold regRes
                iexists _, { v with phase := .lagging }, pred
                simp only [named]
                iframe Hw Hpred Hview Huniq
                isplitl
                · simp only [RegPhase.toWatcher, watcherAt]; iexact Hwat
                ipureintro
                exact Hdel.phase .lagging (fun m h => by cases h)
              isplitl
              · rw [lagOf_insert]; simp only [↓reduceIte]; iexact Hlag
              ipureintro
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [actOf_insert]; simp
              · apply Hok.insert (by rw [Hri]; rfl)
                · intro _; exact Hmv
                · intro h; cases h
              · exact Hrs.insert Hri _ (fun _ => demuxBEL_startOk_active HSO Hvact _)
              · apply demuxBEL_processed_step Hkey Hdone
                · intro w hw; exact GMap.lookup_insert_ne _ _ (Ne.symm hw)
                · intro v' hv' ha
                  rw [GMap.lookup_insert] at hv'; cases hv'; cases ha
            ipureintro; intro k hk
            exact GMap.lookup_delete_ne _ (Ne.symm hk)
          · -- sent: next revision `lastRev + 1`
            try wp_auto
            imod ghost_map_update { v with n := eL.rev + W64 1 } $$ Hviews Hview with ⟨Hviews, Hview⟩
            wp_apply wp_mapInsert $$ Hm as Hm
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            iframe Hm
            isplitl
            · iexists _, _, GMap.insert key { v with n := eL.rev + W64 1 } views'
              simp only [named]
              iframe
              isplitl [Hres Hview Hwat Huniq]
              · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
                iframe Hres
                iunfold regRes
                iexists sent', { v with n := eL.rev + W64 1 }, pred
                simp only [named]
                iframe Hw Hpred Hview Huniq
                isplitl
                · simp only [Hvact, RegPhase.toWatcher, watcherAt]; iexact Hwat
                ipureintro; exact HD1 rfl
              isplitl
              · rw [lagOf_insert]
                simp only [Hvact, reduceCtorEq, ↓reduceIte]
                rw [demuxBEL_delete_none]
                · iexact Hlag
                rw [lagOf_lookup, Hvw]; simp [Hvact]
              ipureintro
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [actOf_insert]; simp [Hvact]
              · apply Hok.insert (by rw [Hri]; rfl)
                · intro _; exact Hmv
                · intro _ b hb
                  have := Hall b (List.mem_of_mem_take hb)
                  simp only; rw [HeL1]; omega
              · exact Hrs.insert Hri _ (fun _ => demuxBEL_startOk_active HSO Hvact _)
              · apply demuxBEL_processed_step Hkey Hdone
                · intro w hw; exact GMap.lookup_insert_ne _ _ (Ne.symm hw)
                · intro v' hv' _ b hb
                  rw [GMap.lookup_insert] at hv'; cases hv'
                  have := Hall b hb
                  simp only; rw [HeL1]; omega
            ipureintro; intro k hk
            exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
        · -- below: next
          wp_for_post
          iframe
          iexists j + W64 1, _, _
          simp only [named]
          iframe
          ipureintro
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          refine ⟨by word, by omega, ?_⟩
          intro t e ht he
          rw [hj1] at ht
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
          · exact Hj.2.2 t e h he
          · subst h; rw [Hej_lookup] at he; cases he; omega
      · -- every event below `nextRev`: nothing to send
        have hfalse : ¬ sint.Z j < sint.Z evSl.len := by
          intro h; apply Hif; first | exact h | simp [h]
        try (rw [decide_eq_false hfalse]
             rw [ite_eq_left_of_eq_true _ _ (by simp)]
             wp_auto)
        have Hjlen : sint.nat j = evs.length := by
          have h1 := HslLen.1; have h2 := HslLen.2
          have := Hj.2.1; word
        have Hbelow : ∀ e ∈ evs, sint.Z e.rev < sint.Z v.n := by
          intro e he
          obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 he
          exact Hj.2.2 t e (by have := (List.getElem?_eq_some_iff.1 ht).1; omega) ht
        have Hfull := demuxBEL_none c.stream (c.stream.take k) evs Hst v.n Hold Hbelow
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl
        · iexists _, _, views'
          simp only [named]
          iframe
          ipureintro
          refine ⟨trivial, Hok, Hrs, ?_⟩
          apply demuxBEL_processed_step Hkey Hdone (fun w _ => rfl)
          intro v' hv' _
          rw [Hvw] at hv'; cases hv'; exact Hfull
        ipureintro; intro k _; rfl
  iintro %m' HP Hm
  iNamed HP
  subst Hm
  wp_auto
  iapply HΦ
  iexists views'
  iunfold demuxLocked
  iexists actP, lagP
  simp only [named]
  iframe
  isplitr
  · iexact Hcerts
  isplitr
  · iexact Hprog
  ipureintro
  refine ⟨demuxBEL_regsOk_full Hok ?_, Hrs⟩
  intro w v hv ha
  exact Hdone w v hv ha (by simp)

end proof

end EtcdGrove
end Perennial
