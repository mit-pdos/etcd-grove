/-
Proof of `Spec/demux__updateStoreLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__updateStoreLocked
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__full
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__PeekOldest
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__Append

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Pure lemmas -/

theorem demuxUSL_take_subslice {α : Type} (evs : List α) {j k : Nat} (hjk : j ≤ k) :
    evs.take k = evs.take j ++ subslice j k evs := by
  rw [subslice_def]
  conv => lhs; rw [← List.take_append_drop j (evs.take k)]
  rw [List.take_take, Nat.min_eq_left hjk]

theorem demuxUSL_mem_subslice {α : Type} {evs : List α} {j k : Nat} {x : α}
    (h : x ∈ subslice j k evs) : ∃ i, j ≤ i ∧ i < k ∧ evs[i]? = some x := by
  rw [subslice_def] at h
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_drop, List.getElem?_take] at hn
  split at hn
  · exact ⟨j + n, by omega, by omega, hn⟩
  · simp at hn

theorem demuxUSL_subslice_head {α : Type} {evs : List α} {j k : Nat} {e0 : α} (hjk : j < k)
    (he0 : evs[j]? = some e0) : subslice j k evs = e0 :: subslice (j + 1) k evs := by
  have hj : j < evs.length := (List.getElem?_eq_some_iff.1 he0).1
  rw [subslice_def, subslice_def]
  have hjt : j < (evs.take k).length := by simp; omega
  rw [List.drop_eq_getElem_cons hjt]
  congr 1
  simp only [List.getElem_take]
  exact (List.getElem?_eq_some_iff.1 he0).2

theorem demuxUSL_sorted_le {evs : List EvModel} (h : EvRevSorted evs) {a b : Nat}
    {x y : EvModel} (hab : a ≤ b) (hx : evs[a]? = some x) (hy : evs[b]? = some y) :
    sint.Z x.rev ≤ sint.Z y.rev := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · unfold EvRevSorted at h
    rw [List.pairwise_iff_getElem] at h
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    exact h a b ha hb hlt
  · have : a = b := by omega
    subst this; rw [hx] at hy; cases hy; exact Int.le_refl _

/-- A run `[j, k)` of revision `e0.rev` starting at a boundary: one more batch. -/
theorem demuxUSL_split_step {evs : List EvModel} {j k : Nat} {e0 : EvModel} (hjk : j < k)
    (he0 : evs[j]? = some e0)
    (hrun : ∀ i e, j ≤ i → i < k → evs[i]? = some e → e.rev = e0.rev)
    (hbd : ∀ x, (evs.take j).getLast? = some x → x.rev ≠ e0.rev) :
    splitBatches (evs.take k) = splitBatches (evs.take j) ++ [subslice j k evs] ∧
      BatchOk (subslice j k evs) ∧ batchRev (subslice j k evs) = e0.rev := by
  have hhead := demuxUSL_subslice_head hjk he0
  have hall : ∀ e ∈ subslice j k evs, e.rev = e0.rev := by
    intro e he
    obtain ⟨i, h1, h2, h3⟩ := demuxUSL_mem_subslice he
    exact hrun i e h1 h2 h3
  have hbr : batchRev (subslice j k evs) = e0.rev := by rw [hhead]; rfl
  refine ⟨?_, ⟨by rw [hhead]; simp, fun e he => by rw [hbr]; exact hall e he⟩, hbr⟩
  rw [demuxUSL_take_subslice evs (Nat.le_of_lt hjk)]
  rw [splitBatches_append _ _ (fun x y hx hy => by
    rw [hhead] at hy; simp at hy; subst hy; exact hbd x hx)]
  rw [splitBatches_run _ (by rw [hhead]; simp) e0.rev hall]

theorem demuxUSL_ringAppend_mem {V : Type} {cap : Nat} {items : List V} {v x : V}
    (h : x ∈ ringAppend cap items v) : x = v ∨ x ∈ items := by
  unfold ringAppend at h
  split at h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_singleton.1 h)
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr (List.mem_of_mem_tail h)
    · exact Or.inl (List.mem_singleton.1 h)

theorem demuxUSL_ringAppend_full {V : Type} {cap : Nat} {items : List V} (v : V)
    (hc : 0 < cap) (h : items.length = cap) : (ringAppend cap items v).length = cap := by
  unfold ringAppend
  rw [ite_eq_right (by omega)]
  simp; omega

theorem demuxUSL_appendAll_snoc (cap : Nat) (h : List Batch) (bs : List Batch) (b : Batch) :
    appendAll cap h (bs ++ [b]) = ringAppend cap (appendAll cap h bs) b := by
  unfold appendAll
  rw [List.foldl_append]
  rfl

theorem demuxUSL_updResp {cap : Nat} {c : DemuxCore} {r : RespModel}
    (hpn : r.isProgressNotify = false) (hne : r.events ≠ []) :
    updResp cap c r = updCore cap c r.events := by
  unfold updResp
  simp [hpn, hne]

/-- The loop's invariant on the run at `j` (up to `k`): event `j` (revision `e0`) starts a run
(a boundary: the event before it has another revision), the events in `[j, k)` have its
revision, and the history so far is below it. -/
def demuxUSL_run (cap : Nat) (c : DemuxCore) (evs : List EvModel) (j k : Nat) : Prop :=
  ∀ e0, evs[j]? = some e0 →
    (∀ i e, j ≤ i → i < k → evs[i]? = some e → e.rev = e0.rev) ∧
    (∀ x, (evs.take j).getLast? = some x → x.rev ≠ e0.rev) ∧
    (∀ x ∈ appendAll cap c.history (splitBatches (evs.take j)),
      sint.Z (batchRev x) < sint.Z e0.rev)

theorem demuxUSL_run_extend {cap : Nat} {c : DemuxCore} {evs : List EvModel} {j k : Nat}
    {e0 e1 : EvModel} (hrun : demuxUSL_run cap c evs j k) (he0 : evs[j]? = some e0)
    (he1 : evs[k]? = some e1) (hr : e1.rev = e0.rev) : demuxUSL_run cap c evs j (k + 1) := by
  intro e0' he0'
  rw [he0] at he0'; cases he0'
  obtain ⟨h1, h2, h3⟩ := hrun e0 he0
  refine ⟨fun i e hi1 hi2 hi3 => ?_, h2, h3⟩
  rcases Nat.lt_or_ge i k with h | h
  · exact h1 i e hi1 h hi3
  · have : i = k := by omega
    subst this; rw [he1] at hi3; cases hi3; exact hr

theorem demuxUSL_getLast_take {α : Type} {l : List α} {k : Nat} (hk0 : 0 < k)
    (hk : k ≤ l.length) : (l.take k).getLast? = l[k - 1]? := by
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk,
    List.getElem?_take_of_lt (by omega)]

theorem demuxUSL_rev_lt {a b : EvModel} (hle : sint.Z a.rev ≤ sint.Z b.rev) (hne : b.rev ≠ a.rev) :
    sint.Z a.rev < sint.Z b.rev := by
  rcases Int.lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (BitVec.eq_of_toInt_eq h.symm) hne

/-- The run `[j, k)` is appended; event `k` starts the next one. -/
theorem demuxUSL_run_new {cap : Nat} {c : DemuxCore} {evs : List EvModel} {j k : Nat}
    {e0 e1 : EvModel} (hjk : j < k) (hrun : demuxUSL_run cap c evs j k)
    (he0 : evs[j]? = some e0) (he1 : evs[k]? = some e1) (hr : e1.rev ≠ e0.rev)
    (hsorted : EvRevSorted evs) :
    appendAll cap c.history (splitBatches (evs.take k)) =
        ringAppend cap (appendAll cap c.history (splitBatches (evs.take j))) (subslice j k evs) ∧
      BatchOk (subslice j k evs) ∧ batchRev (subslice j k evs) = e0.rev ∧
      demuxUSL_run cap c evs k (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := hrun e0 he0
  obtain ⟨hsp, hok, hbr⟩ := demuxUSL_split_step hjk he0 h1 h2
  have hlt : sint.Z e0.rev < sint.Z e1.rev :=
    demuxUSL_rev_lt (demuxUSL_sorted_le hsorted (Nat.le_of_lt hjk) he0 he1) hr
  have happ : appendAll cap c.history (splitBatches (evs.take k)) =
      ringAppend cap (appendAll cap c.history (splitBatches (evs.take j))) (subslice j k evs) := by
    rw [hsp, demuxUSL_appendAll_snoc]
  refine ⟨happ, hok, hbr, ?_⟩
  intro e1' he1'
  rw [he1] at he1'; cases he1'
  refine ⟨fun i e hi1 hi2 hi3 => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have : i = k := by omega
    subst this; rw [he1] at hi3; cases hi3; rfl
  · have hkl : k ≤ evs.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 he1).1
    rw [demuxUSL_getLast_take (by omega) hkl] at hx
    have := h1 (k - 1) x (by omega) (by omega) hx
    rw [this]; exact fun h => hr h.symm
  · rw [happ] at hx
    rcases demuxUSL_ringAppend_mem hx with rfl | hx
    · rw [hbr]; exact hlt
    · have := h3 x hx; omega

/-- The final state, with the last run `b` starting at `j`. -/
theorem demuxUSL_final {cap : Nat} {c : DemuxCore} {r : RespModel} {j : Nat} {b : Batch}
    {el : EvModel} (hpn : r.isProgressNotify = false) (hne : r.events ≠ [])
    (hsplit : splitBatches r.events = splitBatches (r.events.take j) ++ [b])
    (hlast : r.events.getLast? = some el) :
    (updResp cap c r).history =
        ringAppend cap (appendAll cap c.history (splitBatches (r.events.take j))) b ∧
      (updResp cap c r).maxRev = el.rev ∧
      (updResp cap c r).minRev =
        (if (appendAll cap c.history (splitBatches (r.events.take j))).length = cap then
          oldestRev batchRev (appendAll cap c.history (splitBatches (r.events.take j))) + W64 1
        else c.minRev) := by
  rw [demuxUSL_updResp hpn hne]
  unfold updCore
  simp only [hsplit, List.dropLast_concat, hlast]
  refine ⟨demuxUSL_appendAll_snoc _ _ _ _, ?_, ?_⟩ <;> first | rfl | trivial

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- A subslice of a read-only slice of events is the corresponding sublist. -/
theorem demuxUSL_eventsAt_slice (sl : GoSlice) (evs : List EvModel) (low high : w64)
    (hb : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z sl.len) :
    eventsAt (GF := GF) sl evs ⊢
      eventsAt (slice.slice sl Loc low high)
        (subslice (sint.nat low) (sint.nat high) evs) := by
  iintro #H
  iunfold eventsAt at H
  icases H with ⟨%ls, #Hls, %Hlen, #Hev⟩
  icases (ownSlice_slice low high sl DFrac.discard ls hb).1 $$ Hls with ⟨-, #Hmid, -⟩
  iunfold eventsAt
  iexists subslice (sint.nat low) (sint.nat high) ls
  iframe Hmid
  isplitr
  · ipureintro
    simp only [subslice_def, List.length_drop, List.length_take, Hlen]
  imodintro
  iintro %i %ev %e %Hl %He
  simp only [subslice_def, List.getElem?_drop, List.getElem?_take] at Hl He
  split at Hl
  · rename_i hlt
    rw [ite_eq_left hlt] at He
    iapply Hev $$ %(sint.nat low + i) %ev %e %Hl %He
  · simp at Hl

theorem demux.updateStoreLocked.wp_proof
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_full : ringBuffer.full.spec (GF := GF) (hG := hG))
    (wp_PeekOldest : ringBuffer.PeekOldest.spec (GF := GF) (hG := hG))
    (wp_Append : ringBuffer.Append.spec (GF := GF) (hG := hG)) :
    demux.updateStoreLocked.spec (GF := GF) (hG := hG) := by
  intro d cap c resp r
  wp_start as ⟨HminRev, HmaxRev, Hhist, #Hresp, % ⟨Hinv, Hmin0, Hvalid, Hsorted, Hbnd⟩⟩
  wp_auto
  ihave #Hresp' := Hresp
  iunfold respAt at Hresp'
  icases Hresp' with ⟨#HevsAt, #Hhdr, % ⟨Hcomp, Hcanc, Hcre⟩⟩
  wp_apply wp_IsProgressNotify resp_ptr resp r (DFrac.own 1) $$ [resp] as resp
  · iframe resp; iexact Hresp
  cases hpn : r.isProgressNotify
  · wp_auto
    ihave #HevsAt' := HevsAt
    iunfold eventsAt at HevsAt'
    icases HevsAt' with ⟨%ls, #Hls, %Hlslen, #Hev⟩
    ihave %Hsllen := ownSlice_len _ _ _ $$ Hls
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hls
    by_cases he : r.events = []
    · -- no events: nothing changes
      have Hlen0 : resp.Events'.len = W64 0 := by
        have h0 : ls.length = 0 := by rw [Hlslen, he]; rfl
        have h1 := Hsllen.1; have h2 := Hsllen.2
        word
      simp only [Hlen0, _root_.decide_true]
      wp_auto
      iapply HΦ
      have Hu : updResp cap c r = c := by simp [updResp, hpn, he]
      rw [Hu]
      iframe
    have Hlen0 : resp.Events'.len ≠ W64 0 := by
      intro h; apply he
      apply List.eq_nil_of_length_eq_zero
      have h1 := Hsllen.1
      rw [h] at h1
      have : sint.nat (W64 0) = 0 := by word
      omega
    simp only [Hlen0, _root_.decide_false]
    wp_auto
    have Habove : ∀ e ∈ r.events, sint.Z c.maxRev < sint.Z e.rev := by
      simp only [validRevisions, hpn, Bool.false_eq_true, ↓reduceIte, List.all_eq_true,
        decide_eq_true_eq] at Hvalid
      exact Hvalid
    have Hhle : ∀ x ∈ c.history, sint.Z (batchRev x) ≤ sint.Z c.maxRev := fun x hx =>
      Hinv.stream_le x (Hinv.hist_suffix.subset hx)
    have Hlenpos : 0 < r.events.length := by cases h : r.events <;> simp_all
    ihave HI : iprop(∃ (k j mr : w64),
        "Hend" ∷ end_ptr ↦ k ∗
        "batchStart" ∷ batchStart_ptr ↦ j ∗
        "HminRev" ∷ demuxMinRevAddr d ↦ mr ∗
        "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev
          (appendAll cap c.history (splitBatches (r.events.take (sint.nat j)))) ∗
        "%Hidx" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j < sint.Z k ∧ sint.nat k ≤ r.events.length⌝ ∗
        "%Hrun" ∷ ⌜demuxUSL_run cap c r.events (sint.nat j) (sint.nat k)⌝ ∗
        "%Hmr" ∷ ⌜mr = c.minRev ∨
          (appendAll cap c.history (splitBatches (r.events.take (sint.nat j)))).length = cap⌝)
        $$ [«end» batchStart HminRev Hhist]
    · iexists W64 1, W64 0, c.minRev
      simp only [named]
      have h0 : sint.nat (W64 0) = 0 := by word
      rw [h0, List.take_zero]
      iframe
      ipureintro
      refine ⟨⟨by word, by word, by word⟩, ?_, by simp⟩
      intro e0 he0
      refine ⟨fun i e h1 h2 h3 => ?_, fun x hx => by simp at hx, fun x hx => ?_⟩
      · have : i = 0 := by word
        subst this; rw [he0] at h3; cases h3; rfl
      · simp only [appendAll] at hx
        have := Hhle x hx
        have := Habove e0 (List.mem_of_getElem? he0)
        omega
    wp_for HI
    have Hslen : sint.nat resp.Events'.len = r.events.length := by rw [← Hsllen.1, Hlslen]
    wp_if_destruct
    · -- `end < len(events)`
      have Hklt : sint.Z k < sint.Z resp.Events'.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have Hkl : sint.nat k < r.events.length := by word
      have Hjl : sint.nat j < r.events.length := by word
      list_elem ls (sint.nat k) as evp1
      list_elem r.events (sint.nat k) as e1
      list_elem ls (sint.nat j) as evp0
      list_elem r.events (sint.nat j) as e0
      have Hk0 : 0 ≤ sint.Z k := by word
      simp only [Hk0, Hklt, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index resp.Events' (sint.Z k) ls DFrac.discard evp1 Hk0 $$ [] as -
      · iframe Hls; ipureintro; exact Hevp1_lookup
      ihave He1 := Hev $$ %(sint.nat k) %evp1 %e1 %Hevp1_lookup %He1_lookup
      iunfold eventAt at He1
      icases He1 with ⟨%keySl1, #Htyp1, #Hkv1, #Hkey1, #Hks1, #Hmod1⟩
      wp_auto
      have Hjlt : sint.Z j < sint.Z resp.Events'.len := by word
      simp only [Hidx.1, Hjlt, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index resp.Events' (sint.Z j) ls DFrac.discard evp0 Hidx.1 $$ [] as -
      · iframe Hls; ipureintro; exact Hevp0_lookup
      ihave He0 := Hev $$ %(sint.nat j) %evp0 %e0 %Hevp0_lookup %He0_lookup
      iunfold eventAt at He0
      icases He0 with ⟨%keySl0, #Htyp0, #Hkv0, #Hkey0, #Hks0, #Hmod0⟩
      wp_auto
      by_cases hr : e1.rev = e0.rev
      · -- event `end` is in the run
        simp only [hr, decide_true, Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, j, mr
        simp only [named]
        iframe
        ipureintro
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        rw [hk1]
        exact ⟨⟨Hidx.1, by word, by omega⟩, demuxUSL_run_extend Hrun He0_lookup He1_lookup hr, Hmr⟩
      · -- event `end` starts a new run: append the run `[batchStart, end)`
        simp only [hr, decide_false, Bool.not_false]
        wp_auto
        wp_if_destruct
        · -- `end > batchStart`
          generalize Hhistdef : appendAll cap c.history
            (splitBatches (List.take (sint.nat j) r.events)) = hist at Hmr ⊢
          wp_join iprop(∃ mr' : w64, "HminRev" ∷ demuxMinRevAddr d ↦ mr' ∗
              "d" ∷ d_ptr ↦ d ∗
              "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist ∗
              "%Hmr'" ∷ ⌜mr' = c.minRev ∨ hist.length = cap⌝) with [HminRev Hhist d]
            as HR
          · wp_apply wp_full (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
              (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist $$ [$Hhist] as Hhist
            wp_if_destruct
            · wp_apply wp_PeekOldest (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
                (demuxHistAddr d) _ (batchAt (hG := hG)) batchRev hist $$ [$Hhist] as Hhist
              wp_join_done
              iexists _
              iframe
              ipureintro; right; first | trivial | rfl
            · wp_join_done
              iexists mr
              iframe
              ipureintro; exact Hmr
          · iexists mr
            iframe
            ipureintro; exact Hmr
          iNamed HR
          have Hjk : sint.nat j < sint.nat k := by word
          obtain ⟨Happ, Hbok, Hbr, Hrun'⟩ :=
            demuxUSL_run_new Hjk Hrun He0_lookup He1_lookup hr Hsorted
          rw [ite_eq_left ⟨Hidx.1, by word, by word⟩]
          ihave #Hb : batchAt (hG := hG) (slice.slice resp.Events' Loc j k)
              (subslice (sint.nat j) (sint.nat k) r.events) $$ []
          · iunfold batchAt
            isplitl
            · iapply demuxUSL_eventsAt_slice $$ HevsAt; word
            · ipureintro; exact Hbok
          wp_auto
          wp_apply wp_Append (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
            (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist
            (slice.slice resp.Events' Loc j k) (subslice (sint.nat j) (sint.nat k) r.events)
            $$ [$Hhist $Hb] as Hhist
          · ipureintro
            intro last hlast
            rw [Hbr]
            exact (Hrun e0 He0_lookup).2.2 last (by rw [Hhistdef]; exact List.mem_of_getLast? hlast)
          wp_for_post
          iframe
          iexists k + W64 1, k, mr'
          simp only [named]
          rw [Happ, Hhistdef]
          iframe
          ipureintro
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          rw [hk1]
          refine ⟨⟨Hk0, by word, by omega⟩, Hrun', ?_⟩
          rcases Hmr' with h | h
          · exact Or.inl h
          · exact Or.inr (demuxUSL_ringAppend_full _ Hinv.cap_pos h)
        · exfalso; apply Hif; word
    · -- the loop is done: `end = len(events)`; the last run `[batchStart, len)`
      have Hkeq : sint.nat k = r.events.length := by word
      have Hjl : sint.nat j < r.events.length := by word
      list_elem r.events (sint.nat j) as e0
      have Hjlt : sint.Z j < sint.Z resp.Events'.len := by word
      simp only [Hjlt, _root_.decide_true]
      wp_auto
      have Hrun0 := Hrun e0 He0_lookup
      rw [Hkeq] at Hrun0
      obtain ⟨Hsp, Hbok, Hbr⟩ := demuxUSL_split_step (k := r.events.length) Hjl He0_lookup
        Hrun0.1 Hrun0.2.1
      rw [List.take_length] at Hsp
      generalize Hhistdef : appendAll cap c.history
        (splitBatches (List.take (sint.nat j) r.events)) = hist at Hmr Hsp ⊢
      wp_join iprop(∃ mr' : w64, "HminRev" ∷ demuxMinRevAddr d ↦ mr' ∗
          "d" ∷ d_ptr ↦ d ∗
          "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist ∗
          "%Hmr'" ∷ ⌜mr' = if hist.length = cap then oldestRev batchRev hist + W64 1
            else c.minRev⌝) at next with [HminRev Hhist d] as HR
      · wp_apply wp_full (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
          (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist $$ [$Hhist] as Hhist
        by_cases hfull : hist.length = cap
        · simp only [hfull, _root_.decide_true]
          wp_auto
          wp_apply wp_PeekOldest (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
            (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist $$ [$Hhist] as Hhist
          wp_join_done
          iexists _
          iframe
          ipureintro; simp
        · simp only [hfull, _root_.decide_false]
          wp_auto
          wp_join_done
          iexists mr
          iframe
          ipureintro
          simp only [↓reduceIte]
          rcases Hmr with h | h
          · exact h
          · exact absurd h hfull
      iNamed HR
      have Hlenle : sint.Z resp.Events'.len ≤ sint.Z resp.Events'.cap := by
        have := Hwf; word
      rw [ite_eq_left ⟨Hidx.1, by word, Hlenle⟩]
      ihave #Hb : batchAt (hG := hG) (slice.slice resp.Events' Loc j resp.Events'.len)
          (subslice (sint.nat j) r.events.length r.events) $$ []
      · iunfold batchAt
        isplitl
        · rw [← Hslen]
          iapply demuxUSL_eventsAt_slice $$ HevsAt; word
        · ipureintro; exact Hbok
      wp_auto
      wp_apply wp_Append (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
        (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev hist
        (slice.slice resp.Events' Loc j resp.Events'.len)
        (subslice (sint.nat j) r.events.length r.events) $$ [$Hhist $Hb] as Hhist
      · ipureintro
        intro last hlast
        rw [Hbr]
        exact Hrun0.2.2 last (by rw [Hhistdef]; exact List.mem_of_getLast? hlast)
      have Hl1 : 0 ≤ sint.Z (resp.Events'.len - W64 1) ∧
          sint.Z (resp.Events'.len - W64 1) < sint.Z resp.Events'.len := by word
      simp only [Hl1, _root_.and_self, ↓reduceIte]
      have Hl1n : sint.nat (resp.Events'.len - W64 1) = r.events.length - 1 := by word
      list_elem ls (r.events.length - 1) as evpl
      list_elem r.events (r.events.length - 1) as el
      wp_apply wp_load_slice_index resp.Events' (sint.Z (resp.Events'.len - W64 1)) ls DFrac.discard
        evpl Hl1.1 $$ [] as -
      · iframe Hls; ipureintro
        have : (sint.Z (resp.Events'.len - W64 1)).toNat = r.events.length - 1 := by word
        rw [this] <;> exact Hevpl_lookup
      ihave Hel := Hev $$ %(r.events.length - 1) %evpl %el %Hevpl_lookup %Hel_lookup
      iunfold eventAt at Hel
      icases Hel with ⟨%keySll, #Htypl, #Hkvl, #Hkeyl, #Hksl, #Hmodl⟩
      wp_auto
      have Hlast : r.events.getLast? = some el := by
        rw [List.getLast?_eq_getElem?]; exact Hel_lookup
      obtain ⟨Hfh, Hfm, Hfmin⟩ := demuxUSL_final (cap := cap) (c := c) hpn he
        (by rw [Hsp]) Hlast
      iapply HΦ
      rw [Hfh, Hfm, Hfmin, Hhistdef, Hmr']
      iframe
  · -- a progress notification: `maxRev` becomes the header's revision
    have hhr : r.hdrRev ≠ W64 0 := by
      simp only [RespModel.isProgressNotify, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hpn
      exact hpn.2
    iunfold hdrAt at Hhdr
    icases Hhdr with (%Hnil | ⟨%Hnn, #Hh⟩)
    · exact absurd Hnil.2 hhr
    wp_auto
    iapply HΦ
    have Hu : updResp cap c r = { c with maxRev := r.hdrRev } := by simp [updResp, hpn]
    rw [Hu]
    iframe

end proof

end EtcdGrove
end Perennial
