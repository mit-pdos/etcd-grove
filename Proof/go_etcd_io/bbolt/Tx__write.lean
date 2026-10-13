module
public import Spec.go_etcd_io.bbolt.Tx__write
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.sort.Sort_w
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Spec.os.File__WriteAt
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.sync.Pool__Put
public import Proof.go_etcd_io.bbolt.DBAcc
public import Proof.go_etcd_io.bbolt.DBFree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-! ### The dirty pages as a list, and the bytes of the file -/

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A dirty page: its id, its buffer and the buffer's bytes. -/
structure DPg where
  id : w64
  l : Loc
  b : List w8

/-- A dirty page's first slot and number of slots. -/
def DPg.run (e : DPg) : Nat × Nat := (uint.nat e.id, dspan e.b)

/-- `n` bytes of `F` from `a`. -/
abbrev seg (F : List w8) (a n : Nat) : List w8 := (F.drop a).take n

theorem seg_length (F : List w8) (a n : Nat) (h : a + n ≤ F.length) : (seg F a n).length = n := by
  unfold seg; simp only [List.length_take, List.length_drop]; omega

theorem seg_add (F : List w8) (a x y : Nat) : seg F a (x + y) = seg F a x ++ seg F (a + x) y := by
  unfold seg; rw [List.take_add, List.drop_drop]

theorem seg_congr (F F' : List w8) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → F'[i]? = F[i]?) :
    seg F' a n = seg F a n := by
  apply List.ext_getElem?; intro i
  unfold seg
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos hi]; exact h _ (by omega) (by omega)
  · rw [if_neg hi, if_neg hi]

theorem seg_write (F : List w8) (o : Nat) (d : List w8) (h : o + d.length ≤ F.length) :
    seg (writeBytes F o d) o d.length = d := by
  apply seg_ext _ _ _ _ rfl (by rw [writeBytes_length_in F o d h]; exact h)
  intro i hi
  rw [writeBytes_get F o d h, if_pos (by omega), show o + i - o = i by omega]

theorem writeBytes_out (F : List w8) (o : Nat) (d : List w8) (h : o + d.length ≤ F.length) (i : Nat)
    (hi : i < o ∨ o + d.length ≤ i) : (writeBytes F o d)[i]? = F[i]? := by
  rw [writeBytes_get F o d h, if_neg (by omega)]

/-- A page buffer's bytes up to `w + k`: those up to `w` and `k` more. -/
theorem take_add_chunk (b : List w8) (w k : Nat) : b.take (w + k) = b.take w ++ (b.drop w).take k := by
  rw [List.take_add]

theorem ids_ne (L : List DPg) (h : (L.map DPg.id).Nodup) (m j : Nat) (e1 e2 : DPg)
    (h1 : L[m]? = some e1) (h2 : L[j]? = some e2) (hne : m ≠ j) : e1.id ≠ e2.id := by
  intro e
  have hm : m < (L.map DPg.id).length := by
    simp only [List.length_map]; exact (List.getElem?_eq_some_iff.1 h1).1
  have : (L.map DPg.id)[m]? = (L.map DPg.id)[j]? := by
    rw [List.getElem?_map, List.getElem?_map, h1, h2]; simp [e]
  exact hne ((List.Nodup.getElem?_inj hm h).1 this)

theorem pairwise_of_ids (L : List DPg) (h : (L.map DPg.id).Nodup) (R : DPg → DPg → Prop)
    (hR : ∀ e1 ∈ L, ∀ e2 ∈ L, e1.id ≠ e2.id → R e1 e2) : L.Pairwise R := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons e L ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    refine List.pairwise_cons.2 ⟨fun e' he' => hR e List.mem_cons_self e' (List.mem_cons_of_mem _ he')
      (fun hid => h.1 (by rw [hid]; exact List.mem_map_of_mem he')), ih h.2 (fun a ha b hb => hR a
        (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩

/-- The page cache has fewer pages than the mapping has slots. -/
theorem pm_size (σ : DBState) (T : WTx) (hd : dirtyOK σ T)
    (hb : ∀ id p, T.pm !! id = some p → ∃ b, T.bufs !! id = some b) (hlen : σ.bs.length < 2 ^ 62) :
    GMap.size T.pm < 2 ^ 62 := by
  have hns : σ.nslots ≤ σ.bs.length := by
    unfold DBState.nslots
    exact Nat.le_trans (Nat.div_le_self _ _) (Nat.min_le_right _ _)
  have := nodup_length_le (T.pm.toList.map Prod.fst) σ.nslots (GMap.toList_keys_nodup T.pm) (by
    intro x hx
    obtain ⟨⟨x', v⟩, hxv, rfl⟩ := List.mem_map.1 hx
    have hl : T.pm !! x' = some v := (GMap.mem_toList T.pm x' v).1 hxv
    obtain ⟨b, hbb⟩ := hb x' v hl
    have h1 := ((hd.1 x' b (by rw [hl]; rfl) hbb).2.2 0 (by unfold dspan; omega)).1
    simp only
    have : (uint.nat x' : Int) = uint.Z x' := by unfold uint.nat; word
    omega)
  rw [List.length_map] at this
  show T.pm.toList.length < 2 ^ 62
  omega

theorem nodup_not_mem_take {α : Type} (l : List α) (n : Nat) (k : α) (hnd : l.Nodup)
    (hk : l[n]? = some k) : k ∉ l.take n := by
  intro hm
  obtain ⟨hn, hkk⟩ := List.getElem?_eq_some_iff.1 hk
  have hd : k ∈ l.drop n := by rw [List.drop_eq_getElem_cons hn, hkk]; exact List.mem_cons_self
  have := List.nodup_append.1 (show (l.take n ++ l.drop n).Nodup by rw [List.take_append_drop]; exact hnd)
  exact this.2.2 k hm k hd rfl

/-- The list `L` holds the page cache's pages, each once. -/
def listOK (T : WTx) (L : List DPg) : Prop :=
  (∀ e ∈ L, T.pm !! e.id = some e.l ∧ T.bufs !! e.id = some e.b) ∧
  (∀ id, (T.pm !! id).isSome → ∃ e ∈ L, e.id = id) ∧ (L.map DPg.id).Nodup

theorem listOK_perm (T : WTx) (L L' : List DPg) (hp : L'.Perm L) (h : listOK T L) : listOK T L' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e he => h1 e (hp.mem_iff.1 he), fun id hid => ?_, (hp.map DPg.id).nodup_iff.2 h3⟩
  obtain ⟨e, he, rfl⟩ := h2 id hid
  exact ⟨e, hp.mem_iff.2 he, rfl⟩

theorem listOK_page (σ : DBState) (T : WTx) (L : List DPg) (h : listOK T L) (hd : dirtyOK σ T)
    (e : DPg) (he : e ∈ L) :
    e.b.length = dspan e.b * σ.ps ∧ pageId e.b = uint.nat e.id ∧
      uint.nat e.id + dspan e.b ≤ σ.nslots ∧ ∀ k < dspan e.b, slotUnseen σ (uint.nat e.id + k) := by
  obtain ⟨h1, h2⟩ := h.1 e he
  obtain ⟨hl, hid, hk⟩ := hd.1 e.id e.b (by rw [h1]; rfl) h2
  refine ⟨hl, hid, ?_, fun k hk' => (hk k hk').2⟩
  have := (hk (dspan e.b - 1) (by unfold dspan; omega)).1
  unfold dspan at this ⊢; omega

theorem listOK_dirty (T : WTx) (L : List DPg) (h : listOK T L) (s : Nat) :
    dirtySlot T s ↔ inRuns (L.map DPg.run) s := by
  constructor
  · rintro ⟨id, b, hp, hb, h1, h2⟩
    obtain ⟨e, he, rfl⟩ := h.2.1 id hp
    have := (h.1 e he).2
    rw [hb] at this; cases this
    exact ⟨e.run, List.mem_map_of_mem he, h1, h2⟩
  · rintro ⟨r, hr, h1, h2⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hp, hb⟩ := h.1 e he
    exact ⟨e.id, e.b, by rw [hp]; rfl, hb, h1, h2⟩

theorem listOK_disj (σ : DBState) (T : WTx) (L : List DPg) (h : listOK T L) (hd : dirtyOK σ T)
    (e1 e2 : DPg) (h1 : e1 ∈ L) (h2 : e2 ∈ L) (hne : e1.id ≠ e2.id) :
    uint.nat e1.id + dspan e1.b ≤ uint.nat e2.id ∨ uint.nat e2.id + dspan e2.b ≤ uint.nat e1.id := by
  obtain ⟨p1, b1⟩ := h.1 e1 h1
  obtain ⟨p2, b2⟩ := h.1 e2 h2
  exact hd.2 e1.id e1.b e2.id e2.b (by rw [p1]; rfl) b1 (by rw [p2]; rfl) b2 hne

theorem listOK_pw (σ : DBState) (T : WTx) (L : List DPg) (h : listOK T L) (hd : dirtyOK σ T) :
    L.Pairwise (fun e1 e2 => uint.nat e1.id + dspan e1.b ≤ uint.nat e2.id ∨
      uint.nat e2.id + dspan e2.b ≤ uint.nat e1.id) :=
  pairwise_of_ids L h.2.2 _ (fun e1 h1 e2 h2 hne => listOK_disj σ T L h hd e1 e2 h1 h2 hne)

/-- Two dirty pages at distinct positions of the list have disjoint bytes. -/
theorem listOK_bytes (σ : DBState) (T : WTx) (L : List DPg) (h : listOK T L) (hd : dirtyOK σ T)
    (m j : Nat) (e1 e2 : DPg) (h1 : L[m]? = some e1) (h2 : L[j]? = some e2) (hne : m ≠ j) :
    uint.nat e1.id * σ.ps + e1.b.length ≤ uint.nat e2.id * σ.ps ∨
      uint.nat e2.id * σ.ps + e2.b.length ≤ uint.nat e1.id * σ.ps := by
  have hm1 := List.mem_of_getElem? h1
  have hm2 := List.mem_of_getElem? h2
  rw [(listOK_page σ T L h hd e1 hm1).1, (listOK_page σ T L h hd e2 hm2).1]
  rcases listOK_disj σ T L h hd e1 e2 hm1 hm2 (ids_ne L h.2.2 m j e1 e2 h1 h2 hne) with h | h
  · left; have := Nat.mul_le_mul_right σ.ps h; rw [Nat.add_mul] at this; exact this
  · right; have := Nat.mul_le_mul_right σ.ps h; rw [Nat.add_mul] at this; exact this

/-- A dirty slot is the database's whole half (no view takes a part of it). -/
theorem rem_dirty (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1) (T : WTx)
    (hd : dirtyOK σ T) (s : Nat) (hs : dirtySlot T s) : σ.rem s = halfQ := by
  obtain ⟨hlt, -, hr, hw, -⟩ := dirty_unseen σ T hd s hs
  have H := h.2.2.2.2.2.2.2.2.2.2.2.1 s hlt
  have hn : readersQ σ.readers (fun r => r.sees s) = none :=
    readersQ_none _ _ (fun k r hk => by
      unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hr k r hk)
  rw [hn] at H
  unfold wQ at H
  cases hwr : σ.wr with
  | none => rw [hwr] at H; exact H
  | some w' =>
    rw [hwr] at H
    have : w'.sees s = false := by
      unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hw w' hwr
    simp only [this, Bool.false_eq_true, ↓reduceIte] at H
    exact H

/-- The file during the writes, before page `j` of the sorted list: the same length, the bytes
of no dirty page unchanged, the pages before `j` written. -/
def outerOK (L : List DPg) (ps : Nat) (bs F : List w8) (j : Nat) : Prop :=
  F.length = bs.length ∧
  (∀ i, (∀ e ∈ L, ¬ (uint.nat e.id * ps ≤ i ∧ i < uint.nat e.id * ps + e.b.length)) → F[i]? = bs[i]?) ∧
  ∀ m e, m < j → L[m]? = some e → seg F (uint.nat e.id * ps) e.b.length = e.b

/-- The file while page `c` is written: the same length, the bytes outside `c` those of `Fj`
(the file before `c`), the first `w` bytes of `c` written. -/
def innerOK (c : DPg) (ps : Nat) (Fj F : List w8) (w : Nat) : Prop :=
  F.length = Fj.length ∧
  (∀ i, ¬ (uint.nat c.id * ps ≤ i ∧ i < uint.nat c.id * ps + c.b.length) → F[i]? = Fj[i]?) ∧
  seg F (uint.nat c.id * ps) w = c.b.take w

/-- A byte of slot `s` is in a run of slots only if `s` is. -/
theorem byte_in_run (ps s i a d : Nat) (hi : i < ps)
    (h1 : a * ps ≤ s * ps + i) (h2 : s * ps + i < a * ps + d * ps) : a ≤ s ∧ s < a + d := by
  constructor
  · by_cases hc : a ≤ s
    · exact hc
    · have : (s + 1) * ps ≤ a * ps := Nat.mul_le_mul_right ps (by omega)
      rw [Nat.add_mul] at this; omega
  · by_cases hc : s < a + d
    · exact hc
    · have : (a + d) * ps ≤ s * ps := Nat.mul_le_mul_right ps (by omega)
      rw [Nat.add_mul] at this; omega

/-- The file after the writes differs from `bs` only in dirty slots. -/
theorem dirtyOnly_of (T : WTx) (L : List DPg) (ps : Nat) (hL : listOK T L) (bs F : List w8)
    (hlen : F.length = bs.length)
    (hout : ∀ i, (∀ e ∈ L, ¬ (uint.nat e.id * ps ≤ i ∧ i < uint.nat e.id * ps + e.b.length)) →
      F[i]? = bs[i]?)
    (hlenb : ∀ e ∈ L, e.b.length = dspan e.b * ps) : dirtyOnly T ps bs F := by
  refine ⟨hlen, fun s hs => ?_⟩
  apply List.ext_getElem?; intro i
  unfold slotAt
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  by_cases hi : i < ps
  · rw [if_pos hi, if_pos hi]
    apply hout
    intro e he ⟨h1, h2⟩
    rw [hlenb e he] at h2
    obtain ⟨h3, h4⟩ := byte_in_run ps s i _ _ hi h1 h2
    exact hs ((listOK_dirty T L hL s).2 ⟨e.run, List.mem_map_of_mem he, h3, h4⟩)
  · rw [if_neg hi, if_neg hi]

/-- The bytes after the whole slots are unchanged. -/
theorem tail_of (L : List DPg) (ps N sz : Nat) (bs F : List w8) (hlen : F.length = bs.length)
    (hout : ∀ i, (∀ e ∈ L, ¬ (uint.nat e.id * ps ≤ i ∧ i < uint.nat e.id * ps + e.b.length)) →
      F[i]? = bs[i]?)
    (hin : ∀ e ∈ L, uint.nat e.id * ps + e.b.length ≤ N) :
    (F.take sz).drop N = (bs.take sz).drop N := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_take, List.getElem?_take]
  by_cases hi : N + i < sz
  · rw [if_pos hi, if_pos hi]
    exact hout _ (fun e he h => by have := hin e he; omega)
  · rw [if_neg hi, if_neg hi]

theorem dirtyAll_of (T : WTx) (L : List DPg) (ps : Nat) (hL : listOK T L) (F : List w8)
    (h : ∀ e ∈ L, seg F (uint.nat e.id * ps) e.b.length = e.b) : dirtyAll T ps F := by
  intro id b hp hb
  obtain ⟨e, he, rfl⟩ := hL.2.1 id hp
  have := (hL.1 e he).2
  rw [hb] at this; cases this
  exact h e he

theorem rem_val (ov ps n : Nat) (hov : ov < 2 ^ 32) (hn : n = (1 + ov) * ps) :
    (W64 (uint.Z (W32 (ov : Int))) + W64 1) * W64 (ps : Int) = W64 (n : Int) := by
  have h1 : uint.Z (W32 (ov : Int)) = ov := by word
  rw [h1, ← BitVec.ofInt_add, ← BitVec.ofInt_mul, hn]
  congr 1
  push_cast
  rw [Int.add_comm]

theorem off_val (id : w64) (ps : Nat) :
    W64 ((uint.nat id : Nat) : Int) * W64 (ps : Int) = W64 ((uint.nat id * ps : Nat) : Int) := by
  rw [← BitVec.ofInt_mul]; push_cast; rfl

theorem pageOverflow_lt (b : List w8) : pageOverflow b < 2 ^ 32 := by
  have := leAt_lt b 12 4; unfold pageOverflow; simpa using this

theorem set_self {α : Type} (L : List α) (j : Nat) (c : α) (h : L[j]? = some c) : L.set j c = L := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_set]
  by_cases hij : j = i
  · subst hij; rw [if_pos rfl, h]
    rw [if_pos (List.getElem?_eq_some_iff.1 h).1]
  · rw [if_neg hij]

theorem mem_split_idx {α : Type} (L : List α) (j : Nat) (e : α) (he : e ∈ L.take j ∨ e ∈ L.drop (j + 1)) :
    ∃ m, m ≠ j ∧ L[m]? = some e := by
  rcases he with he | he
  · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 he
    rw [List.getElem?_take] at hm
    by_cases hmj : m < j
    · rw [if_pos hmj] at hm; exact ⟨m, by omega, hm⟩
    · rw [if_neg hmj] at hm; cases hm
  · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 he
    rw [List.getElem?_drop] at hm
    exact ⟨j + 1 + m, by omega, hm⟩

/-- The bytes of another dirty page than `c` are outside `c`'s. -/
theorem other_bytes (σ : DBState) (T : WTx) (L : List DPg) (h : listOK T L) (hd : dirtyOK σ T)
    (j : Nat) (c : DPg) (hc : L[j]? = some c) (e : DPg) (he : e ∈ L.take j ∨ e ∈ L.drop (j + 1))
    (i : Nat) (hi : uint.nat e.id * σ.ps ≤ i ∧ i < uint.nat e.id * σ.ps + e.b.length) :
    ¬ (uint.nat c.id * σ.ps ≤ i ∧ i < uint.nat c.id * σ.ps + c.b.length) := by
  obtain ⟨m, hm, hme⟩ := mem_split_idx L j e he
  have := listOK_bytes σ T L h hd m j e c hme hc hm
  omega

theorem chunk_take (b : List w8) (w cs k : Nat) (hk : k ≤ cs) :
    (bytesAt b w cs).take k = (b.drop w).take k := by
  unfold bytesAt; rw [List.take_take, Nat.min_eq_left hk]

theorem sub_val (r cs : Nat) (h : cs ≤ r) (hr : r < 2 ^ 62) :
    W64 (r : Int) - W64 (cs : Int) = W64 ((r - cs : Nat) : Int) := by word

theorem w64_eq0 (x : Nat) (hx : x < 2 ^ 62) (h : W64 (x : Int) = W64 0) : x = 0 := by word

theorem add_val (a b : Nat) (h : a + b < 2 ^ 62) :
    W64 (a : Int) + W64 (b : Int) = W64 ((a + b : Nat) : Int) := by word

theorem cs_lt (a : Nat) (h : uint.Z (W64 2147483646) < uint.Z (W64 (a : Int))) (ha : a < 2 ^ 62) :
    2147483646 < a := by word

theorem cs_ge (a : Nat) (h : ¬ uint.Z (W64 2147483646) < uint.Z (W64 (a : Int))) (ha : a < 2 ^ 62) :
    ¬ 2147483646 < a := by word

theorem zero_step (b : List w8) (k : Nat) (hk : k < b.length) :
    (List.replicate k (W8 0) ++ b.drop k).set k (W8 0) = List.replicate (k + 1) (W8 0) ++ b.drop (k + 1) := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_set]
  have hl : (List.replicate k (W8 0) ++ b.drop k).length = b.length := by simp; omega
  by_cases hik : k = i
  · subst hik
    rw [if_pos rfl, if_pos (by rw [hl]; exact hk), List.getElem?_append_left (by simp)]
    simp
  · rw [if_neg hik]
    by_cases hi : i < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
      simp [hi, show i < k + 1 by omega]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getElem?_drop]
      congr 1; omega

end pure

/-! ### The mapped cells of the dirty pages -/

section cells
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The database's half of the mapped cells of a dirty page's slots, in the file `F`. -/
def win (data : Loc) (ps : Nat) (F : List w8) (e : DPg) : IProp GF :=
  bytesPointsto (data +ₗ ((uint.nat e.id * ps : Nat) : Int)) (DFrac.own halfQ)
    (seg F (uint.nat e.id * ps) e.b.length)

open Classical in
/-- The database's slots: those of no dirty page, and the dirty pages' (whose slots it holds at
half: no view takes a part of them). -/
theorem slots_wins (data : Loc) (F : List w8) (ps : Nat) (rem : Nat → Qp) (n : Nat)
    (L : List DPg) (S : Nat → Prop)
    (hS : ∀ s < n, (S s ↔ inRuns (L.map DPg.run) s)) (hrem : ∀ s < n, S s → rem s = halfQ)
    (hfit : n * ps ≤ F.length) (hin : ∀ e ∈ L, uint.nat e.id + dspan e.b ≤ n)
    (hpw : L.Pairwise (fun e1 e2 => uint.nat e1.id + dspan e1.b ≤ uint.nat e2.id ∨
      uint.nat e2.id + dspan e2.b ≤ uint.nat e1.id))
    (hlen : ∀ e ∈ L, e.b.length = dspan e.b * ps) :
    slotsView (GF := GF) data F ps rem (List.range n) ⊣⊢
      cellsOut data F ps rem S n ∗ [∗list] e ∈ L, win data ps F e := by
  refine (slots_out data F ps rem S n hrem).trans (sep_congr .rfl ?_)
  refine (cellsIf_ext data F ps halfQ _ _ n hS).trans ?_
  refine (cellsIf_runs data F ps halfQ n hfit (L.map DPg.run) ?_ ?_).trans ?_
  · intro r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
    exact hin e he
  · rw [List.pairwise_map]; exact hpw
  refine (BIBase.BiEntails.of_eq (BigSepL.bigSepL_map (PROP := IProp GF) DPg.run)).trans ?_
  refine bigSepL_congr_mem fun _ e he => ?_
  unfold win runBytes DPg.run
  simp only
  rw [hlen e he]
  exact .rfl

/-- A page buffer's header, lent out. -/
theorem hdr_split (l : Loc) (q : DFrac) (b : List w8) (h : 16 ≤ b.length) :
    bytesPointsto (GF := GF) l q b ⊢
      l ↦{q} pageOf b ∗ (l ↦{q} pageOf b -∗ bytesPointsto l q b) := by
  have hne : b ≠ [] := List.ne_nil_of_length_pos (by omega)
  iintro H
  icases persistent_entails_left (bytesPointsto_car l q b hne) $$ H with ⟨H, %hc⟩
  icases (page_header_bytes (hG := hG) l q b h hc).1 $$ H with ⟨Hh, Hr⟩
  iframe Hh
  iintro Hh
  iapply (page_header_bytes (hG := hG) l q b h hc).2
  iframe

/-- Three consecutive parts of `n` bytes of `F`. -/
theorem seg3 (data : Loc) (q : DFrac) (F : List w8) (a x y z : Nat) (h : a + x + y + z ≤ F.length) :
    bytesPointsto (GF := GF) (data +ₗ (a : Int)) q (seg F a (x + y + z)) ⊣⊢
      bytesPointsto (data +ₗ (a : Int)) q (seg F a x) ∗
      bytesPointsto (data +ₗ ((a + x : Nat) : Int)) q (seg F (a + x) y) ∗
      bytesPointsto (data +ₗ ((a + x + y : Nat) : Int)) q (seg F (a + x + y) z) := by
  rw [show x + y + z = x + (y + z) by omega, seg_add, seg_add F (a + x)]
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
  rw [seg_length F a x (by omega), loc_add_assoc, show (a : Int) + (x : Int) = ((a + x : Nat) : Int) by omega]
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
  rw [seg_length F (a + x) y (by omega), loc_add_assoc,
    show ((a + x : Nat) : Int) + (y : Int) = ((a + x + y : Nat) : Int) by omega]
  exact .rfl

/-- The caller's half of the mapped cells of `[o, o + n)`, inside the mapping. -/
theorem mapRange_eq_seg (data : Loc) (sz : Nat) (F : List w8) (o n : Nat) (h : o + n ≤ sz) :
    mapRange (GF := GF) (some (data, sz)) F o (o + n) =
      bytesPointsto (data +ₗ (o : Int)) (DFrac.own halfQ) (seg F o n) := by
  unfold mapRange
  simp only
  rw [mapRange_seg F sz o (o + n) h, show o + n - o = n by omega]
  rfl

/-- The page cache's buffers are the transaction's dirty bytes. -/
theorem bufs_dom (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) :
    ([∗map] id ↦ p ∈ pm, ∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto (GF := GF) p (DFrac.own 1) bs) ⊢
      ⌜∀ id p, pm !! id = some p → ∃ b, bufs !! id = some b⌝ := by
  have H : ∀ {k : w64} {v : Loc}, Std.get? pm k = some v →
      (iprop(∃ bs, ⌜bufs !! k = some bs⌝ ∗ bytesPointsto (GF := GF) v (DFrac.own 1) bs) ⊢
        (⌜∃ b, bufs !! k = some b⌝ : IProp GF)) := by
    intro k v _; iintro ⟨%b, %h, -⟩; ipureintro; exact ⟨b, h⟩
  refine (BigSepM.bigSepM_mono H).trans (BigSepM.bigSepM_pure_intro.trans ?_)
  iintro %h; ipureintro; exact fun id p hp => h id p hp

/-- The pages' headers, lent out (for the sort). -/
theorem hdrs_split (L : List DPg) (h : ∀ e ∈ L, 16 ≤ e.b.length) :
    ([∗list] e ∈ L, bytesPointsto (GF := GF) e.l (DFrac.own 1) e.b) ⊢
      ([∗list] e ∈ L, e.l ↦ pageOf e.b) ∗
        ([∗list] e ∈ L, (e.l ↦ pageOf e.b -∗ bytesPointsto (GF := GF) e.l (DFrac.own 1) e.b)) :=
  (BigSepL.bigSepL_mono (fun {_ e} hk =>
    hdr_split (GF := GF) e.l (DFrac.own 1) e.b (h e (List.mem_of_getElem? hk)))).trans
    BigSepL.bigSepL_sep_eqv.1

theorem hdrs_join (L : List DPg) :
    ([∗list] e ∈ L, e.l ↦ pageOf e.b) ∗
        ([∗list] e ∈ L, (e.l ↦ pageOf e.b -∗ bytesPointsto (GF := GF) e.l (DFrac.own 1) e.b)) ⊢
      [∗list] e ∈ L, bytesPointsto (GF := GF) e.l (DFrac.own 1) e.b := by
  refine BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono (fun _ => ?_))
  iintro ⟨H, Hw⟩; iapply Hw $$ H

theorem sepL_at {A : Type} (L : List A) (j : Nat) (c : A) (hc : L[j]? = some c) (Φ : A → IProp GF) :
    ([∗list] e ∈ L, Φ e) ⊣⊢ ([∗list] e ∈ L.take j, Φ e) ∗ Φ c ∗ [∗list] e ∈ L.drop (j + 1), Φ e := by
  obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.1 hc
  have hL : L = L.take j ++ c :: L.drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop j L, List.drop_eq_getElem_cons hj, hcj]
  refine (BIBase.BiEntails.of_eq (congrArg (fun l => [∗list] e ∈ l, Φ e) hL)).trans ?_
  exact BigSepL.bigSepL_append.trans (sep_congr .rfl BigSepL.bigSepL_cons)

/-- The windows of pages whose bytes agree in two files. -/
theorem wins_congr (data : Loc) (ps : Nat) (F F' : List w8) (M : List DPg)
    (h : ∀ e ∈ M, ∀ i, uint.nat e.id * ps ≤ i → i < uint.nat e.id * ps + e.b.length → F'[i]? = F[i]?) :
    ([∗list] e ∈ M, win (GF := GF) data ps F e) ⊣⊢ [∗list] e ∈ M, win data ps F' e := by
  refine bigSepL_congr_mem fun _ e he => ?_
  unfold win; rw [seg_congr F F' _ _ (h e he)]; exact .rfl

end cells

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [linux : GOOSLinux]

set_option maxHeartbeats 1600000 in
theorem Tx.write.wp_wproof
    (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG))
    (hSort : sort.Sort.wspec (GF := GF) (hG := hG))
    (hOv : Page.Overflow.spec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hUBS : UnsafeByteSlice.spec (GF := GF) (hG := hG))
    (hWA : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG))
    (hfds : _root_.Perennial.EtcdGrove.bbolt.fdatasync.spec (GF := GF) (hG := hG))
    (hPut : sync.Pool.Put.spec (GF := GF) (hG := hG)) :
    Tx.write.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl txid σ T Hdirty Htdb Hps31
  wp_start as ⟨HR, HG, Hv⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  isimp only [dbWR] at HR
  icases HR with ⟨Hown, %Hf⟩
  obtain ⟨HAS, Hrw, Hdata, Hps, Hfli, w, Hw, Hwp, Hwq, Hwh, Htxw, Htxb⟩ := Hf
  icases ownDB_logger I W.dbl γ σ $$ Hown with ⟨%lg, %dl, #Hlg2, #Hdl2, #Hdlok0, %Hlgf, Hown⟩
  isimp only [ownDB] at Hown
  iNamed Hown
  irename Hstats => Hdbstats
  irename Hdl => Hdl0
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  unfold ownWriteTxG
  icases HG with ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hwritable, Hmanaged, Hdbf, Hmetaf, Hpages, Hstats, Hch, Hwf, %Htxn⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdatav, #Hps', #Hlg, Hfliv, #Hdl, %Hlgv, Hpv⟩
  icombine Hdl Hdl2 gives %Hdle
  subst Hdle
  rw [Htdb]
  wp_auto
  wp_apply hLog W.dbl DFrac.discard W.lg W.dl Hlgf.2 $$ [Hlg Hdl] as Hlg'
  · iframe #
  have Hd : (if W.lg = interface.nil then discardIface W.dl else W.lg) = discardIface W.dl := by
    rcases Hlgv with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  -- the dirty pages' bytes, and the page cache's size
  icases persistent_entails_left (bufs_dom (GF := GF) T.pm T.bufs) $$ Hbufs with ⟨Hbufs, %Hpb⟩
  have Hok' := Hok
  obtain ⟨Hps80, Hps32, Hns2, ⟨Hsz48, Hbs62⟩, Hdc, -⟩ := Hok'
  have Hsize := pm_size σ T Hdirty Hpb Hbs62
  wp_apply wp_map_len T.t.pages' T.pm (DFrac.own 1) $$ [Hpm] as Hpm
  · iframe
  wp_apply wp_slice_make3 (V := Loc) (W64 0) (W64 (GMap.size T.pm : Int)) ⟨by word, by word⟩
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  try wp_auto
  -- the page cache's pages, collected in a slice
  irename : (pages_ptr ↦ sl0 : IProp GF) => Hpgs
  irename : (p_ptr ↦ (null : Loc) : IProp GF) => Hpv0
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (L : List DPg)
      (R : GMap w64 Loc) (pv : Loc),
      "Hpgs" ∷ pages_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* L.map DPg.l ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "Hpv" ∷ p_ptr ↦ pv ∗
      "%HL" ∷ ⌜0 ≤ i ∧ L.map DPg.id = keys.take i.toNat ∧
        (∀ e ∈ L, T.pm !! e.id = some e.l ∧ T.bufs !! e.id = some e.b) ∧
        (∀ id, R !! id = if id ∈ keys.take i.toNat then none else T.pm !! id)⌝ ∗
      "HR" ∷ ([∗map] id ↦ p ∈ R, ∃ bs, ⌜T.bufs !! id = some bs⌝ ∗ bytesPointsto p (DFrac.own 1) bs) ∗
      "HLb" ∷ [∗list] e ∈ L, bytesPointsto e.l (DFrac.own 1) e.b)) $$ Hpm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpgs Hsl0 Hcap0 Hpv0 Hbufs]
  · iexists sl0, [], T.pm, null
    iframe
    isplitr
    · ipureintro
      simp
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨Hi0, HLid, HLmem, HRl⟩ := HL
    have Hnin : key ∉ keys.take i.toNat := nodup_not_mem_take keys i.toNat key Hknodup Hkey
    have HRk : R !! key = some v := by rw [HRl key, if_neg Hnin]; exact Hv
    icases (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun id p => iprop(∃ bs, ⌜T.bufs !! id = some bs⌝ ∗ bytesPointsto (GF := GF) p (DFrac.own 1) bs))
      (show Std.get? R key = some v from HRk)).1 $$ HR with ⟨Hk, HR⟩
    icases Hk with ⟨%bk, %Hbk, Hkb⟩
    try wp_auto
    wp_apply (wp_slice_literal (V := Loc) [v])
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, Hcap1⟩
    wp_apply wp_slice_append sl (L.map DPg.l) _ [v] (DFrac.own 1) $$ [Hsl Hcap Hsl1] as %sl2 ⟨Hsl2, Hcap2, -⟩
    · iframe
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl2, L ++ [⟨key, v, bk⟩], GMap.delete key R, v
    have Htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    rw [List.map_append]
    iframe
    isplitr
    · ipureintro
      refine ⟨by omega, by rw [List.map_append, HLid, Htk]; rfl, fun e he => ?_, fun id => ?_⟩
      · rcases List.mem_append.1 he with he | he
        · exact HLmem e he
        · rw [List.mem_singleton] at he; subst he; exact ⟨Hv, Hbk⟩
      · rw [Htk]
        by_cases hid : id = key
        · subst hid; rw [GMap.lookup_delete, if_pos (List.mem_append_right _ List.mem_cons_self)]
        · rw [GMap.lookup_delete_ne _ (Ne.symm hid), HRl id]
          simp only [List.mem_append, List.mem_singleton, hid, or_false]
    · iapply BigSepL.bigSepL_nil.2; iempintro
  iintro HP Hpm
  iNamed HP
  obtain ⟨-, HLid, HLmem, -⟩ := HL
  rw [show (GMap.size T.pm : Int).toNat = keys.length by omega, List.take_length] at HLid
  have HLok : listOK T L := by
    refine ⟨HLmem, fun id h => ?_, by rw [HLid]; exact Hknodup⟩
    have : id ∈ L.map DPg.id := by rw [HLid]; exact (Hkset id).2 h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 this
    exact ⟨e, he, rfl⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) Pgid.ty Page.ty.PointerType) as %pl Hpl
  try wp_auto
  -- the sort: the pages' headers lent out
  have Hb16 : ∀ e ∈ L, 16 ≤ e.b.length := by
    intro e he
    rw [(listOK_page σ T L HLok Hdirty e he).1]
    have : σ.ps ≤ dspan e.b * σ.ps := Nat.le_mul_of_pos_left _ (by unfold dspan; omega)
    omega
  icases hdrs_split (GF := GF) L Hb16 $$ HLb with ⟨HLh, HLw⟩
  wp_apply (hSort sl L DPg.l (fun e => pageOf e.b) (DFrac.own 1)) $$ [Hsl HLh] as %L' ⟨%HL', Hsl, HLh⟩
  · iframe
  ihave HLw := (BigSepL.bigSepL_perm (Φ := fun e => iprop(e.l ↦ pageOf e.b -∗
      bytesPointsto (GF := GF) e.l (DFrac.own 1) e.b)) HL'.1.symm).1 $$ HLw
  ihave HLb := hdrs_join (GF := GF) L' $$ [HLh HLw]
  · iframe
  have HL'ok : listOK T L' := listOK_perm T L L' HL'.1 HLok
  have Hb16' : ∀ e ∈ L', 16 ≤ e.b.length := fun e he => Hb16 e (HL'.1.mem_iff.1 he)
  have HL'len : L'.length < 2 ^ 62 := by
    have h1 : L.length = keys.length := by rw [← HLid, List.length_map]
    rw [HL'.1.length_eq, h1, Hklen]; exact Hsize
  try wp_auto
  -- the dirty slots' cells, page by page
  have Hpw := listOK_pw σ T L' HL'ok Hdirty
  have Hin : ∀ e ∈ L', uint.nat e.id + dspan e.b ≤ σ.nslots :=
    fun e he => (listOK_page σ T L' HL'ok Hdirty e he).2.2.1
  have Hlenb : ∀ e ∈ L', e.b.length = dspan e.b * σ.ps :=
    fun e he => (listOK_page σ T L' HL'ok Hdirty e he).1
  have HSd : ∀ s < σ.nslots, (dirtySlot T s ↔ inRuns (L'.map DPg.run) s) :=
    fun s _ => listOK_dirty T L' HL'ok s
  have Hrem : ∀ s < σ.nslots, dirtySlot T s → σ.rem s = halfQ :=
    fun s _ hs => rem_dirty σ v0 v1 Hok T Hdirty s hs
  icases (slots_wins (GF := GF) σ.data σ.bs σ.ps σ.rem σ.nslots L' (dirtySlot T) HSd Hrem
    (nslots_mul_le σ) Hin Hpw Hlenb).1 $$ Hslots with ⟨Hout, Hwins⟩
  icases typedPointsto_not_null_dup _ _ _ $$ ops with ⟨ops, %Hopsnn⟩
  iStructNamed ops
  irename : (("_" ∷ True) : IProp GF) => Hjunk
  iclear Hjunk
  irename : (i_ptr ↦ W64 0 : IProp GF) => Hi
  irename : (p_ptr ↦ (null : Loc) : IProp GF) => Hp
  -- the end, from any file `F'` that changed only the dirty pages' bytes
  ihave Hfin : (∀ (F' : List w8) (st : TxStats) (err : GoInterface),
      ⌜F'.length = σ.bs.length ∧
        (∀ i, (∀ e ∈ L', ¬ (uint.nat e.id * σ.ps ≤ i ∧ i < uint.nat e.id * σ.ps + e.b.length)) →
          F'[i]? = σ.bs[i]?) ∧
        (err = interface.nil → ∀ e ∈ L', seg F' (uint.nat e.id * σ.ps) e.b.length = e.b)⌝ -∗
      fileBytes σ.fd F' -∗ ([∗list] e ∈ L', win σ.data σ.ps F' e) -∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" W.dbl) ↦
        dv.ops'.writeAt' -∗
      structFieldRef DB go!"NoSync" W.dbl ↦ dv.NoSync' -∗
      structFieldRef DB go!"file" W.dbl ↦ dv.file' -∗
      structFieldRef Tx go!"stats" txl ↦ st -∗ fileMap σ.fd (some (σ.data, σ.sz)) -∗
      structFieldRef Tx go!"db" txl ↦ W.dbl -∗ Φ #err : IProp GF)
    $$ [-Hstats Hbytes Hwins writeAt NoSync file HLb Hsl Hi Hp tx lg Hmap Hdbf Hpgs]
  · iintro %F' %st %err %Hpure Hbytes Hwins writeAt NoSync file Hstats Hmap Hdbf
    obtain ⟨HFlen, HFout, HFall⟩ := Hpure
    have Hdo : dirtyOnly T σ.ps σ.bs F' := dirtyOnly_of T L' σ.ps HL'ok σ.bs F' HFlen HFout Hlenb
    have Hok2 := dbOK_dirty σ v0 v1 Hok T Hdirty F' Hdo
    ihave Hout := (cellsOut_congr (GF := GF) σ.data σ.bs F' σ.ps σ.rem (dirtySlot T) σ.nslots
      (fun s _ hs => Hdo.2 s hs)).1 $$ Hout
    ihave Hslots := (slots_wins (GF := GF) σ.data F' σ.ps σ.rem σ.nslots L' (dirtySlot T) HSd Hrem
      (by rw [HFlen]; exact nslots_mul_le σ) Hin Hpw Hlenb).2 $$ [Hout Hwins]
    · iframe
    have Htl : mapTail (GF := GF) σ.data F' σ.sz σ.ps = mapTail σ.data σ.bs σ.sz σ.ps := by
      unfold mapTail
      rw [HFlen, tail_of L' σ.ps _ σ.sz σ.bs F' HFlen HFout ?_]
      intro e he
      rw [Hlenb e he, ← Nat.add_mul]
      exact Nat.mul_le_mul_right σ.ps (Hin e he)
    ihave ops := typedPointsto_combine (structFieldRef DB go!"ops" W.dbl) dv.ops' (DFrac.own 1)
      Hopsnn $$ [writeAt]
    · simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iexists F', pl, st
    isplitl [Hslots Htail Hbytes ops NoSync file Hflf Hdata Hfp Hmap Hfl Hrwl Hmmaph Htoks Hstath
      Hdbstats Hrauth StrictMode NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags
      MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile dataref datasz meta0 meta1 opened rwtx
      stats batch readOnly]
    · unfold dbWR
      isplitl
      · simp only [ownDB]
        iexists dv, fls, v0, v1, dl
        isplitr
        · ipureintro; exact Hdv
        isplitr
        · ipureintro; exact Hok2
        isplitr
        · ipureintro; exact Hdr
        isplitr
        · ipureintro; exact Hops
        ihave Hplain : dbPlain W.dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType
          NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile
          file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
        · simp only [dbPlain]; iframe
        have Hns' : ({ σ with bs := F' } : DBState).nslots = σ.nslots := by
          unfold DBState.nslots; simp only [HFlen]
        rw [Htl, Hns']
        iframe
        iframe #
        try (ipureintro; exact Hlog)
      · ipureintro; exact ⟨HAS, Hrw, Hdata, Hps, Hfli, w, Hw, Hwp, Hwq, Hwh, Htxw, Htxb⟩
    isplitl [Hwritable Hmanaged Hdbf Hmetaf Hpages Hstats Hch Hwf Hm Hpl Hbs]
    · simp only [TxW_rest_root]
      rw [Htdb]
      iframe
      isplitr
      · ipureintro; exact Htxn
      iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl [Hdatav Hfliv Hpv]
    · simp only [wView]; iframe; iframe #; ipureintro; exact Hlgv
    ipureintro
    exact ⟨Hdo, fun he => dirtyAll_of T L' σ.ps HL'ok F' (HFall he)⟩
  ihave IH : (∃ (j : w64) (F : List w8) (pv : Loc) (st : TxStats),
      "Hi" ∷ i_ptr ↦ j ∗ "Hp" ∷ p_ptr ↦ pv ∗
      "Hstats" ∷ structFieldRef Tx go!"stats" txl ↦ st ∗
      "Hbytes" ∷ fileBytes σ.fd F ∗
      "Hwins" ∷ ([∗list] e ∈ L', win σ.data σ.ps F e) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ L'.length ∧ outerOK L' σ.ps σ.bs F (sint.nat j)⌝ :
      IProp GF) $$ [Hi Hp Hstats Hbytes Hwins]
  · iexists W64 0, σ.bs, null, T.t.stats'
    iframe
    ipureintro
    refine ⟨by decide, by simp, rfl, fun i _ => rfl, fun m e hm _ => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl] at hm; omega
  wp_for IH
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len := by simpa using Hif
    clear Hif
    have Hjn : sint.nat j < L'.length := by
      have := Hsll.1; simp only [List.length_map] at this; word
    list_elem L' (sint.nat j) as c
    have Hget : (L'.map DPg.l)[sint.nat j]? = some c.l := by
      rw [List.getElem?_map, Hc_lookup]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len
      from ⟨Hj.1, Hlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ c.l Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hget
    try wp_auto
    have Hcm : c ∈ L' := List.mem_of_getElem? Hc_lookup
    obtain ⟨Hclen, Hcid, Hcin, Hcun⟩ := listOK_page σ T L' HL'ok Hdirty c Hcm
    icases (BigSepL.bigSepL_lookup_acc Hc_lookup).1 $$ HLb with ⟨Hcb, HLback⟩
    icases hdr_split (GF := GF) c.l (DFrac.own 1) c.b (Hb16' c Hcm) $$ Hcb with ⟨Hh, Hhback⟩
    wp_apply hOv c.l (pageOf c.b) (DFrac.own 1) $$ [Hh] as Hh
    · iframe
    try wp_auto
    wp_apply hId c.l (pageOf c.b) (DFrac.own 1) $$ [Hh] as Hh
    · iframe
    try wp_auto
    ihave Hcb := Hhback $$ Hh
    have HcinB : uint.nat c.id * σ.ps + c.b.length ≤ σ.nslots * σ.ps := by
      rw [Hclen, ← Nat.add_mul]; exact Nat.mul_le_mul_right σ.ps Hcin
    have HNb := nslots_mul_le σ
    have HNsz : σ.nslots * σ.ps ≤ σ.sz := by
      unfold DBState.nslots; have := Nat.div_mul_le_self (min σ.sz σ.bs.length) σ.ps; omega
    have Hc16 := Hb16' c Hcm
    have Hremv : (W64 (uint.Z (W32 ((pageOverflow c.b : Nat) : Int))) + W64 1) * W64 ((W.ps : Nat) : Int) =
        W64 ((c.b.length - 0 : Nat) : Int) := by
      rw [Nat.sub_zero]
      exact rem_val _ _ _ (pageOverflow_lt c.b) (by rw [Hclen, ← Hps]; rfl)
    have Hoffv : W64 ((pageId c.b : Nat) : Int) * W64 ((W.ps : Nat) : Int) =
        W64 ((uint.nat c.id * σ.ps + 0 : Nat) : Int) := by
      rw [Nat.add_zero, Hcid, ← Hps]; exact off_val c.id σ.ps
    irename : (rem_ptr ↦ (_ : w64) : IProp GF) => Hrem
    irename : (offset_ptr ↦ (_ : w64) : IProp GF) => Hoff
    irename : (written_ptr ↦ (_ : w64) : IProp GF) => Hwr
    icases (sepL_at L' (sint.nat j) c Hc_lookup (fun e => win (GF := GF) σ.data σ.ps F e)).1 $$ Hwins
      with ⟨Hwpre, Hwc, Hwpost⟩
    ihave IH2 : (∃ (w : Nat) (F2 : List w8) (st2 : TxStats),
        "Hrem" ∷ rem_ptr ↦ W64 ((c.b.length - w : Nat) : Int) ∗
        "Hoff" ∷ offset_ptr ↦ W64 ((uint.nat c.id * σ.ps + w : Nat) : Int) ∗
        "Hwr" ∷ written_ptr ↦ W64 (w : Int) ∗
        "Hstats" ∷ structFieldRef Tx go!"stats" txl ↦ st2 ∗
        "Hbytes" ∷ fileBytes σ.fd F2 ∗ "Hwc" ∷ win σ.data σ.ps F2 c ∗
        "%Hw" ∷ ⌜w < c.b.length ∧ innerOK c σ.ps F F2 w⌝ : IProp GF) $$ [Hrem Hoff Hwr Hstats Hbytes Hwc]
    · iexists 0, F, st
      rw [← Hremv, ← Hoffv]
      iframe
      ipureintro
      exact ⟨by omega, rfl, fun i _ => rfl, by simp⟩
    wp_for IH2
    obtain ⟨Hwlt, Hin2⟩ := Hw
    have Hlw : c.b.length - w < 2 ^ 62 := by omega
    obtain ⟨cs, Hcs⟩ : ∃ cs : Nat, cs = min (c.b.length - w) 2147483646 := ⟨_, rfl⟩
    have Hcs0 : 0 < cs := by omega
    wp_if_destruct
    focus
      have : 2147483646 < c.b.length - w := cs_lt _ (by simpa using Hif) Hlw
      try wp_auto
      rw [show (2147483646 : Int) = (cs : Int) by omega]
      ihave Hrem : (∃ r : Nat, rem_ptr ↦ W64 (r : Int) ∗ ⌜r = c.b.length - w⌝) $$ [Hrem]
      · iexists _; iframe; ipureintro; rfl
    rotate_left
    focus
      have : ¬ 2147483646 < c.b.length - w := cs_ge _ (by simpa using Hif) Hlw
      try wp_auto
      rw [show c.b.length - w = cs by omega]
      ihave Hrem : (∃ r : Nat, rem_ptr ↦ W64 (r : Int) ∗ ⌜r = c.b.length - w⌝) $$ [Hrem]
      · iexists _; iframe; ipureintro; omega
    all_goals
      icases Hrem with ⟨%r, Hrem, %Hr⟩
      have Hcn : c.b ≠ [] := List.ne_nil_of_length_pos (by omega)
      icases persistent_entails_left (bytesPointsto_car c.l _ c.b Hcn) $$ Hcb with ⟨Hcb, %Hccar⟩
      wp_apply hUBS c.l (W64 (w : Int)) (W64 0) (W64 (cs : Int)) Hccar (by word) (by word) (by word)
      try wp_auto
      -- the chunk: the buffer's bytes `w` to `w + cs`, and the mapping's cells there
      have Hwcs : w + cs ≤ c.b.length := by omega
      icases bytes_slice_acc (GF := GF) c.l (DFrac.own 1) c.b w cs Hwcs (by omega) Hccar $$ Hcb
        with ⟨Hchunk, Hcback⟩
      have Hsle : slice.mk (c.l +ₗ (sint.Z (W64 (w : Int)) + sint.Z (W64 0))) (W64 (cs : Int) - W64 0)
          (W64 (cs : Int) - W64 0) = sliceAt c.l w cs := by
        unfold sliceAt
        have h1 : sint.Z (W64 (w : Int)) + sint.Z (W64 0) = (w : Int) := by word
        rw [h1]; congr 1 <;> word
      rw [Hsle]
      have Hpos : uint.nat c.id * σ.ps + c.b.length ≤ F2.length := by rw [Hin2.1]; have := Hj.2.2.1; omega
      icases (seg3 (GF := GF) σ.data (DFrac.own halfQ) F2 (uint.nat c.id * σ.ps) w cs
        (c.b.length - w - cs) (by omega)).1 $$ [Hwc] with ⟨Hw1, Hw2, Hw3⟩
      · unfold win at *
        rw [show w + cs + (c.b.length - w - cs) = c.b.length by omega]; iexact Hwc
      rw [Hops]
      have Hsn : sint.nat (W64 ((uint.nat c.id * σ.ps + w : Nat) : Int)) = uint.nat c.id * σ.ps + w := by
        have : uint.nat c.id * σ.ps + w < 2 ^ 62 := by omega
        word
      have Hbl := bytesAt_length c.b w cs Hwcs
      ihave Hmr : mapRange (GF := GF) (some (σ.data, σ.sz)) F2
          (min (sint.nat (W64 ((uint.nat c.id * σ.ps + w : Nat) : Int))) F2.length)
          (sint.nat (W64 ((uint.nat c.id * σ.ps + w : Nat) : Int)) + (bytesAt c.b w cs).length) $$ [Hw2]
      · rw [Hsn, Nat.min_eq_left (by omega), Hbl, mapRange_eq_seg _ _ _ _ _ (by omega)]
        iexact Hw2
      wp_apply hWA σ.file σ.fd F2 (some (σ.data, σ.sz)) (sliceAt c.l w cs) (bytesAt c.b w cs)
        (DFrac.own 1) (W64 ((uint.nat c.id * σ.ps + w : Nat) : Int)) (by word)
        $$ [Hbytes Hmap Hchunk Hmr] as %n %err ⟨%k, %Hk, Hbytes, Hmap, Hchunk, Hmr⟩
      · iframe; iframe #
      obtain ⟨Hkc, Hn, Hke⟩ := Hk
      have Hdl : ((bytesAt c.b w cs).take k).length = k := by rw [List.length_take, Hbl]; omega
      have Hwin : uint.nat c.id * σ.ps + w + ((bytesAt c.b w cs).take k).length ≤ F2.length := by
        rw [Hdl]; omega
      have HF3len := writeBytes_length_in F2 (uint.nat c.id * σ.ps + w) _ Hwin
      rw [Hsn, Nat.min_eq_left (show uint.nat c.id * σ.ps + w ≤ F2.length by omega), Hbl,
        mapRange_eq_seg _ _ _ _ _ (show uint.nat c.id * σ.ps + w + cs ≤ σ.sz by omega)]
      -- the window of `c` in the new file
      have HF3out : ∀ i, (i < uint.nat c.id * σ.ps + w ∨ uint.nat c.id * σ.ps + w + k ≤ i) →
          (writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k))[i]? = F2[i]? :=
        fun i hi => writeBytes_out _ _ _ Hwin i (by rw [Hdl]; exact hi)
      ihave Hwc : win σ.data σ.ps (writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k)) c
        $$ [Hw1 Hmr Hw3]
      · unfold win
        have hsplit : c.b.length = w + cs + (c.b.length - w - cs) := by omega
        rw [show seg (writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k))
            (uint.nat c.id * σ.ps) c.b.length =
          seg (writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k))
            (uint.nat c.id * σ.ps) (w + cs + (c.b.length - w - cs)) from by rw [← hsplit]]
        iapply (seg3 (GF := GF) σ.data (DFrac.own halfQ) _ (uint.nat c.id * σ.ps) w cs (c.b.length - w - cs)
          (by rw [HF3len]; omega)).2
        rw [seg_congr F2 _ (uint.nat c.id * σ.ps) w (fun i _ h => HF3out i (Or.inl h)),
          seg_congr F2 _ (uint.nat c.id * σ.ps + w + cs) _ (fun i h _ => HF3out i (Or.inr (by omega)))]
        iframe
      have Hin3 : innerOK c σ.ps F (writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k))
          (w + k) := by
        refine ⟨HF3len.trans Hin2.1, fun i hi => ?_, ?_⟩
        · rw [HF3out i (by omega)]; exact Hin2.2.1 i hi
        · have Hsw := seg_write F2 _ _ Hwin
          rw [Hdl] at Hsw
          rw [seg_add, seg_congr F2 _ (uint.nat c.id * σ.ps) w (fun i _ h => HF3out i (Or.inl h)),
            Hin2.2.2, Hsw, chunk_take c.b w cs k (by rw [Hbl] at Hkc; exact Hkc), take_add_chunk]
      generalize HF3 : writeBytes F2 (uint.nat c.id * σ.ps + w) ((bytesAt c.b w cs).take k) = F3
        at HF3len HF3out Hin3 ⊢
      have Hagree : ∀ e, (e ∈ L'.take (sint.nat j) ∨ e ∈ L'.drop (sint.nat j + 1)) → ∀ i,
          uint.nat e.id * σ.ps ≤ i → i < uint.nat e.id * σ.ps + e.b.length → F3[i]? = F[i]? :=
        fun e he i h1 h2 => Hin3.2.1 i (other_bytes σ T L' HL'ok Hdirty _ c Hc_lookup e he i ⟨h1, h2⟩)
      cases err with
      | ok e =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %slx ⟨Hslx, -⟩
        try wp_auto
        wp_apply hErrf W.dl _ _ $$ [Hdlok0]
        · iframe #
        try wp_auto
        wp_for_post
        wp_for_post
        ihave Hwpre := (wins_congr (GF := GF) σ.data σ.ps F F3 (L'.take (sint.nat j))
          (fun e he => Hagree e (Or.inl he))).1 $$ Hwpre
        ihave Hwpost := (wins_congr (GF := GF) σ.data σ.ps F F3 (L'.drop (sint.nat j + 1))
          (fun e he => Hagree e (Or.inr he))).1 $$ Hwpost
        ihave Hwins := (sepL_at L' (sint.nat j) c Hc_lookup
          (fun e => win (GF := GF) σ.data σ.ps F3 e)).2 $$ [Hwpre Hwc Hwpost]
        · iframe
        ihave %Hp : ⌜F3.length = σ.bs.length ∧
            (∀ i, (∀ e ∈ L', ¬ (uint.nat e.id * σ.ps ≤ i ∧ i < uint.nat e.id * σ.ps + e.b.length)) →
              F3[i]? = σ.bs[i]?) ∧
            (GoInterface.ok e = interface.nil →
              ∀ e ∈ L', seg F3 (uint.nat e.id * σ.ps) e.b.length = e.b)⌝ $$ []
        · ipureintro
          refine ⟨Hin3.1.trans Hj.2.2.1, fun i hi => ?_, fun h => nomatch h⟩
          rw [Hin3.2.1 i (hi c Hcm)]; exact Hj.2.2.2.1 i hi
        iapply Hfin $$ %F3 %st2 %(GoInterface.ok e) %Hp Hbytes Hwins writeAt NoSync file Hstats Hmap Hdbf
      | nil =>
        have Hkcs : k = cs := by have := Hke rfl; rw [Hbl] at this; exact this
        try wp_auto
        wp_apply hInc (structFieldRef Tx go!"stats" txl) st2 (W64 1) $$ [Hstats] as %st3 ⟨-, Hstats⟩
        · iframe
        try wp_auto
        have Hrs : W64 (r : Int) - W64 (cs : Int) = W64 ((c.b.length - (w + cs) : Nat) : Int) := by
          rw [show c.b.length - (w + cs) = r - cs by omega]
          exact sub_val r cs (by omega) (by omega)
        rw [Hrs]
        wp_if_destruct
        · have Hend : c.b.length - (w + cs) = 0 := w64_eq0 _ (by omega) Hif
          try wp_auto
          wp_for_post
          ihave Hcb := Hcback $$ Hchunk
          ihave HLb := HLback $$ %c Hcb
          rw [set_self L' _ c Hc_lookup]
          ihave Hwpre := (wins_congr (GF := GF) σ.data σ.ps F F3 (L'.take (sint.nat j))
            (fun e he => Hagree e (Or.inl he))).1 $$ Hwpre
          ihave Hwpost := (wins_congr (GF := GF) σ.data σ.ps F F3 (L'.drop (sint.nat j + 1))
            (fun e he => Hagree e (Or.inr he))).1 $$ Hwpost
          ihave Hwins := (sepL_at L' (sint.nat j) c Hc_lookup
            (fun e => win (GF := GF) σ.data σ.ps F3 e)).2 $$ [Hwpre Hwc Hwpost]
          · iframe
          wp_for_post
          iframe
          iexists j + W64 1, F3, c.l, st3
          iframe
          ipureintro
          have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            have : sint.nat j < 2 ^ 62 := by omega
            word
          rw [Hj1]
          refine ⟨by word, by omega, Hin3.1.trans Hj.2.2.1, fun i hi => ?_, fun m e hm he => ?_⟩
          · rw [Hin3.2.1 i (hi c Hcm)]; exact Hj.2.2.2.1 i hi
          · by_cases hmj : m = sint.nat j
            · subst hmj
              rw [Hc_lookup] at he; cases he
              have := Hin3.2.2
              rw [show w + k = c.b.length by omega, List.take_length] at this
              exact this
            · have hme : e ∈ L'.take (sint.nat j) := by
                apply List.mem_of_getElem? (i := m)
                rw [List.getElem?_take, if_pos (by omega)]; exact he
              rw [seg_congr F F3 _ _ (Hagree e (Or.inl hme))]
              exact Hj.2.2.2.2 m e (by omega) he
        · have Hnend : c.b.length - (w + cs) ≠ 0 := fun h => Hif (by rw [h]; rfl)
          try wp_auto
          rw [add_val _ _ (show uint.nat c.id * σ.ps + w + cs < 2 ^ 62 by omega),
            add_val _ _ (show w + cs < 2 ^ 62 by omega)]
          ihave Hcb := Hcback $$ Hchunk
          wp_for_post
          iframe
          iexists w + cs, F3, st3
          rw [show c.b.length - (w + cs) = c.b.length - (w + cs) from rfl,
            show uint.nat c.id * σ.ps + w + cs = uint.nat c.id * σ.ps + (w + cs) by omega]
          iframe
          ipureintro
          exact ⟨by omega, by rw [← Hkcs]; exact Hin3⟩
  · have Hge : ¬ sint.Z j < sint.Z sl.len := by simpa using Hif
    clear Hif
    have Hjl : sint.nat j = L'.length := by
      have := Hsll.1; simp only [List.length_map] at this; word
    obtain ⟨-, -, HFo⟩ := Hj
    rw [Hjl] at HFo
    have HFall : ∀ e ∈ L', seg F (uint.nat e.id * σ.ps) e.b.length = e.b := by
      intro e he
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 he
      exact HFo.2.2 m e (List.getElem?_eq_some_iff.1 hm).1 hm
    have Hpf : F.length = σ.bs.length ∧
        (∀ i, (∀ e ∈ L', ¬ (uint.nat e.id * σ.ps ≤ i ∧ i < uint.nat e.id * σ.ps + e.b.length)) →
          F[i]? = σ.bs[i]?) ∧
        (∀ (er : GoInterface), er = interface.nil →
          ∀ e ∈ L', seg F (uint.nat e.id * σ.ps) e.b.length = e.b) :=
      ⟨HFo.1, HFo.2.1, fun _ _ => HFall⟩
    try wp_auto
    cases hns : dv.NoSync'
    focus
      try wp_auto
      wp_apply hfds W.dbl dv.file' σ.fd (DFrac.own 1) $$ [file] as %ferr file
      · rw [Hdv.2.2.2.2.2.2.1]; iframe; iframe #
      try wp_auto
      cases ferr
      focus
        rename_i e
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %slx ⟨Hslx, -⟩
        try wp_auto
        rw [GOOSLinux.goos]
        try wp_auto
        wp_apply hErrf W.dl _ _ $$ [Hdlok0]
        · iframe #
        try wp_auto
        have Hpe := (⟨Hpf.1, Hpf.2.1, Hpf.2.2 (GoInterface.ok e)⟩ : _ ∧ _ ∧ _)
        iapply Hfin $$ %F %st %(GoInterface.ok e) %Hpe Hbytes Hwins writeAt NoSync file Hstats Hmap Hdbf
      try wp_auto
    rotate_left
    focus
      try wp_auto
    all_goals
      -- the one-slot pages back to the page pool
      try wp_auto
      irename : (i_ptr ↦ W64 0 : IProp GF) => Hi3
      irename : (p_ptr ↦ (null : Loc) : IProp GF) => Hp3
      ihave IH3 : (∃ (j2 : w64) (pv : Loc), "Hi3" ∷ i_ptr ↦ j2 ∗ "Hp3" ∷ p_ptr ↦ pv ∗
          "HLb" ∷ ([∗list] e ∈ L'.drop (sint.nat j2), bytesPointsto e.l (DFrac.own 1) e.b) ∗
          "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.nat j2 ≤ L'.length⌝ : IProp GF) $$ [Hi3 Hp3 HLb]
      · iexists W64 0, null
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        iframe; ipureintro; exact ⟨by decide, by omega⟩
      wp_for IH3
      wp_if_destruct
      · have Hlt : sint.Z j2 < sint.Z sl.len := by first | simpa using Hif | simpa using GoGlobalContext.intoVal_inj_bool Hif
        clear Hif
        have Hjn : sint.nat j2 < L'.length := by
          have := Hsll.1; simp only [List.length_map] at this; word
        list_elem L' (sint.nat j2) as c2
        have Hget : (L'.map DPg.l)[sint.nat j2]? = some c2.l := by
          rw [List.getElem?_map, Hc2_lookup]; rfl
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z sl.len
          from ⟨Hj2.1, Hlt⟩))]
        wp_apply wp_load_slice_index _ (sint.Z j2) _ _ c2.l Hj2.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact Hget
        try wp_auto
        have Hc2m : c2 ∈ L' := List.mem_of_getElem? Hc2_lookup
        rw [List.drop_eq_getElem_cons Hjn, show L'[sint.nat j2] = c2 from
          (List.getElem?_eq_some_iff.1 Hc2_lookup).2]
        icases BigSepL.bigSepL_cons.1 $$ HLb with ⟨Hc2, HLb⟩
        icases hdr_split (GF := GF) c2.l (DFrac.own 1) c2.b (Hb16' c2 Hc2m) $$ Hc2 with ⟨Hh, Hhback⟩
        wp_apply hOv c2.l (pageOf c2.b) (DFrac.own 1) $$ [Hh] as Hh
        · iframe
        try wp_auto
        ihave Hc2 := Hhback $$ Hh
        have Hj21 : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by
          have : sint.nat j2 < 2 ^ 62 := by omega
          word
        by_cases hov : pageOverflow c2.b = 0
        · have Hov0 : W64 (uint.Z (W32 ((pageOverflow c2.b : Nat) : Int))) = W64 0 := by rw [hov]; rfl
          rw [decide_eq_true Hov0]
          try wp_auto
          have Hc2len : c2.b.length = σ.ps := by
            rw [(listOK_page σ T L' HL'ok Hdirty c2 Hc2m).1]; unfold dspan; rw [hov]; omega
          have Hcn : c2.b ≠ [] := List.ne_nil_of_length_pos (by omega)
          icases persistent_entails_left (bytesPointsto_car c2.l _ c2.b Hcn) $$ Hc2 with ⟨Hc2, %Hc2car⟩
          wp_apply hUBS c2.l (W64 0) (W64 0) (W64 (W.ps : Int)) Hc2car (by word) (by word)
            (by rw [← Hps]; word)
          have Hs0 : slice.mk (c2.l +ₗ (sint.Z (W64 0) + sint.Z (W64 0))) (W64 (W.ps : Int) - W64 0)
              (W64 (W.ps : Int) - W64 0) = slice.mk c2.l (W64 (σ.ps : Int)) (W64 (σ.ps : Int)) := by
            rw [← Hps]; congr 1
            · simp [Loc.add]
            · word
            · word
          rw [Hs0]
          ihave Hbuf := (ownSlice_bytes (slice.mk c2.l (W64 (σ.ps : Int)) (W64 (σ.ps : Int))) c2.b
            (DFrac.own 1) Hcn).2 $$ [Hc2]
          · iframe; ipureintro; simp only; constructor <;> word
          try wp_auto
          rename_i ipo iu
          irename : (i_ptr ↦ W64 0 : IProp GF) => Hi4
          irename : (iu ↦ (_ : w64) : IProp GF) => Hiu
          have Hpsl : sint.Z (W64 (σ.ps : Int)) = σ.ps := by word
          ihave IH4 : (∃ (k2 uv : w64), "Hi4" ∷ i_ptr ↦ k2 ∗ "Hiu" ∷ iu ↦ uv ∗
              "Hbuf" ∷ slice.mk c2.l (W64 (σ.ps : Int)) (W64 (σ.ps : Int)) ↦*
                (List.replicate (sint.nat k2) (W8 0) ++ c2.b.drop (sint.nat k2)) ∗
              "%Hk2" ∷ ⌜0 ≤ sint.Z k2 ∧ sint.nat k2 ≤ c2.b.length⌝ : IProp GF) $$ [Hi4 Hiu Hbuf]
          · iexists W64 0, _
            rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero, List.nil_append, List.drop_zero]
            iframe; ipureintro; exact ⟨by decide, by omega⟩
          wp_for IH4
          by_cases hk : sint.Z k2 < sint.Z (W64 (σ.ps : Int))
          · try rw [decide_eq_true hk]
            try simp only [_root_.decide_true, ↓reduceIte]
            have Hkn : sint.nat k2 < c2.b.length := by rw [Hc2len]; rw [Hpsl] at hk; word
            list_elem c2.b (sint.nat k2) as bk
            have Hgk : (List.replicate (sint.nat k2) (W8 0) ++ c2.b.drop (sint.nat k2))[sint.nat k2]? =
                some bk := by
              rw [List.getElem?_append_right (by simp)]
              simp only [List.length_replicate, Nat.sub_self, List.getElem?_drop, Nat.add_zero]
              exact Hbk_lookup
            have Hbd : (0 ≤ sint.Z k2 ∧ sint.Z k2 < sint.Z (W64 (σ.ps : Int))) = True :=
              eq_true ⟨Hk2.1, hk⟩
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            try (wp_apply wp_load_slice_index _ (sint.Z k2) _ _ bk Hk2.1 $$ [Hbuf] as Hbuf
                 focus (iframe; ipureintro; exact Hgk))
            try wp_auto
            try rw [ite_eq_left_of_eq_true _ _ Hbd]
            have Hbl2 : (List.replicate (sint.nat k2) (W8 0) ++ c2.b.drop (sint.nat k2)).length =
                c2.b.length := by simp; omega
            wp_apply wp_store_slice_index _ (sint.Z k2) _ (W8 0) $$ [Hbuf] as Hbuf
            · iframe; ipureintro; rw [Hbl2]; constructor <;> word
            rw [show (sint.Z k2).toNat = sint.nat k2 from rfl, zero_step c2.b _ Hkn]
            try wp_auto
            wp_for_post
            iframe
            iexists k2 + W64 1, _
            have Hk21 : sint.nat (k2 + W64 1) = sint.nat k2 + 1 := by
              have : sint.nat k2 < 2 ^ 62 := by omega
              word
            rw [Hk21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
          · try rw [decide_eq_false hk]
            have hft : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
            try rw [decide_eq_false hft, decide_eq_true (rfl : (#false : val) = #false)]
            try simp only [Bool.false_eq_true, ↓reduceIte]
            have Hke : sint.nat k2 = c2.b.length := by rw [Hc2len]; rw [Hpsl] at hk; word
            rw [Hke, List.drop_length, List.append_nil, Hc2len]
            try wp_auto
            wp_apply hPut (structFieldRef DB go!"pagePool" W.dbl) (pageBuf σ.ps) _ $$ [Hbuf]
            · iframe #
              unfold pageBuf
              iexists _
              iframe
              ipureintro; rfl
            try wp_auto
            wp_for_post
            iframe
            iexists j2 + W64 1, c2.l
            rw [Hj21]
            iframe
            ipureintro; exact ⟨by word, by omega⟩
        · have Hov0 : W64 (uint.Z (W32 ((pageOverflow c2.b : Nat) : Int))) ≠ W64 0 := by
            have := pageOverflow_lt c2.b
            intro h; apply hov; word
          rw [decide_eq_false Hov0]
          try wp_auto
          wp_for_post
          iframe
          iexists j2 + W64 1, c2.l
          rw [Hj21]
          iframe
          ipureintro; exact ⟨by word, by omega⟩
      · first
          | (have hb : decide (sint.Z j2 < sint.Z sl.len) = false := by
               cases h : decide (sint.Z j2 < sint.Z sl.len)
               · rfl
               · exact absurd (by rw [h]) Hif
             rw [hb]
             simp only [_root_.decide_true, ↓reduceIte])
          | skip
        try wp_auto
        have Hpe := (⟨Hpf.1, Hpf.2.1, Hpf.2.2 GoInterface.nil⟩ : _ ∧ _ ∧ _)
        iapply Hfin $$ %F %st %GoInterface.nil %Hpe Hbytes Hwins writeAt NoSync file Hstats Hmap Hdbf

end proof

end bbolt
end EtcdGrove
end Perennial
