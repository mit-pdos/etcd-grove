/-
`Commit`'s publish, pure (U10l of `notes/bbolt-proof-plan.md`; was U10k's open `cm_pub_ok`):
`commitStep_commit`'s premises (`cpOK`) for the published slots, and `wdbOK` of the published writer
side, from `cmPubPre`/`cmPubPg` and the write's post. The published writer side is the writer side
after a failed meta write (`cm_unpub_ok`) with the published slots out of its `W` slots and the
new committed state (`wdbOK_withC_pub`).

The new high-water mark's pages lie inside the file by `markCov` (decision D-K, `cm_pub_hwm`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailPub
public import Proof.go_etcd_io.bbolt.Commit.WriteRun

@[expose] public section

noncomputable section

set_option maxRecDepth 20000

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem po_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

theorem po_flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A page's chunks, concatenated, are the page. -/
theorem flatMap_pageChunk (pg : List w8) (a n : Nat) (hl : pg.length = 4096 * n) :
    (List.range' a n).flatMap (fun s => pageChunk pg (s - a)) = pg := by
  induction n generalizing a pg with
  | zero => simp at hl; simp [hl]
  | succ n ih =>
    rw [List.range'_succ, List.flatMap_cons, Nat.sub_self]
    have e : (List.range' (a + 1) n).flatMap (fun s => pageChunk pg (s - a)) =
        (List.range' (a + 1) n).flatMap (fun s => pageChunk (pg.drop 4096) (s - (a + 1))) := by
      apply po_flatMap_congr
      intro s hs
      have := (List.mem_range'_1.1 hs).1
      rw [pageChunk_succ]
      congr 1
      omega
    rw [e, ih (pg.drop 4096) (a + 1) (by simp [hl]; omega)]
    unfold pageChunk
    simp

theorem pp_mem_pendSlots' (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

theorem po_mem_pagesSlots (P : Pages) (s : Nat) :
    s ∈ pagesSlots P ↔ ∃ id pg, P !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg) := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range']
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

/-- **`cpOK` from the publish's facts** (the first half of `cm_pub_ok`). -/
theorem cm_cpOK (D : Data) (X : WX) (w : WDb) (b : Loc) (l : Nat) (Pg : Pages)
    (wb' : Nat → List w8) (hpre : cmPubPre D X w) (hpg : cmPubPg D X w Pg)
    (htx : X.t.mv.txid' = w.wtxid) (hok : wdbOK w)
    (hmapl : X.t.mv.pgid'.toNat * 4096 ≤ l)
    (hlen : ∀ s ∈ bufSlots X.t.bufs, (wb' s).length = 4096)
    (hch : ∀ id pg, X.t.bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
      wb' (id.toNat + j) = pageChunk pg j) :
    cpOK w.C w.fl b l X.t.mv Pg D ((bufSlots X.t.bufs).filter (pubP w X Pg)) wb' := by
  obtain ⟨-, hb, -, hsl, -, -, -, hmv, hps, -⟩ := hpre
  obtain ⟨hD, htree, h62, hdrop, hnp, hfb, hpages, hslots, -, -⟩ := hpg
  have h7 : w.C.txid + 1 < 2 ^ 64 := hok.2.2.2.2.2.2.1
  have hhwm : (pubC w.C X.t.mv Pg).hwm = X.t.mv.pgid'.toNat := pubC_hwm _ _ _
  have hS : ∀ s, s ∈ (bufSlots X.t.bufs).filter (pubP w X Pg) ↔
      s ∈ treeSlots (pubC w.C X.t.mv Pg) ∧ s ∉ slotsOf w.C w.fl := by
    intro s
    rw [List.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      simp only [pubP, decide_eq_true_eq] at h
      exact h
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by simp only [pubP, decide_eq_true_eq]; exact ⟨h1, h2⟩⟩
      rcases hslots s h1 with h | h
      · exact absurd h h2
      · exact h
  refine ⟨?_, hmv, hps, hD, htree, h62, hdrop, hS, fun id pg hp => ?_, hfb, hnp, fun s hs => ?_⟩
  · rw [htx]; unfold WDb.wtxid; exact po_W64_toNat _ h7
  · rcases hpages id pg hp with h | h
    · exact Or.inl h
    · right
      have hlt : id < 2 ^ 64 := by
        have := htree.2.2.2.1 id pg hp
        rw [hhwm] at this
        have := X.t.mv.pgid'.isLt
        omega
      have hid : (W64 (id : Int)).toNat = id := po_W64_toNat id hlt
      obtain ⟨-, hl, -, -⟩ := hb _ _ h
      refine ⟨fun j hj => (hS _).2 ⟨?_, ?_⟩, ?_⟩
      · exact (po_mem_pagesSlots _ _).2 ⟨id, pg, hp, by omega, by omega⟩
      · have hm : id + j ∈ bufSlots X.t.bufs :=
          (mem_bufSlots _ _).2 ⟨_, pg, h, by rw [hid]; omega, by rw [hid]; omega⟩
        obtain ⟨c1, c2, -⟩ := hsl _ hm
        rw [mem_slotsOf]
        rintro (c | c)
        · exact c1 c
        · exact c2 c
      · refine (flatMap_pageChunk pg id (1 + pageOverflow pg) hl).symm.trans
          (po_flatMap_congr fun s hs => ?_)
        have := List.mem_range'_1.1 hs
        have e := hch _ pg h (s - id) (by omega)
        rw [hid, show id + (s - id) = s by omega] at e
        exact e.symm
  · have hSB := (List.mem_filter.1 hs).1
    obtain ⟨id, pg, h, h1, h2⟩ := (mem_bufSlots _ s).1 hSB
    obtain ⟨-, -, h3, h4⟩ := hb _ _ h
    obtain ⟨-, -, c3⟩ := hsl s hSB
    refine ⟨hlen s hSB, c3, fun b' l' e => ?_, by omega⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have : X.t.mv.pgid'.toNat ≤ l / 4096 := (Nat.le_div_iff_mul_le (by decide)).2 hmapl
    omega

/-- **The published writer side's `wdbOK`, transferred** from the writer side `w0` (all written
slots back among its `W` slots): the published slots `S` (wholly inside the file, new tree slots)
out of the `W` slots, their bytes free to change, and the new committed state `C'` with its
facts. -/
theorem wdbOK_withC_pub (w0 : WDb) (C' : CommitSt) (S W1 : List Nat) (wb1 : Nat → List w8)
    (hok : wdbOK w0) (hW1 : ∀ s, s ∈ W1 ↔ s ∈ w0.W ∧ s ∉ S)
    (hwb : ∀ s, s ∉ S → wb1 s = w0.wb s) (hSin : ∀ s ∈ S, 4096 * (s + 1) ≤ w0.m.size)
    (hSt : ∀ s ∈ S, s ∈ treeSlots C')
    (hhwm : C'.hwm * 4096 ≤ w0.m.size)
    (hW' : ∀ s ∈ w0.W, s ∉ S → s ∉ treeSlots C')
    (hdrop : ∀ s ∈ treeSlots w0.C, s ∉ treeSlots C' → s ∈ pendSlots w0.fl)
    (hfree : ∀ x ∈ w0.fl.free, x.toNat ∉ treeSlots C')
    (hflc : ∀ f, C'.flpg = some f → flCurOK w0.fl C' (extentBytes wb1 f))
    (htx : C'.txid + 1 < 2 ^ 64) (hh64 : C'.hwm < 2 ^ 64)
    (hmap : ∀ b l, w0.ms = some (b, l) → C'.hwm * 4096 ≤ l)
    (hlt : ∀ s, s ∈ treeSlots C' ∨ s ∈ pendSlots w0.fl → s < C'.hwm)
    (hflt : ∀ x ∈ w0.fl.free, x.toNat < C'.hwm) :
    wdbOK ((w0.reslot w0.m W1 wb1).withC C') := by
  obtain ⟨c1, c2, -, c4, -, -, -, -, -, c10, -, -, c13, c14, c15, c16, c17⟩ := hok
  simp only [wdbOK, WDb.withC, WDb.reslot]
  refine ⟨c1, c2, hhwm, fun s => ?_, hfree, hflc, htx, hh64, hmap, c10, hlt, hflt, c13, c14,
    fun s hs hz => ?_, fun s h1 h2 => ?_, c17⟩
  · show s ∈ W1 ↔ 2 ≤ s ∧ s < max (mapLen w0.ms) w0.m.size / 4096 ∧ s ∉ treeSlots C' ∧
      s ∉ pendSlots w0.fl
    rw [hW1]
    constructor
    · rintro ⟨hs, hn⟩
      obtain ⟨a, b, -, d⟩ := (c4 s).1 hs
      exact ⟨a, b, hW' s hs hn, d⟩
    · rintro ⟨a, b, ht, d⟩
      refine ⟨(c4 s).2 ⟨a, b, fun h => d (hdrop s h ht), d⟩, fun h => ht (hSt s h)⟩
  · show (wb1 s).length = 4096
    have := (hW1 s).1 hs
    rw [hwb s this.2]
    exact c15 s this.1 hz
  · show w0.m.size - 4096 * s ≤ (wb1 s).length
    have h1' : 4096 * s < w0.m.size := h1
    have h2' : w0.m.size < 4096 * (s + 1) := h2
    have hn : s ∉ S := fun h => by have := hSin s h; omega
    rw [hwb s hn]
    exact c16 s h1' h2'

theorem po_pageOverflow_chunk0 (pg : List w8) : pageOverflow (pageChunk pg 0) = pageOverflow pg := by
  unfold pageOverflow pageHdr bytesAt pageChunk
  simp only [Nat.mul_zero, List.drop_zero, List.take_take]
  rfl

/-- **The new high-water mark's pages inside the file** (D-K, maintainer 13): the slots from the
committed mark (inside the file, `wdbOK`) to the new one are dirty pages' (`markCov`), which the
write put inside the file. -/
theorem cm_pub_hwm (D : Data) (X : WX) (w : WDb) (Pg : Pages) (m' : OsMeta)
    (hpg : cmPubPg D X w Pg) (hok : wdbOK w) (hm' : w.m.size ≤ m'.size)
    (hin : ∀ s ∈ bufSlots X.t.bufs, 4096 * (s + 1) ≤ m'.size) :
    (pubC w.C X.t.mv Pg).hwm * 4096 ≤ m'.size := by
  have hmc := hpg.2.2.2.2.2.2.2.2.2
  have h3 := hok.2.2.1
  rw [pubC_hwm]
  by_cases h : X.t.mv.pgid'.toNat ≤ w.C.hwm
  · have : X.t.mv.pgid'.toNat * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ h
    omega
  · have := hin _ (hmc (X.t.mv.pgid'.toNat - 1) (by omega) (by omega))
    have e : X.t.mv.pgid'.toNat - 1 + 1 = X.t.mv.pgid'.toNat := by omega
    rw [e] at this
    omega

/-- **The publish's pure facts** (U10l; was U10k's open lemma): after the write (the file `m'`,
the slots' bytes `wb'`) and the meta write (the file `m''`), `commitStep_commit`'s premises for
the published slots `S = SB.filter (pubP w X Pg)`, and `wdbOK` of the published writer side (the
rest of the written slots and the tail `T` among its `W` slots, its committed state
`pubC w.C X.t.mv Pg`). The mark's clause is `cm_pub_hwm`'s. -/
theorem cm_pub_ok (D : Data) (X : WX) (w : WDb) (b : Loc) (l : Nat) (Pg : Pages)
    (m' m'' : OsMeta) (wb' : Nat → List w8) (hpre : cmPubPre D X w) (hpg : cmPubPg D X w Pg)
    (htx : X.t.mv.txid' = w.wtxid) (hok : wdbOK w) (hms : w.ms = some (b, l))
    (hmapl : X.t.mv.pgid'.toNat * 4096 ≤ l) (hflpg : w.C.flpg = none)
    (hm' : w.m.size ≤ m'.size ∧ m'.size ≤ max w.m.size l ∧ m'.maps = w.m.maps ∧
      ∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, 4096 * (s + 1) ≤ m'.size →
        (wb' s).length = 4096)
    (hm'' : m''.size = m'.size ∧ m''.maps = m'.maps) (hsz63 : m'.size < 2 ^ 63)
    (hin : ∀ s ∈ bufSlots X.t.bufs, 4096 * (s + 1) ≤ m'.size)
    (hch : ∀ id pg, X.t.bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
      wb' (id.toNat + j) = pageChunk pg j)
    (hpart : ∀ s, 4096 * s < m'.size → m'.size < 4096 * (s + 1) →
      m'.size - 4096 * s ≤ (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb s).length) :
    cpOK w.C w.fl b l X.t.mv Pg D ((bufSlots X.t.bufs).filter (pubP w X Pg)) wb' ∧
    wdbOK ((w.reslot m'' ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s) ++
        (cmTail w (bufSlots X.t.bufs) l ++
          wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l)))
      (wbUpd ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s)) wb'
        (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb))).withC (pubC w.C X.t.mv Pg)) := by
  obtain ⟨-, hsub, -, -, hinW⟩ := cm_write_pre D X w b l hpre hok hms hmapl
  have hml : mapLen w.ms = l := by rw [hms]; rfl
  have hsubT : ∀ s ∈ bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l, s ∈ w.W := by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hsub s h
    · exact ((mem_cmTail _ _ _ s).1 h).2.1
  have hall := cm_unpub_ok w m'' (bufSlots X.t.bufs) (cmTail w (bufSlots X.t.bufs) l)
    (pubP w X Pg) wb' hok hsubT (by omega) (by rw [hml]; omega) (by omega)
    (by rw [hm''.2, hm'.2.2.1]) (fun s hs hz => hm'.2.2.2 s hs (by omega))
    (cm_rest w _ l hinW) hflpg (fun s h1 h2 => ?_)
  rotate_left
  · -- the partial last page: no dirty page's slot (those lie inside the file)
    rw [hm''.1] at h1 h2
    have hnSB : s ∉ bufSlots X.t.bufs := fun h => by have := hin s h; omega
    have e : ∀ P : Nat → Bool, s ∉ (bufSlots X.t.bufs).filter P :=
      fun P h => hnSB (List.mem_filter.1 h).1
    unfold wbUpd
    rw [if_neg (e _), if_neg (e _), hm''.1]
    exact hpart s h1 h2
  refine ⟨cm_cpOK D X w b l Pg wb' hpre hpg htx hok hmapl
    (fun s hs => hm'.2.2.2 s (List.mem_append_left _ hs) (hin s hs)) hch, ?_⟩
  have hpre' := hpre
  obtain ⟨-, hb, hnd, hsl, -, -, -, -, -, -⟩ := hpre'
  have hpg' := hpg
  obtain ⟨-, htree, -, hdrop, hnp, hfb, -, hslots, hflp, -⟩ := hpg'
  have hc4 := hok.2.2.2.1
  have hc5 := hok.2.2.2.2.1
  have hhwmE : (pubC w.C X.t.mv Pg).hwm = X.t.mv.pgid'.toNat := pubC_hwm _ _ _
  have hnotSB : ∀ s ∈ cmTail w (bufSlots X.t.bufs) l ++
      wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l), s ∉ bufSlots X.t.bufs := by
    intro s hs hSB
    rcases List.mem_append.1 hs with h | h
    · exact ((mem_cmTail _ _ _ s).1 h).2.2.2 hSB
    · simp only [wMinus, List.mem_filter, decide_eq_true_eq] at h
      exact h.2 (List.mem_append_left _ hSB)
  -- a new tree slot that was a `W` slot is published
  have hpubW : ∀ s, s ∈ w.W → s ∈ treeSlots (pubC w.C X.t.mv Pg) →
      s ∈ bufSlots X.t.bufs ∧ pubP w X Pg s = true := by
    intro s hs ht
    obtain ⟨-, -, c3, c4⟩ := (hc4 s).1 hs
    have hns : s ∉ slotsOf w.C w.fl := by
      rw [mem_slotsOf]; rintro (h | h)
      · exact c3 h
      · exact c4 h
    rcases hslots s ht with h | h
    · exact absurd h hns
    · exact ⟨h, by simp only [pubP, decide_eq_true_eq]; exact ⟨ht, hns⟩⟩
  have := wdbOK_withC_pub _ (pubC w.C X.t.mv Pg) ((bufSlots X.t.bufs).filter (pubP w X Pg))
    ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s) ++
        (cmTail w (bufSlots X.t.bufs) l ++
          wMinus w.W (bufSlots X.t.bufs ++ cmTail w (bufSlots X.t.bufs) l)))
    (wbUpd ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s)) wb'
        (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb)) hall
    (fun s => ?_) (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_) ?_ (fun s hs hn => ?_)
    hdrop (fun x hx ht => ?_) (fun f hf => ?_) ?_ ?_ (fun b' l' e => ?_) (fun s hs => ?_)
    (fun x hx => ?_)
  · exact this
  · -- the `W` slots without the published ones
    show _ ↔ _ ∈ (bufSlots X.t.bufs).filter (pubP w X Pg) ++ _ ∧ _
    constructor
    · intro h
      refine ⟨List.mem_append_right _ h, fun hp => ?_⟩
      have hP := (List.mem_filter.1 hp).2
      rcases List.mem_append.1 h with h' | h'
      · have := (List.mem_filter.1 h').2
        rw [hP] at this; cases this
      · exact hnotSB s h' (List.mem_filter.1 hp).1
    · rintro ⟨h, hn⟩
      rcases List.mem_append.1 h with h' | h'
      · exact absurd h' hn
      · exact h'
  · -- the bytes off the published slots
    show _ = wbUpd _ wb' _ s
    unfold wbUpd
    rw [if_neg hs]
  · show 4096 * (s + 1) ≤ m''.size
    rw [hm''.1]; exact hin s (List.mem_filter.1 hs).1
  · have := (List.mem_filter.1 hs).2
    simp only [pubP, decide_eq_true_eq] at this
    exact this.1
  · show (pubC w.C X.t.mv Pg).hwm * 4096 ≤ m''.size
    rw [hm''.1]
    exact cm_pub_hwm D X w Pg m' hpg hok hm'.1 hin
  · have hW : s ∈ w.W := (mem_cm_lists w.W _ _ (pubP w X Pg) hsubT s).1 hs
    intro ht
    obtain ⟨h1, h2⟩ := hpubW s hW ht
    exact hn (List.mem_filter.2 ⟨h1, h2⟩)
  · show False
    rcases hslots _ ht with h | h
    · rw [mem_slotsOf] at h
      rcases h with h | h
      · exact hc5 x hx h
      · exact hnp _ ht h
    · have hlt : x.toNat < 2 ^ 64 := x.isLt
      have := (hsl _ h).2.2
      apply this
      have e : W64 ((x.toNat : Nat) : Int) = x := by simp [W64]
      rw [e]; exact hx
  · obtain ⟨pg, hbp, hcur⟩ := hflp f hf
    have hcur' := hcur
    obtain ⟨h2f, hend, hlen, -, -, -, -, -, hext, -⟩ := hcur' f hf
    have hflt : f < 2 ^ 64 := by
      rw [hhwmE] at hend; have := X.t.mv.pgid'.isLt; omega
    have hfid : (W64 (f : Int)).toNat = f := po_W64_toNat f hflt
    obtain ⟨-, hl, -, -⟩ := hb _ _ hbp
    have hwb1 : ∀ j < 1 + pageOverflow pg, wbUpd ((bufSlots X.t.bufs).filter
        (fun s => !pubP w X Pg s)) wb' (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb) (f + j) =
        pageChunk pg j := by
      intro j hj
      have hm : f + j ∈ bufSlots X.t.bufs :=
        (mem_bufSlots _ _).2 ⟨_, pg, hbp, by rw [hfid]; omega, by rw [hfid]; omega⟩
      have hnp' : pubP w X Pg (f + j) = false := by
        simp only [pubP, decide_eq_false_iff_not]
        rintro ⟨ht, -⟩
        exact (hext (f + j) (by omega) (by omega)).1
          ((mem_pagesSlots_iff _ _).1 ht)
      unfold wbUpd
      rw [if_pos (List.mem_filter.2 ⟨hm, by simp [hnp']⟩)]
      have := hch _ pg hbp j hj
      rw [hfid] at this
      exact this
    have e : extentBytes (wbUpd ((bufSlots X.t.bufs).filter (fun s => !pubP w X Pg s)) wb'
        (wbUpd (cmTail w (bufSlots X.t.bufs) l) wb' w.wb)) f = pg := by
      unfold extentBytes
      have h0 := hwb1 0 (by omega)
      rw [Nat.add_zero] at h0
      rw [h0, po_pageOverflow_chunk0]
      refine (po_flatMap_congr fun s hs => ?_).trans
        (flatMap_pageChunk pg f (1 + pageOverflow pg) (by rw [hl]))
      have := List.mem_range'_1.1 hs
      have e2 := hwb1 (s - f) (by omega)
      rw [show f + (s - f) = s by omega] at e2
      exact e2
    show flCurOK w.fl (pubC w.C X.t.mv Pg) _
    rw [e]; exact hcur
  · show (pubC w.C X.t.mv Pg).txid + 1 < 2 ^ 64
    have := htree.2.2.2.2.2
    omega
  · rw [pubC_hwm]
    exact X.t.mv.pgid'.isLt
  · show (pubC w.C X.t.mv Pg).hwm * 4096 ≤ l'
    rw [show (w.reslot m'' _ _).ms = w.ms from rfl, hms] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    rw [hhwmE]; omega
  · show s < (pubC w.C X.t.mv Pg).hwm
    rcases hs with h | h
    · obtain ⟨id, pg, hp, h1, h2⟩ := (po_mem_pagesSlots _ _).1 h
      have := htree.2.2.2.1 id pg hp
      omega
    · obtain ⟨t, pd, x, hp, hx, rfl⟩ := (pp_mem_pendSlots' w.fl s).1 h
      apply hfb.2.1 t pd x hp hx
      rcases hfb.2.2.1 t pd hp with h | ⟨h, -⟩
      · exact h
      · rw [pubC_txid]
        have : X.t.mv.txid'.toNat = w.C.txid + 1 := (cm_cpOK D X w b l Pg wb' hpre hpg htx hok
          hmapl (fun s hs => hm'.2.2.2 s (List.mem_append_left _ hs) (hin s hs)) hch).1
        simp only [Option.some.injEq] at h
        omega
  · exact hfb.1 x hx

end pure

end bbolt
end EtcdGrove
end Perennial
