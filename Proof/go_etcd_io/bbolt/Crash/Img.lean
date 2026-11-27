/- Lean-first (no Rocq counterpart).

# A reference image of a committed state from the bytes of its pages

`RefImg X C` (`Crash/Good.lean`) is what the crash invariant's abstract state keeps of the committed
state `C`: a byte list `X` whose metas are `C`'s and whose tree pages, walked from `C`'s root, are
`C`'s pages. At `Commit`'s commit point the new committed state's reference image is the file's
bytes with the new meta in its slot; `treePages_of_agree` gives its tree from the bytes of each of
its pages (old pages: synced, the previous image's; new pages: just written), without a previous
image of the same state (`treePages_transfer` is the version from one). `bDur_commit_of` is H1's
`bDur_commit_point` with that image (`cpImg`): from the idle facts of the committed state and the
file's bytes after the commit's first `fdatasync` (every byte durable), the new state's meta, tree
and pages, the committing facts.
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Phases

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs Spill Read
open go_etcd_io.bbolt.internal.common

section img
variable [GooseExts]

/-- **A file page whose bytes are a page's** (`pg`, a whole number of pages by its header): the
file's page there is `pg`. -/
theorem filePage_of_agree (ys pg : List w8) (id : Nat) (hl : pg.length = (1 + pageOverflow pg) * 4096)
    (hag : ∀ k < pg.length, ys[4096 * id + k]? = pg[k]?) : filePage ys id = pg := by
  have hb : ∀ L, L ≤ pg.length → bytesAt ys (4096 * id) L = pg.take L := by
    intro L hL
    apply List.ext_getElem?; intro j
    by_cases hj : j < L
    · rw [bytesAt_getElem? _ _ _ _ hj, hag j (by omega), List.getElem?_take, if_pos hj]
    · unfold bytesAt; rw [List.getElem?_take, if_neg hj, List.getElem?_take, if_neg hj]
  have h4 : 4096 ≤ pg.length := by rw [hl, Nat.add_mul]; omega
  unfold filePage
  rw [hb 4096 h4, cr_pageOverflow_take _ _ (by omega), ← hl, hb _ (Nat.le_refl _),
    List.take_of_length_le (Nat.le_refl _)]

/-- A tree page of a well-formed committed state: its id at least 2, a whole number of pages, its
extent inside the high-water mark (`refImg_page` without an image). -/
theorem tree_page_facts {C : CommitSt} (htree : treeOK C) {id : Nat} {pg : List w8}
    (hp : C.pages !! id = some pg) :
    2 ≤ id ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧ id + (1 + pageOverflow pg) ≤ C.hwm := by
  obtain ⟨⟨hwf, -⟩, htp, -, hext, -, -⟩ := _root_.id htree
  have hhas : treeHas C.pages C.root id := by
    have h1 := hp
    rw [← htp, treePages_lookup] at h1
    split at h1
    · assumption
    · cases h1
  have hlen : pg.length = (1 + pageOverflow pg) * 4096 := by
    cases treeHas_treeWF C.pages C.hwm hhas hwf with
    | page _ pg' _ _ hpg' _ hl _ => rw [hp] at hpg'; cases hpg'; exact hl
  exact ⟨wt_tree_page_ge2 C htree id pg hp, hlen, hext id pg hp⟩

/-- **Bytes holding each of `C`'s tree pages have `C`'s tree** (`treePages_transfer` from the
pages' bytes). -/
theorem treePages_of_agree (ys : List w8) (C : CommitSt) (htree : treeOK C)
    (hlen : C.hwm * 4096 ≤ ys.length)
    (hag : ∀ id pg, C.pages !! id = some pg → ∀ k < pg.length, ys[4096 * id + k]? = pg[k]?) :
    treePages (filePages ys C.hwm) C.root = C.pages := by
  obtain ⟨⟨hwf, -⟩, htp, -⟩ := _root_.id htree
  have hpage : ∀ id pg, C.pages !! id = some pg → filePage ys id = pg := fun id pg hp =>
    filePage_of_agree ys pg id (tree_page_facts htree hp).2.1 (hag id pg hp)
  have hle : pagesLe C.pages (filePages ys C.hwm) := by
    intro id pg hpg
    obtain ⟨-, -, he⟩ := tree_page_facts htree hpg
    rw [filePages_lookup, if_pos (by omega), hpage id pg hpg]
  apply GMap.ext
  intro id
  show treePages _ C.root !! id = C.pages !! id
  rw [treePages_lookup]
  by_cases h : treeHas (filePages ys C.hwm) C.root id
  · rw [if_pos h]
    have h' := treeHas_of_le hle C.hwm h hwf
    obtain ⟨pg, hpg⟩ := wt_treeHas_page h'
    rw [hpg]; exact hle id pg hpg
  · rw [if_neg h]
    rcases hc : C.pages !! id with _ | pg
    · rfl
    · exfalso; apply h
      have h1 : treePages C.pages C.root !! id = some pg := by rw [htp]; exact hc
      rw [treePages_lookup] at h1
      split at h1
      · rename_i ht; exact treeHas_le hle ht
      · cases h1

/-! ## The commit point's reference image -/

/-- `xs` with `ys` from `off`. -/
def bytesSet (xs : List w8) (off : Nat) (ys : List w8) : List w8 :=
  xs.take off ++ ys ++ xs.drop (off + ys.length)

theorem bytesSet_length (xs ys : List w8) (off : Nat) (h : off + ys.length ≤ xs.length) :
    (bytesSet xs off ys).length = xs.length := by
  unfold bytesSet; simp only [List.length_append, List.length_take, List.length_drop]; omega

theorem bytesSet_getElem? (xs ys : List w8) (off b : Nat) (h : off + ys.length ≤ xs.length) :
    (bytesSet xs off ys)[b]? =
      if off ≤ b ∧ b < off + ys.length then ys[b - off]? else xs[b]? := by
  unfold bytesSet
  have ht : (xs.take off).length = off := by simp only [List.length_take]; omega
  by_cases h1 : b < off
  · rw [if_neg (by omega), List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_take, if_pos h1]
  · rw [List.append_assoc, List.getElem?_append_right (by omega), ht]
    by_cases h2 : b - off < ys.length
    · rw [if_pos (by omega), List.getElem?_append_left h2]
    · rw [if_neg (by omega), List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega

/-- **The new committed state's reference image at the commit point**: the file's values, the new
meta in its slot. -/
def cpImg (s : CSt) (C' : CommitSt) : List w8 :=
  bytesSet (s.bs.map Prod.fst) (4096 * (C'.txid % 2)) (C'.slot C'.txid)

/-- A byte of a run of `4096`-byte chunks. -/
theorem flatMap_chunk_getElem? (g : Nat → List w8) :
    ∀ (n a k : Nat), (∀ j < n, (g (a + j)).length = 4096) → k < 4096 * n →
      ((List.range' a n).flatMap g)[k]? = (g (a + k / 4096))[k % 4096]?
  | 0, _, _, _, hk => by omega
  | n + 1, a, k, hg, hk => by
    rw [List.range'_succ, List.flatMap_cons]
    have ha : (g a).length = 4096 := by simpa using hg 0 (by omega)
    by_cases h : k < 4096
    · rw [List.getElem?_append_left (by omega), Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h,
        Nat.add_zero]
    · rw [List.getElem?_append_right (by omega), ha,
        flatMap_chunk_getElem? g n (a + 1) (k - 4096)
          (fun j hj => by rw [show a + 1 + j = a + (j + 1) by omega]; exact hg (j + 1) (by omega))
          (by omega)]
      rw [show a + 1 + (k - 4096) / 4096 = a + k / 4096 by omega,
        show (k - 4096) % 4096 = k % 4096 by omega]

theorem slot_length {C : CommitSt} (h : C.metaOk) (i : Nat) : (C.slot i).length = 4096 := by
  unfold CommitSt.slot; split
  · exact h.1
  · exact h.2.1

set_option maxRecDepth 10000 in
/-- **The commit point's committing facts** (`bDur_commit_point` with `cpImg`; see the file
header): from the idle facts of `a`, the file's bytes all durable (the commit's first `fdatasync`)
with the crash size bounds agreeing (`DB.grow`'s sync), and the new committed state `C'` (its txid
one more and below `2 ^ 62`, its other slot `a.cur`'s, its meta well formed with zero tail, its
tree well formed, no synced freelist page, its pages inside the file, each one of `a.cur`'s or, in
whole slots of `g`, the file's bytes). -/
theorem bDur_commit_of (a : BAbs) (s : CSt) (hb : s.busy = .idle) (hD : BDur a s)
    (hph : a.phase = .idle) (hdur : ∀ (k : Nat) (x : ByteG), s.bs[k]? = some x → x = durB x.1)
    (hlh : s.m.lo = s.m.hi) (C' : CommitSt) (g : Nat → List w8)
    (htx : C'.txid = a.cur.txid + 1) (htx2 : C'.txid < 2 ^ 62)
    (hsl : ∀ i, i % 2 ≠ C'.txid % 2 → C'.slot i = a.cur.slot i)
    (hmok : C'.metaOk) (htree : treeOK C') (hfl : C'.flpg = none)
    (hhwm : C'.hwm * 4096 ≤ s.m.size)
    (htail : ∀ k, 80 ≤ k → k < 4096 → (C'.slot C'.txid)[k]? = some 0)
    (hnew : ∀ id pg, C'.pages !! id = some pg → a.cur.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, (g (id + j)).length = 4096 ∧ ∀ k < 4096,
          (s.bs[4096 * (id + j) + k]?).map Prod.fst = (g (id + j))[k]?) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap g)) :
    BDur { cur := C', prev := a.cur, xcur := cpImg s C', xprev := a.xcur, phase := .committing }
      s := by
  have hD' := hD
  rw [bDur_idle_iff hph] at hD'
  obtain ⟨hW, hR, hm, hd, hh, -, -, -⟩ := hD'
  have hl : s.bs.length = s.m.size := hW.1
  have hlo : s.m.lo ≤ s.m.size := hW.2.2.1
  have hhi : s.m.size ≤ s.m.hi := hW.2.2.2
  have h3 := refImg_hwm hR
  have hXl := hR.len
  have hsz : 12288 ≤ s.m.size := by have := Nat.mul_le_mul_right 4096 h3; omega
  have hsll : (C'.slot C'.txid).length = 4096 := slot_length hmok _
  have hp2 : C'.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  have hin : 4096 * (C'.txid % 2) + (C'.slot C'.txid).length ≤ (s.bs.map Prod.fst).length := by
    rw [List.length_map, hl, hsll]; omega
  have hX : ∀ b, (cpImg s C')[b]? = if 4096 * (C'.txid % 2) ≤ b ∧ b < 4096 * (C'.txid % 2) + 4096
      then (C'.slot C'.txid)[b - 4096 * (C'.txid % 2)]? else (s.bs[b]?).map Prod.fst := by
    intro b; unfold cpImg; rw [bytesSet_getElem? _ _ _ _ hin, hsll, List.getElem?_map]
  have hXlen : (cpImg s C').length = s.m.size := by
    unfold cpImg; rw [bytesSet_length _ _ _ hin, List.length_map, hl]
  -- a synced byte's value in the file
  have hps : ∀ b v, PSync s b v → (s.bs[b]?).map Prod.fst = some v := by
    intro b v h; rw [h.1]; rfl
  have hxc : ∀ b, b < a.xcur.length → some (xb a.xcur b) = a.xcur[b]? := fun b hb => xb_some _ b hb
  -- bytes past the meta pages
  have hX2 : ∀ b, 8192 ≤ b → (cpImg s C')[b]? = (s.bs[b]?).map Prod.fst := by
    intro b hb; rw [hX, if_neg (by omega)]
  -- the other slot: `a.cur`'s current slot, synced
  have hoth : ∀ b, b < 8192 → ¬ (4096 * (C'.txid % 2) ≤ b ∧ b < 4096 * (C'.txid % 2) + 4096) →
      (cpImg s C')[b]? = some (xb a.xcur b) := by
    intro b hb hn; rw [hX, if_neg hn]; exact hps b _ (hm b hb)
  -- the slots
  have hslot : ∀ i < 2, bytesAt (cpImg s C') (4096 * i) 4096 = C'.slot i := by
    intro i hi
    apply List.ext_getElem?; intro k
    by_cases hk : k < 4096
    · rw [bytesAt_getElem? _ _ _ _ hk]
      by_cases hi' : i = C'.txid % 2
      · subst hi'
        rw [hX, if_pos (by omega), show 4096 * (C'.txid % 2) + k - 4096 * (C'.txid % 2) = k by omega,
          ← slot_mod]
      · rw [hoth _ (by omega) (by omega), hsl i (by omega), refImg_slot hR i,
          Nat.mod_eq_of_lt hi, bytesAt_getElem? _ _ _ _ hk, ← hxc _ (by omega)]
    · rw [List.getElem?_eq_none (by unfold bytesAt; simp only [List.length_take]; omega),
        List.getElem?_eq_none (by rw [slot_length hmok]; omega)]
  -- the pages
  have hag : ∀ id pg, C'.pages !! id = some pg → ∀ k < pg.length,
      (cpImg s C')[4096 * id + k]? = pg[k]? := by
    intro id pg hp k hk
    obtain ⟨hid, hpl, hpe⟩ := tree_page_facts htree hp
    rw [hX2 _ (by omega)]
    rcases hnew id pg hp with hold | ⟨hg, hpg⟩
    · obtain ⟨hfp, -, -, he⟩ := refImg_page hR hold
      have hpd : protData a.xcur a.cur (4096 * id + k) := .inl ⟨id, pg, hold, by omega, by omega⟩
      rw [hps _ _ (hd _ hpd), ← hfp]
      unfold filePage
      rw [bytesAt_getElem? _ _ _ _ (by rw [← cr_filePage_overflow, hfp, ← hpl]; exact hk)]
      have hb : 4096 * id + k < a.xcur.length := by
        rw [hpl] at hk; have := Nat.mul_le_mul_right 4096 he; rw [Nat.add_mul] at this; omega
      exact hxc _ hb
    · have hj : k / 4096 < 1 + pageOverflow pg := by rw [hpl] at hk; omega
      have e : 4096 * id + k = 4096 * (id + k / 4096) + k % 4096 := by omega
      have hc := flatMap_chunk_getElem? g (1 + pageOverflow pg) id k (fun j hj' => (hg j hj').1)
        (by rw [hpl] at hk; omega)
      rw [← hpg] at hc
      rw [e, (hg (k / 4096) hj).2 (k % 4096) (Nat.mod_lt _ (by omega)), hc]
  have hRc : RefImg (cpImg s C') C' := by
    refine ⟨⟨?_, ?_, ?_⟩, hmok, htree, ?_, ?_, ?_, htx2, ?_⟩
    · have := hslot 0 (by omega); rw [Nat.mul_zero] at this; rw [this]; rfl
    · have := hslot 1 (by omega); rw [Nat.mul_one] at this; rw [this]; rfl
    · exact (treePages_of_agree _ C' htree (by rw [hXlen]; exact hhwm) hag).symm
    · intro f hf; rw [hfl] at hf; cases hf
    · rw [hXlen]; exact hhwm
    · rw [htx]; exact Nat.succ_pos _
    · intro j hj k hk1 hk2 v hv
      by_cases hj' : j = C'.txid % 2
      · subst hj'
        rw [hX, if_pos (by omega), show 4096 * (C'.txid % 2) + k - 4096 * (C'.txid % 2) = k by omega,
          htail k hk1 hk2] at hv
        exact (Option.some.inj hv).symm
      · rw [hoth _ (by omega) (by omega)] at hv
        rw [← Option.some.inj hv]
        exact refImg_tail hR hj hk1 hk2
  have hdc : ∀ b, protData (cpImg s C') C' b → PSync s b (xb (cpImg s C') b) := by
    intro b hpb
    obtain ⟨hb1, hb2⟩ := protData_range hRc hpb
    have hbl : b < s.bs.length := by omega
    have hx := hdur b s.bs[b] (List.getElem?_eq_getElem hbl)
    have hxb : xb (cpImg s C') b = s.bs[b].1 := by
      have h1 := xb_some (cpImg s C') b (by omega)
      rw [hX2 b hb1, List.getElem?_eq_getElem hbl] at h1
      exact Option.some.inj h1
    refine ⟨by rw [hxb, List.getElem?_eq_getElem hbl, ← hx], fun t off data n h => ?_⟩
    rw [hb] at h; cases h
  have hsl' : C'.slot (C'.txid + 1) = a.cur.slot a.cur.txid := by
    have h2 : (C'.txid + 1) % 2 = a.cur.txid % 2 := by omega
    rw [hsl _ (by omega), slot_mod a.cur (C'.txid + 1), slot_mod a.cur a.cur.txid, h2]
  have hlo' : s.m.lo = s.m.size := by omega
  have hhi' : s.m.hi = s.m.size := by omega
  have hhc : C'.hwm * 4096 ≤ s.m.lo := by omega
  exact bDur_commit_point a hph s hb hD C' (cpImg s C') hRc htx hsl' hdc hhc hlo' hhi'

end img

end bbolt
end EtcdGrove
end Perennial
