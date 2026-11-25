/- Lean-first (no Rocq counterpart).

# bbolt's crash invariant on the per-byte file model: the durability predicate

`BDur a s`: a pure predicate on bbolt's abstract crash state `a` (`BAbs`: the committed state
`cur`, the previous one `prev`, reference images of both, and a phase) and the generic state `s`
of its database file (`CSt`, `Proof/os/CrashSt.lean`), such that every file a crash may leave is
good (`bDur_okS`, through `FileOkS` under the premise `BoltCrashWhole` of the file's inode):
* **idle** (no commit between its commit point and its second `fdatasync`; the commit's page
  writes and `grow` happen here): a good image of `cur`'s data;
* **committing** (from just before the new meta's `pwrite` starts to the end of the second
  `fdatasync`; `cur` is the new committed state, `prev` the one before): of `cur`'s or `prev`'s;
* **init** (`DB.init`'s two writes and syncs): a file `needsInit` accepts, or `init`'s whole
  image (the empty data).

**The facts** (`BDur`), per byte, from the candidates a crash picks from (`crashCands`):
* idle: both meta pages and `cur`'s protected data bytes (`protData`: its tree pages' and synced
  freelist page's extents) are synced (`PSync`: one candidate, the reference image's byte, and no
  write in flight on them), below the smallest size since the last sync (`hwm · 4096 ≤ lo`); the
  slot the next commit writes is `metaPre` (if its magic and version are right, page size 4096 and
  an older txid: the premise fixes only a validating slot's first 56 bytes, so its checksum may be
  torn).
* committing: `prev`'s meta slot and both states' protected data bytes synced; the other slot,
  `cur`'s, in flight (`CandOV`: each byte its old value then only its new one, the first new stamp
  the same for all, so each state "as of one change" is the old slot or the new one); the file's
  size has not moved since its last sync (`vmeta`'s bounds the size).
* init: at most four pages, every candidate of every byte zero or `init`'s byte.

Unprotected bytes may hold anything; the meta pages' tails (bytes 80 to 4096) are zero in both
reference images, and so in every crash image (`metaOk`'s probes at offsets 1024 and 2048).

**The size.** The ghost state (`OsMeta`) does not record the file extension's crash sizes
(`OsFile.szCrash`: an `ftruncate`'s target exactly), only their bounds `[lo, hi]`, so inside
`DB.grow`'s window (`lo < hi`, between its `Truncate` and its `Sync`) a crash image's size is known
to be at least `hwm · 4096` but not a whole number of pages. `bDur_okS` asks `lo = hi` of an idle
state (true everywhere else); `bDur_okSU` covers every state, without whole pages.
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Good

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open go_etcd_io.bbolt.internal.common

section dur
variable [GooseExts]

/-! ## The abstract state -/

/-- The phase of bbolt's file. -/
inductive BPhase where
  | idle
  | committing
  | init
  deriving DecidableEq

/-- **bbolt's abstract crash state**: the committed state `cur`, the previous one `prev`, their
reference images `xcur`, `xprev` (`RefImg`), and the phase. -/
structure BAbs where
  cur : CommitSt
  prev : CommitSt
  xcur : List w8
  xprev : List w8
  phase : BPhase

/-! ## Per-byte facts -/

/-- Byte `b` is synced with the value `v`: its one candidate `v`, no write in flight on it. -/
def PSync (s : CSt) (b : Nat) (v : w8) : Prop :=
  s.bs[b]? = some (durB v) ∧
    ∀ t off data n, s.busy = .write t off data n → b < off ∨ off + data.length ≤ b

/-- The candidates `c` of a byte of a meta slot being written: the old value `o` (stamp 0), then
only the new one `v`; if any (`N = some N0`), one stamped `N0` and none earlier. -/
def CandOV (c : Cands) (o v : w8) (N : Option Nat) : Prop :=
  ∃ L, c = (o, 0) :: L ∧ (∀ q ∈ L, q.1 = v) ∧
    match N with
    | none => L = []
    | some N0 => (v, N0) ∈ L ∧ ∀ q ∈ L, N0 ≤ q.2

/-- What the specs keep of a state, and the change in flight inside the file or growing it. -/
def BWf (s : CSt) : Prop :=
  s.bs.length = s.m.size ∧ BusyIn s ∧ s.m.lo ≤ s.m.size ∧ s.m.size ≤ s.m.hi

/-- A write in flight lies inside the file. -/
def WrIn (s : CSt) : Prop :=
  ∀ t off data n, s.busy = .write t off data n → off + data.length ≤ s.m.size

/-- `X`'s byte `b`. -/
abbrev xb (X : List w8) (b : Nat) : w8 := X.getD b 0

/-- **The idle facts** of the committed state `C` with reference image `X` (see the file header). -/
def IdleOk (C : CommitSt) (X : List w8) (s : CSt) : Prop :=
  RefImg X C ∧ metaPre (metaOf (C.slot (C.txid + 1))) C.txid ∧
    (∀ b < 8192, PSync s b (xb X b)) ∧ (∀ b, protData X C b → PSync s b (xb X b)) ∧
    C.hwm * 4096 ≤ s.m.lo ∧ s.m.size % 4096 = 0 ∧ WrIn s

/-- **The committing facts**: `prev` (`P`, image `Xp`) and the new `cur` (`C`, image `Xc`); see the
file header. -/
def CommitOk (C P : CommitSt) (Xc Xp : List w8) (s : CSt) : Prop :=
  RefImg Xp P ∧ RefImg Xc C ∧ C.txid = P.txid + 1 ∧ C.slot (C.txid + 1) = P.slot P.txid ∧
    metaPre (metaOf (P.slot (P.txid + 1))) P.txid ∧
    (∀ k < 4096, PSync s (4096 * (P.txid % 2) + k) (xb Xp (4096 * (P.txid % 2) + k))) ∧
    (∃ N : Option Nat, ∀ k < 4096, ∃ c, crashCands s (4096 * (C.txid % 2) + k) = some c ∧
      CandOV c (xb Xp (4096 * (C.txid % 2) + k)) (xb Xc (4096 * (C.txid % 2) + k)) N) ∧
    (∀ b, protData Xp P b → PSync s b (xb Xp b)) ∧ (∀ b, protData Xc C b → PSync s b (xb Xc b)) ∧
    P.hwm * 4096 ≤ s.m.lo ∧ C.hwm * 4096 ≤ s.m.lo ∧ s.m.size % 4096 = 0 ∧
    s.vmeta.lo = s.m.size ∧ s.vmeta.hi = s.m.size ∧ WrIn s

/-- **The init facts**: every candidate of the first four pages zero or `init`'s byte, the page
cache too, and at most four pages. -/
def InitOk (s : CSt) : Prop :=
  (∀ b < 16384, ∃ c, crashCands s b = some c ∧ ∀ q ∈ c, q.1 = 0 ∨ q.1 = initByte b) ∧
    (∀ b x, s.bs[b]? = some x → x.1 = 0 ∨ x.1 = initByte b) ∧ s.vmeta.hi ≤ 16384

/-- **The durability predicate** (see the file header). -/
def BDur (a : BAbs) (s : CSt) : Prop :=
  BWf s ∧
    match a.phase with
    | .idle => IdleOk a.cur a.xcur s
    | .committing => CommitOk a.cur a.prev a.xcur a.xprev s
    | .init => InitOk s

/-- **What every crash image of a state is**, by phase (whole pages). -/
def bCrash (a : BAbs) (f : OsFile) : Prop :=
  match a.phase with
  | .idle => bGood (treeData a.cur) f
  | .committing => bGood (treeData a.cur) f ∨ bGood (treeData a.prev) f
  | .init => bGoodInit f ∨ bGood ∅ f

/-- `bCrash` without whole pages for the idle and committing phases. -/
def bCrashU (a : BAbs) (f : OsFile) : Prop :=
  match a.phase with
  | .idle => bGoodU (treeData a.cur) f
  | .committing => bGoodU (treeData a.cur) f ∨ bGoodU (treeData a.prev) f
  | .init => bGoodInit f ∨ bGood ∅ f

/-- The `Good` of the crash invariant at `a`. -/
def bOk (a : BAbs) (fo : Option OsFile) : Prop := ∀ f, fo = some f → bCrash a f

/-- `bOk` without whole pages. -/
def bOkU (a : BAbs) (fo : Option OsFile) : Prop := ∀ f, fo = some f → bCrashU a f

/-! ## The candidates of synced bytes -/

theorem vmeta_lo_of (s : CSt) (hW : BWf s) : s.vmeta.lo = s.m.lo := by
  obtain ⟨-, hbz, hlo, -⟩ := hW
  unfold CSt.vmeta
  rcases hb : s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩
  · rfl
  · simp only [cfMeta, announce_lo]; omega
  · simp only [announce_lo]
    have : s.m.size ≤ sz := by unfold BusyIn at hbz; rw [hb] at hbz; exact hbz
    omega

theorem size_le_vmeta_hi (s : CSt) (hW : BWf s) : s.m.size ≤ s.vmeta.hi := by
  obtain ⟨-, -, -, hhi⟩ := hW
  unfold CSt.vmeta
  rcases s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩
  · exact hhi
  · simp only [cfMeta, announce_hi]; omega
  · simp only [announce_hi]; omega

theorem vmeta_hi_of (s : CSt) (hW : BWf s) (hwr : WrIn s)
    (hnt : ∀ t sz n, s.busy ≠ .trunc t sz n) : s.vmeta.hi = s.m.hi := by
  obtain ⟨-, -, -, hhi⟩ := hW
  unfold CSt.vmeta
  rcases hb : s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩
  · rfl
  · have := hwr t off data n hb
    simp only [cfMeta, announce_hi]; omega
  · exact absurd hb (hnt t sz n)

/-- **A synced byte's candidates**: its one value. -/
theorem psync_cands {s : CSt} {b : Nat} {v : w8} (hW : BWf s) (h : PSync s b v) :
    crashCands s b = some [(v, 0)] ∧ b < s.m.size := by
  obtain ⟨hbs, hnw⟩ := h
  have hb : b < s.m.size := by
    have := (List.getElem?_eq_some_iff.1 hbs).1; rw [hW.1] at this; exact this
  have hbase : baseCands s b = some [(v, 0)] := by
    unfold baseCands; rw [if_pos hb, hbs]; rfl
  refine ⟨?_, hb⟩
  unfold crashCands
  rcases hbs' : s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩
  · exact hbase
  · have hoff : off ≤ s.m.size := by have := hW.2.1; unfold BusyIn at this; rw [hbs'] at this; exact this
    have := hnw t off data n hbs'
    dsimp only
    rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    exact hbase
  · have hsz : s.m.size ≤ sz := by have := hW.2.1; unfold BusyIn at this; rw [hbs'] at this; exact this
    dsimp only
    rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    exact hbase

/-- **A synced byte below the smallest size since the last sync is in every crash image.** -/
theorem view_psync {s : CSt} {f : OsFile} {b : Nat} {v : w8} (hW : BWf s) (hV : BView s f)
    (h : PSync s b v) (hb : b < s.m.lo) : f.contents[b]? = some v := by
  obtain ⟨hc, -⟩ := psync_cands hW h
  have hlo := vmeta_lo_of s hW
  have hbf : b < f.size := by have := hV.lo; omega
  rw [contents_getElem? f b hbf]
  have hpg : pageIn f.size b = true := by
    simp only [pageIn, decide_eq_true_eq]; have := Nat.mul_div_le b 4096; omega
  rcases hV.byte b _ hpg hc with ⟨q, hq⟩ | ⟨h1, -⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at hq; rw [hq.1]
  · omega

/-! ## Meta slots -/

theorem slot_mod (C : CommitSt) (i : Nat) : C.slot i = C.slot (i % 2) := by
  unfold CommitSt.slot; rw [Nat.mod_mod]

/-- A reference image's slots are its bytes. -/
theorem refImg_slot {X : List w8} {C : CommitSt} (hR : RefImg X C) (i : Nat) :
    C.slot i = bytesAt X (4096 * (i % 2)) 4096 := by
  unfold CommitSt.slot
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, hR.img.1, hR.img.2.1]

/-- The slots of `C` with the metas of `ys`. -/
theorem slot_with (C : CommitSt) (ys : List w8) (i : Nat) :
    ({ C with m0 := bytesAt ys 0 4096, m1 := bytesAt ys 4096 4096 } : CommitSt).slot i =
      bytesAt ys (4096 * (i % 2)) 4096 := by
  unfold CommitSt.slot
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

theorem bytesAt_length' (xs : List w8) (a n : Nat) (h : a + n ≤ xs.length) :
    (bytesAt xs a n).length = n := by
  simp [bytesAt]; omega

/-- The first 56 meta bytes of a meta page. -/
theorem metaOf_take56 (pg : List w8) (h : 80 ≤ pg.length) :
    (encode (metaOf pg)).take 56 = (List.range 56).map fun k => pg.getD (16 + k) 0 := by
  unfold metaOf
  rw [ByteEncoding.encode_decode _ (by simp [bytesAt]; omega)]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 56
  · rw [List.getElem?_take, if_pos hk, bytesAt_getElem? pg 16 64 k (by omega)]
    simp [hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 16 + k < pg.length by omega)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- The first 56 meta bytes of slot `j` of a file's raw bytes. -/
theorem rawMeta_take56 (f : OsFile) (j : Nat) :
    (encode (decode (rawMeta f j) : Meta)).take 56 =
      (List.range 56).map fun k => f.cache (4096 * j + 16 + k) := by
  rw [ByteEncoding.encode_decode _ (rawMeta_length f j)]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 56
  · simp [rawMeta, hk, show k < 64 by omega]
  · rw [List.getElem?_eq_none (by simp [rawMeta]; omega), List.getElem?_eq_none (by simp; omega)]

/-- A byte of slot `q` of `X`, read through the slot. -/
theorem bytesAt_getD (X : List w8) (a k : Nat) (hk : k < 4096) (hX : a + 4096 ≤ X.length) :
    (bytesAt X a 4096).getD k 0 = xb X (a + k) := by
  rw [List.getD_eq_getElem?_getD, bytesAt_getElem? _ _ _ _ hk, ← List.getD_eq_getElem?_getD]

/-! ## The value of a slot's byte as of a stamp -/

omit [GooseExts] in
theorem getLast?_map_of (v : w8) :
    ∀ (a : w8 × Nat) (l : List (w8 × Nat)), l ≠ [] → (∀ q ∈ l, q.1 = v) →
      ((a :: l).getLast?.map (·.1)) = some v
  | _, [], h, _ => absurd rfl h
  | _, [x], _, hv => by simp [hv x (by simp)]
  | _, x :: y :: t, _, hv => by
    rw [List.getLast?_cons_cons]
    exact getLast?_map_of v x (y :: t) (by simp) (fun q hq => hv q (List.mem_cons_of_mem _ hq))

/-- **The value as of stamp `n` of a slot byte being written**: the old one before the first new
stamp, the new one from it on. -/
theorem valAt_candOV {c : Cands} {o v : w8} {N : Option Nat} (h : CandOV c o v N) (n : Nat) :
    valAt c n = (match N with | none => o | some N0 => if N0 ≤ n then v else o) := by
  obtain ⟨L, rfl, hv, hN⟩ := h
  unfold valAt
  rw [List.filter_cons_of_pos (by simp)]
  cases N with
  | none =>
    dsimp only at hN ⊢; subst hN; simp
  | some N0 =>
    obtain ⟨hmem, hge⟩ := hN
    dsimp only
    by_cases hn : N0 ≤ n
    · rw [if_pos hn]
      rw [getLast?_map_of v (o, 0) (L.filter (·.2 ≤ n)) ?_ ?_]
      · rfl
      · intro he
        have : (v, N0) ∈ L.filter (·.2 ≤ n) := List.mem_filter.2 ⟨hmem, by simp [hn]⟩
        rw [he] at this; cases this
      · intro q hq; exact hv q (List.mem_filter.1 hq).1
    · rw [if_neg hn]
      have he : L.filter (·.2 ≤ n) = [] := by
        rw [List.filter_eq_nil_iff]; intro q hq; have := hge q hq; simp; omega
      rw [he]; rfl

/-- Every candidate of a slot byte being written is the old or the new value. -/
theorem candOV_mem {c : Cands} {o v : w8} {N : Option Nat} (h : CandOV c o v N) {x : w8} {q : Nat}
    (hq : (x, q) ∈ c) : x = o ∨ x = v := by
  obtain ⟨L, rfl, hv, -⟩ := h
  rcases List.mem_cons.1 hq with e | e
  · exact .inl (Prod.mk.inj e).1
  · exact .inr (hv _ e)

end dur

end bbolt
end EtcdGrove
end Perennial
