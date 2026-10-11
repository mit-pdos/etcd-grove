/-
A cursor on the read path: the pages of its bucket, and its stack.

A cursor's bucket has its pages in the mapping (`data`, page size `ps`, the pages `pages` the
transaction sees, at the fraction `q`: `TxModel.lean`'s `pagesView`), or, for an inline bucket
(root page id 0), one leaf page inside its parent's value (`ip`, bytes `ipg`). `BktView`
records which, and `pageAt` is where page `pid` is and its bytes (what `Bucket.pageNode`
returns, no node being materialized). `bktCtx bl V` is the rest of what the read path reads:
the bucket, its `InBucket` header, its transaction and the database's `data` and `pageSize`
fields (each at some fraction).

`stackOK V pid es`: the stack `es` is a path from page `pid` down: every element refers to a
page (no node), the page at the element's place; a branch's index is one of its elements, and
the next element is that element's child; the last element is a leaf, its index anywhere in
`[-1, count]` (`-1` only for `Last` on an empty leaf, `count` past the end).
-/
module

public import Proof.go_etcd_io.bbolt.TxModel
public import Proof.go_etcd_io.bbolt.KeyOrder
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.Cursor__keyValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- Where a bucket's pages are (see the module doc). -/
structure BktView where
  data : Loc
  ps : w64
  pages : GMap Nat (List w8)
  hwm : Nat
  root : w64
  ip : Loc
  ipg : List w8

/-- Page `pid` of the bucket: its location and bytes. -/
def BktView.pageAt (V : BktView) (pid : w64) : Option (Loc × List w8) :=
  if V.root = W64 0 then (if pid = W64 0 then some (V.ip, V.ipg) else none)
  else (V.pages !! uint.nat pid).map fun pg => (V.data +ₗ uint.Z (pid * V.ps), pg)

/-- The view's locations are in blocks, and its pages below `MaxMapSize`. -/
def BktView.ok (V : BktView) : Prop :=
  V.data.locCar ≠ 0 ∧ V.ip.locCar ≠ 0 ∧
  ∀ id pg, V.pages !! id = some pg → id * uint.nat V.ps < 281474976710655

/-- The subtree of page `pid` is well-formed (for an inline bucket: its leaf page). -/
def BktView.wfAt (V : BktView) (pid : w64) : Prop :=
  if V.root = W64 0 then pid = W64 0 ∧ pageFlags V.ipg = leafPageFlag ∧
    leafWF V.ipg V.ipg.length ∧ 16 ≤ V.ipg.length
  else treeWF V.pages V.hwm (uint.nat pid)

theorem uint_pid_ps' (V : BktView) (pid : w64) (pg : List w8) (hok : V.ok)
    (h : V.pages !! uint.nat pid = some pg) :
    uint.Z (pid * V.ps) = ((uint.nat pid * uint.nat V.ps : Nat) : Int) := by
  have hb := hok.2.2 _ _ h
  have hu : uint.Z (pid * V.ps) = (uint.Z pid * uint.Z V.ps) % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  rw [hu]
  have e1 : uint.Z pid = ((uint.nat pid : Nat) : Int) := by unfold uint.nat uint.Z; simp
  have e2 : uint.Z V.ps = ((uint.nat V.ps : Nat) : Int) := by unfold uint.nat uint.Z; simp
  rw [e1, e2, ← Int.natCast_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- `pg` is a well-formed leaf page (what `nsearch` and `keyValue` read). -/
def leafOK (pg : List w8) : Prop :=
  pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧ 16 ≤ pg.length

/-- A page of the view is in a block. -/
theorem pageAt_car (V : BktView) (pid : w64) (p : Loc) (pg : List w8) (hok : V.ok)
    (h : V.pageAt pid = some (p, pg)) : p.locCar ≠ 0 := by
  unfold BktView.pageAt at h
  split at h
  · split at h
    · cases h; exact hok.2.1
    · cases h
  · obtain ⟨pg', _, heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    simpa [Loc.add] using hok.1

/-- Page `pid` of a well-formed view: where it is, its bytes, and what `pageNode` needs. -/
theorem wfAt_page (V : BktView) (pid : w64) (hok : V.ok) (h : V.wfAt pid) :
    ∃ p pg, V.pageAt pid = some (p, pg) ∧ 16 ≤ pg.length ∧
      (V.root = W64 0 → pid = W64 0 ∧ p = V.ip) ∧
      (V.root ≠ W64 0 → p = V.data +ₗ uint.Z (pid * V.ps) ∧ W64 (pageId pg) = pid ∧
        uint.Z (pid * V.ps) < 281474976710655) ∧
      ((pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
       (pageFlags pg = branchPageFlag ∧ branchWF pg pg.length V.hwm ∧
         ∀ i < pageCount pg, V.wfAt (W64 (branchPgid pg i)))) := by
  unfold BktView.wfAt at h
  by_cases hr : V.root = W64 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h
    obtain ⟨hp0, hfl, hwf, hlen⟩ := h
    refine ⟨V.ip, V.ipg, ?_, hlen, fun _ => ⟨hp0, rfl⟩, fun h' => absurd hr h', Or.inl ⟨hfl, hwf⟩⟩
    unfold BktView.pageAt
    rw [ite_eq_left_of_eq_true _ _ (eq_true hr), ite_eq_left_of_eq_true _ _ (eq_true hp0)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h
    cases h with
    | page root pg hlt hlk hid hpt =>
    have Hu := uint_pid_ps' V pid pg hok hlk
    have Hb := hok.2.2 _ _ hlk
    refine ⟨_, pg, ?_, ?_, fun h' => absurd h' hr, fun _ => ⟨rfl, ?_, by omega⟩, ?_⟩
    · unfold BktView.pageAt
      rw [ite_eq_right_of_eq_false _ _ (eq_false hr), hlk]; rfl
    · cases hpt with
      | leaf _ _ _ hw _ => have := hw.2.1; unfold elemOff at this; omega
      | branch _ _ _ hw _ => have := hw.2.2.1; unfold elemOff at this; omega
    · rw [hid]; unfold uint.nat; word
    · cases hpt with
      | leaf _ _ hfl hw _ => exact Or.inl ⟨hfl, hw⟩
      | branch _ _ hfl hw hk =>
        refine Or.inr ⟨hfl, hw, fun i hi => ?_⟩
        unfold BktView.wfAt
        rw [ite_eq_right_of_eq_false _ _ (eq_false hr)]
        have hl : branchPgid pg i < 2 ^ 64 := leAt_lt _ _ 8
        have : uint.nat (W64 ((branchPgid pg i : Nat) : Int)) = branchPgid pg i := by
          unfold uint.nat; word
        rw [this]; exact hk i hi

/-- `leafSeekAt pg kb idx`: `idx` is the first element of the leaf `pg` whose key is not below
`kb` (`count` if none): what `nsearch` finds. -/
def leafSeekAt (pg kb : List w8) (idx : w64) : Prop :=
  0 ≤ sint.Z idx ∧ sint.Z idx ≤ pageCount pg ∧
  (∀ k, 0 ≤ k → k < sint.Z idx → leafGE pg kb k = false) ∧
  (sint.Z idx < pageCount pg → leafGE pg kb (sint.Z idx) = true)

section stacks
variable [ext : FfiSyntax]

/-- The stack invariant (see the module doc). -/
def stackOK (V : BktView) : w64 → List elemRef → Prop
  | _, [] => False
  | pid, r :: rs => r.node' = null ∧ ∃ pg, V.pageAt pid = some (r.page', pg) ∧
      ((pageFlags pg = branchPageFlag ∧ 0 ≤ sint.Z r.index' ∧ sint.Z r.index' < pageCount pg ∧
          stackOK V (W64 (branchPgid pg (sint.Z r.index').toNat)) rs) ∨
       (pageFlags pg = leafPageFlag ∧ rs = [] ∧ -1 ≤ sint.Z r.index' ∧
          sint.Z r.index' ≤ pageCount pg))

/-- The last element of a stack refers to the leaf page `pg` (with its index `idx`). -/
def stackLeaf (V : BktView) : w64 → List elemRef → List w8 → w64 → Prop
  | _, [], _, _ => False
  | pid, [r], pg, idx => V.pageAt pid = some (r.page', pg) ∧ r.index' = idx
  | pid, r :: rs, pg, idx => ∃ pg', V.pageAt pid = some (r.page', pg') ∧
      stackLeaf V (W64 (branchPgid pg' (sint.Z r.index').toNat)) rs pg idx

/-! The stack as the moves (`first`, `next`, ...) see it: a path of branch elements down to
the top element, which is a branch (while the move goes down) or a leaf. -/

/-- A leaf's index: at most past the end, and below 0 only on an empty leaf (`last`). -/
def leafIdx (pg : List w8) (idx : w64) : Prop :=
  sint.Z idx ≤ pageCount pg ∧ (0 ≤ sint.Z idx ∨ (sint.Z idx = -1 ∧ pageCount pg = 0))

/-- The element `r` refers to page `pid` (bytes `pg`), of a well-formed subtree: a branch with
one of its elements, or a leaf. -/
def topOK (V : BktView) (pid : w64) (r : elemRef) (pg : List w8) : Prop :=
  V.wfAt pid ∧ r.node' = null ∧ V.pageAt pid = some (r.page', pg) ∧
  ((pageFlags pg = branchPageFlag ∧ 0 ≤ sint.Z r.index' ∧ sint.Z r.index' < pageCount pg) ∨
   (pageFlags pg = leafPageFlag ∧ leafIdx pg r.index'))

/-- The child an element of a branch page refers to. -/
def childOf (pg : List w8) (r : elemRef) : w64 := W64 (branchPgid pg (sint.Z r.index').toNat)

/-- `es` are branch elements, from page `pid` down to page `pid'`. -/
def branchesTo (V : BktView) : w64 → List elemRef → w64 → Prop
  | pid, [], pid' => pid = pid'
  | pid, r :: rs, pid' => ∃ pg, topOK V pid r pg ∧ pageFlags pg = branchPageFlag ∧
      branchesTo V (childOf pg r) rs pid'

/-- The stack `es` goes from page `pid` down to its top `r` (page `pid'`, bytes `pg`). -/
def curPath (V : BktView) (pid : w64) (es : List elemRef) (pid' : w64) (r : elemRef)
    (pg : List w8) : Prop :=
  ∃ pre, es = pre ++ [r] ∧ branchesTo V pid pre pid' ∧ topOK V pid' r pg

/-- The stack goes from the bucket's root down to a leaf, its top `r` (bytes `pg`). -/
def leafTop (V : BktView) (es : List elemRef) (r : elemRef) (pg : List w8) : Prop :=
  ∃ pid', curPath V V.root es pid' r pg ∧ pageFlags pg = leafPageFlag

/-- A cursor's stack between moves: empty (never positioned) or down to a leaf. -/
def cursorOK (V : BktView) (es : List elemRef) : Prop :=
  es = [] ∨ ∃ r pg, leafTop V es r pg

/-- The value the public moves return: nil for a nested bucket (flag `BucketLeafFlag`). -/
def kvVal (v : GoSlice) (f : w32) : GoSlice := if f &&& W32 1 = W32 0 then v else slice.nil

/-- What a move returns: nil, or the key, value and flags of the stack's top element
(`kvResult`, slices into the leaf page; nil past the end). -/
def kvOK (V : BktView) (es : List elemRef) (k v : GoSlice) (f : w32) : Prop :=
  (k = slice.nil ∧ v = slice.nil ∧ f = W32 0) ∨
  ∃ r pg, leafTop V es r pg ∧ (k, v, f) = kvResult r.page' pg (sint.Z r.index')

theorem branchesTo_append (V : BktView) (a c : w64) (xs ys : List elemRef) :
    branchesTo V a (xs ++ ys) c ↔ ∃ b, branchesTo V a xs b ∧ branchesTo V b ys c := by
  induction xs generalizing a with
  | nil => simp [branchesTo]
  | cons x xs ih =>
    simp only [List.cons_append, branchesTo, ih]
    constructor
    · rintro ⟨pg, h1, h2, b, h3, h4⟩; exact ⟨b, ⟨pg, h1, h2, h3⟩, h4⟩
    · rintro ⟨b, ⟨pg, h1, h2, h3⟩, h4⟩; exact ⟨pg, h1, h2, b, h3, h4⟩

/-- A branch on top: its element's child can be pushed. -/
theorem branchesTo_snoc (V : BktView) (a b : w64) (xs : List elemRef) (r : elemRef)
    (pg : List w8) (h : branchesTo V a xs b) (ht : topOK V b r pg)
    (hb : pageFlags pg = branchPageFlag) :
    branchesTo V a (xs ++ [r]) (childOf pg r) :=
  (branchesTo_append V a _ xs [r]).2 ⟨b, h, pg, ht, hb, rfl⟩

/-- Element `i` of a stack: the path down to it, and its page. -/
theorem curPath_at (V : BktView) (a b : w64) (es : List elemRef) (r : elemRef) (pg : List w8)
    (h : curPath V a es b r pg) (i : Nat) (hi : i < es.length) :
    ∃ pidi pgi, branchesTo V a (es.take i) pidi ∧ topOK V pidi es[i] pgi ∧
      (i + 1 < es.length → pageFlags pgi = branchPageFlag ∧
        curPath V (childOf pgi es[i]) (es.drop (i + 1)) b r pg) := by
  obtain ⟨pre, rfl, hpre, htop⟩ := h
  by_cases hil : i < pre.length
  · have hsplit : pre = pre.take i ++ pre[i] :: pre.drop (i + 1) := by
      simp
    have h2 := hpre
    rw [hsplit, branchesTo_append] at h2
    obtain ⟨c, hc, pgi, ht, hb, hrest⟩ := h2
    refine ⟨c, pgi, ?_, ?_, fun _ => ⟨hb, ?_⟩⟩
    · rw [List.take_append_of_le_length (by omega)]; exact hc
    · rw [List.getElem_append_left hil]; exact ht
    · refine ⟨pre.drop (i + 1), ?_, ?_, htop⟩
      · rw [List.drop_append_of_le_length (by omega)]
      · rw [List.getElem_append_left hil]; exact hrest
  · have hi' : i = pre.length := by simp at hi; omega
    subst hi'
    refine ⟨b, pg, ?_, ?_, fun h => absurd h (by simp)⟩
    · rw [List.take_append_of_le_length (by omega), List.take_length]; exact hpre
    · rw [List.getElem_append_right (by omega)]; simpa using htop

theorem pageAt_unique {V : BktView} {pid : w64} {p p' : Loc} {pg pg' : List w8}
    (h : V.pageAt pid = some (p, pg)) (h' : V.pageAt pid = some (p', pg')) : p = p' ∧ pg = pg' := by
  rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩

/-- The children of a branch page of a well-formed view are well-formed. -/
theorem wfAt_child (V : BktView) (pid : w64) (p : Loc) (pg : List w8) (hok : V.ok)
    (hwf : V.wfAt pid) (hpa : V.pageAt pid = some (p, pg)) (hb : pageFlags pg = branchPageFlag) :
    branchWF pg pg.length V.hwm ∧ ∀ i < pageCount pg, V.wfAt (W64 (branchPgid pg i)) := by
  obtain ⟨p1, pg1, hpa1, -, -, -, hk⟩ := wfAt_page V pid hok hwf
  obtain ⟨-, rfl⟩ := pageAt_unique hpa hpa1
  rcases hk with ⟨hl, -⟩ | ⟨-, hw, hc⟩
  · rw [hb] at hl; exact absurd hl (by decide)
  · exact ⟨hw, hc⟩

/-- What `search` returns (a path down to a leaf, `stackOK`/`stackLeaf`) as a `curPath`. -/
theorem stackOK_curPath (V : BktView) (hok : V.ok) : ∀ (es : List elemRef) (pid : w64)
    (pg : List w8) (idx : w64), V.wfAt pid → stackOK V pid es → stackLeaf V pid es pg idx →
    0 ≤ sint.Z idx →
    ∃ pid' r, curPath V pid es pid' r pg ∧ pageFlags pg = leafPageFlag ∧ r.index' = idx
  | [], _, _, _, _, h, _, _ => h.elim
  | r :: rs, pid, pg, idx, hwf, ⟨hn, pg0, hpa, hk⟩, hl, h0 => by
    rcases hk with ⟨hb, hi0, hil, hrs⟩ | ⟨hfl, rfl, -, hle⟩
    · cases rs with
      | nil => exact hrs.elim
      | cons s ss =>
        obtain ⟨pg', hpa', hl'⟩ := hl
        obtain ⟨-, rfl⟩ := pageAt_unique hpa hpa'
        have hc := (wfAt_child V pid _ pg0 hok hwf hpa hb).2 (sint.Z r.index').toNat (by omega)
        obtain ⟨pid', r', ⟨pre, hes, hbr, htop⟩, hfl, hidx⟩ :=
          stackOK_curPath V hok (s :: ss) _ pg idx hc hrs hl' h0
        refine ⟨pid', r', ⟨r :: pre, by rw [hes]; rfl, ?_, htop⟩, hfl, hidx⟩
        exact ⟨pg0, ⟨hwf, hn, hpa, Or.inl ⟨hb, hi0, hil⟩⟩, hb, hbr⟩
    · obtain ⟨hpa', hidx⟩ := hl
      obtain ⟨-, rfl⟩ := pageAt_unique hpa hpa'
      refine ⟨pid, r, ⟨[], rfl, rfl, hwf, hn, hpa, Or.inr ⟨hfl, hle, Or.inl (hidx ▸ h0)⟩⟩, hfl, hidx⟩

theorem take_succ_set {α : Type} (es : List α) (n : Nat) (x : α) (h : n < es.length) :
    (es.take (n + 1)).set n x = es.take n ++ [x] := by
  induction es generalizing n with
  | nil => simp at h
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.set_cons_succ, List.cons_append]
      rw [ih n (by simp at h; omega)]

theorem take_succ_set_self {α : Type} (es : List α) (n : Nat) (h : n < es.length) :
    (es.take (n + 1)).set n es[n] = es.take (n + 1) := by
  rw [take_succ_set es n _ h, List.take_succ, List.getElem?_eq_getElem h]; rfl

theorem sint_pred (x : w64) (h : 0 < sint.Z x) :
    sint.Z (x - W64 1) = sint.Z x - 1 := by word

theorem w64_of_sint (x : w64) (n : Int) (h : sint.Z x = n) (h0 : 0 ≤ n) (h1 : n < 2 ^ 63) :
    x = W64 n := by word

theorem take_succ_getElem? {α : Type} (es : List α) (n : Nat) (h : n < es.length) :
    (es.take (n + 1))[n]? = some es[n] := by
  rw [List.getElem?_take]; simp [h]

theorem subslice_take_succ {α : Type} (es : List α) (n : Nat) :
    subslice 0 n (es.take (n + 1)) = es.take n := by
  unfold subslice; rw [List.drop_zero, List.take_take]; congr 1; omega

theorem subslice_set_succ {α : Type} (es : List α) (n : Nat) (x : α) (h : n < es.length) :
    subslice 0 (n + 1) (es.set n x) = es.take n ++ [x] := by
  unfold subslice
  rw [List.drop_zero]
  induction es generalizing n with
  | nil => simp at h
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      rw [ih n (by simp at h; omega)]

/-- A leaf on top of the stack: what reading it needs. -/
theorem leafTop_facts (V : BktView) (es : List elemRef) (r : elemRef) (pg : List w8)
    (hok : V.ok) (h : leafTop V es r pg) :
    ∃ pid pre, es = pre ++ [r] ∧ branchesTo V V.root pre pid ∧ V.wfAt pid ∧
      V.pageAt pid = some (r.page', pg) ∧ r.node' = null ∧
      16 ≤ pg.length ∧ pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧ leafIdx pg r.index' ∧
      r.page'.locCar ≠ 0 := by
  obtain ⟨pid, ⟨pre, hes, hbr, hwf, hn, hpa, hk⟩, hfl⟩ := h
  obtain ⟨p1, pg1, hpa1, hlen, -, -, hk1⟩ := wfAt_page V pid hok hwf
  obtain ⟨-, rfl⟩ := pageAt_unique hpa hpa1
  have hli : leafIdx pg r.index' := by
    rcases hk with ⟨hb, -⟩ | ⟨-, hl⟩
    · rw [hfl] at hb; exact absurd hb (by decide)
    · exact hl
  have hlw : leafWF pg pg.length := by
    rcases hk1 with ⟨-, hw⟩ | ⟨hb, -⟩
    · exact hw
    · rw [hfl] at hb; exact absurd hb (by decide)
  exact ⟨pid, pre, hes, hbr, hwf, hpa, hn, hlen, hfl, hlw, hli, pageAt_car V pid _ _ hok hpa⟩

theorem set_len_append {α : Type} (pre : List α) (r x : α) :
    (pre ++ [r]).set pre.length x = pre ++ [x] := by
  simp [List.set_append_right]

/-- The index of a slice's last element (`len(s) - 1`). -/
theorem top_index (s : GoSlice) (n : Nat) (h : n + 1 = sint.nat s.len ∧ 0 ≤ sint.Z s.len) :
    (sint.Z (s.len - W64 1)).toNat = n ∧
      (0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len) := by
  obtain ⟨h1, h2⟩ := h
  unfold sint.nat at h1
  refine ⟨?_, ?_, ?_⟩ <;> word

theorem w64_nat_ne_zero (n : Nat) (h : n < 65536) (h0 : n ≠ 0) : W64 (n : Int) ≠ W64 0 := by
  intro h'
  have := congrArg uint.Z h'
  have e : uint.Z (W64 (n : Int)) = n := by word
  rw [e] at this
  exact h0 (by have : uint.Z (W64 0) = 0 := rfl; omega)

theorem sub_one_sint (n : Nat) (h : n < 65536) : sint.Z (W64 (n : Int) - W64 1) = n - 1 := by
  word

theorem sint_succ (x : w64) (h : sint.Z x < 65535) (h' : -1 ≤ sint.Z x) :
    sint.Z (x + W64 1) = sint.Z x + 1 := by word

/-- A move that returns a nil key returns a nil value (`Seek` returns nil, nil then). -/
theorem kvOK_nil_key (V : BktView) (es : List elemRef) (k v : GoSlice) (f : w32) (hok : V.ok)
    (h : kvOK V es k v f) (hk : k = slice.nil) : kvVal v f = slice.nil := by
  rcases h with ⟨-, rfl, -⟩ | ⟨r, pg, hlt, he⟩
  · unfold kvVal; split <;> rfl
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hc⟩ := leafTop_facts V es r pg hok hlt
    unfold kvResult at he
    split at he
    · cases he; unfold kvVal; split <;> rfl
    · exfalso
      cases he
      have := congrArg GoSlice.ptr hk
      simp only [slice.nil] at this
      have h2 := congrArg Loc.locCar this
      simp [Loc.add, null] at h2
      exact hc h2

end stacks

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The bucket's pages, at the fraction `q`. -/
def bktPages (V : BktView) (q : Qp) : IProp GF :=
  if V.root = W64 0 then bytesPointsto V.ip (DFrac.own q) V.ipg
  else pagesView V.data (uint.nat V.ps) q V.pages

/-- What the read path reads of the bucket at `bl` besides its pages (see the module doc). -/
def bktCtx (bl : Loc) (V : BktView) : IProp GF :=
  iprop(∃ (bv : Bucket) (ib : internal.common.InBucket) (t : Tx) (dbl : Loc)
      (d1 d2 d3 d4 : DFrac),
    bl ↦{d1} bv ∗ bv.InBucket' ↦{d2} ib ∗ bv.tx' ↦{d3} t ∗
    structFieldRef DB go!"data" dbl ↦{d4} V.data ∗ structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗
    ⌜ib.root' = V.root ∧ bv.nodes' = map.nil ∧ bv.rootNode' = null ∧ t.db' = dbl ∧
      t.pages' = map.nil ∧ (V.root = W64 0 → bv.page' = V.ip) ∧ dbl ≠ null⌝)

/-- A cursor at `cl` on the bucket at `bl`, with the stack `es`: what its methods own. -/
def curI (cl bl : Loc) (V : BktView) (q : Qp) (es : List elemRef) : IProp GF :=
  iprop(∃ (cv : Cursor), ⌜cv.bucket' = bl⌝ ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
    ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ bktCtx bl V ∗ bktPages V q)

theorem uint_pid_ps (V : BktView) (pid : w64) (pg : List w8) (hok : V.ok)
    (h : V.pages !! uint.nat pid = some pg) :
    uint.Z (pid * V.ps) = ((uint.nat pid * uint.nat V.ps : Nat) : Int) :=
  uint_pid_ps' V pid pg hok h

/-- A page of the view, taken out of the bucket's pages (and given back). -/
theorem bktPages_acc (V : BktView) (q : Qp) (pid : w64) (p : Loc) (pg : List w8)
    (hok : V.ok) (h : V.pageAt pid = some (p, pg)) :
    bktPages (GF := GF) V q ⊢ bytesPointsto p (DFrac.own q) pg ∗
      (bytesPointsto p (DFrac.own q) pg -∗ bktPages V q) := by
  unfold BktView.pageAt at h
  unfold bktPages
  by_cases hr : V.root = W64 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h ⊢
    by_cases hp : pid = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h
      cases h
      iintro H; iframe H; iintro H; iexact H
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h; cases h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h ⊢
    obtain ⟨pg', hpg', heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    unfold pagesView
    have Hu := uint_pid_ps V pid pg hok hpg'
    rw [Hu]
    exact (BigSepM.bigSepM_lookup_acc hpg').1

end preds

end bbolt
end EtcdGrove
end Perennial
