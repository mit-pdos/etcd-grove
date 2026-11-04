/-
Cursor stacks relative to a view and a transaction's data (U0a of `notes/bbolt-proof-plan.md`;
design §3.10, §3.13 "Cursor stacks (B5)").

A cursor's stack (`[]elemRef`: a page or a node, and an index) is a root-to-leaf path in a
bucket's tree. Its **shape** is read in the base view: a branch's children are its page's (a
materialized branch node has its page's entries before `Commit`, `nodePg`), so a path is a list
of page ids (`pids`), each element a page reference of the view or a node reference whose page id
the node-location registry `nl` records. Its **position** over the bucket's entries `es` (sorted:
`bktEnts`) is the number of entries below the leaf's lower bound (the base branch keys' bounds
along the path) plus the leaf index: a leaf's entries are those of `es` within its bounds (for a
reader by `treeKeys`; for a writer by R6, `ltree_leaf_of_T`). An empty leaf has the position of
the next one, which is why `next`'s skipping of empty leaves keeps it.

`rStackAt` (readers: page references only, `es` the view's) and `wStackAt` (writers: `es` from
`T.cur`, node references through the registry) are the two instances (B5).
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section cursor
variable [GooseExts]

/-- The location of page `pid` of the view. -/
def pageLoc (v : View) (pid : Nat) : Loc := v.base +ₗ ((pid * 4096 : Nat) : Int)

/-- The value of the top-level bucket `n` in the view (its root bucket's entry). -/
def baseVal (v : View) (n : GoString) : Option (List w8) :=
  ((treeEntries v.pages v.root).find? fun e => decide (e.1 = n)).map Prod.snd

/-- The root page of bucket `n` in the base view (`0`: inline, or not in the view: created by
the transaction). -/
def baseRoot (v : View) (n : GoString) : Nat := ((baseVal v n).map inBucketRoot).getD 0

/-- The keys of page `pid` of the view. -/
def pidKeys (v : View) (pid : Nat) : List (List w8) :=
  match v.pages !! pid with
  | some pg => (List.range (pageCount pg)).map (pageKey pg)
  | none => []

/-- **The shape of a stack**: `pids` (one per element) is a root-to-leaf path of bucket `n`'s
base tree, and each element refers to its page (a page of the view; for the inline root, a
location in the view) or to a node of bucket `b` read from it (registry `nl`). -/
def sPath (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (n : GoString)
    (els : List elemRef) (pids : List Nat) : Prop :=
  els ≠ [] ∧ pids.length = els.length ∧ pids.head? = some (baseRoot v n) ∧
  ∀ j e pid, els[j]? = some e → pids[j]? = some pid →
    (e.node' ≠ null → nl e.node' = some (b, pid)) ∧
    (e.node' = null → e.page' ≠ null ∧ (pid ≠ 0 → e.page' = pageLoc v pid)) ∧
    (j + 1 < els.length → ∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = branchPageFlag ∧
      e.index'.toNat < pageCount pg ∧ pids[j + 1]? = some (branchPgid pg e.index'.toNat)) ∧
    (j + 1 = els.length → pid = 0 ∨ ∃ pg, v.pages !! pid = some pg ∧
      pageFlags pg = leafPageFlag)

/-- The bounds below a path from the bounds `b`: `entryBnd` along its branches' keys. -/
def pathBndFrom (v : View) (b : Option (List w8) × Option (List w8)) :
    List Nat → List elemRef → Option (List w8) × Option (List w8)
  | pid :: pid' :: ps, e :: es =>
    pathBndFrom v (entryBnd b (pidKeys v pid) e.index'.toNat) (pid' :: ps) es
  | _, _ => b

/-- The bounds of the leaf a path reaches. -/
def pathBnd (v : View) (pids : List Nat) (els : List elemRef) :
    Option (List w8) × Option (List w8) :=
  pathBndFrom v (none, none) pids els

/-- The leaf index of a stack (its last element's). -/
def leafIdx (els : List elemRef) : Nat := ((els.getLast?).map fun e => e.index'.toNat).getD 0

open Classical in
/-- The entries of `es` within the bounds `bnd` (a leaf's entries). -/
def entsIn (es : List BoltEnt) (bnd : Option (List w8) × Option (List w8)) : List BoltEnt :=
  es.filter fun e => decide (keyIn bnd.1 bnd.2 e.1)

open Classical in
/-- The position a path denotes over `es`: the entries below the leaf's lower bound, plus the
leaf index. -/
def stackPos (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Nat :=
  (es.filter fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1)).length + leafIdx els

/-- **A stack at a position**: unpositioned (any stack), or a path whose position is `i` (at
most `es.length`: past the last, `Next` stays at `es.length`). -/
def stackAt (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (n : GoString) (els : List elemRef) : Option Nat → Prop
  | none => True
  | some i => ∃ pids, sPath nl v b n els pids ∧ i = min (stackPos v es pids els) es.length

/-- **A reader's stack** in bucket `n` of its view `v` (page references only). -/
def rStackAt (v : View) (n : GoString) (els : List elemRef) (pos : Option Nat) : Prop :=
  stackAt (fun _ => none) v (bktEnts ((v.data !! n).getD ∅)) null n els pos ∧
    ∀ e ∈ els, e.node' = null

/-- **A writer's stack** in bucket `n` (handle `b`) at the view `T`, over the base view `v` and
the node-location registry `nl` (B5, N3). -/
def wStackAt (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc) (n : GoString)
    (els : List elemRef) (pos : Option Nat) : Prop :=
  stackAt nl v (bktEnts ((T.cur !! n).getD ∅)) b n els pos

/-! ## Moves -/

/-- At each branch the index a search for `k` descends to (the last whose key is at most `k`,
or the first: `routes` of `WriteTxShape`), and at the leaf the first entry not below `k`. -/
def sRoutes (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (k : List w8) : Prop :=
  (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
    let ks := pidKeys v pid
    e.index'.toNat < ks.length ∧
    (e.index'.toNat = 0 ∨ ∃ ki, ks[e.index'.toNat]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
    ∀ kn, ks[e.index'.toNat + 1]? = some kn → go.GoStringLt k kn) ∧
  leafIdx els = ((entsIn es (pathBnd v pids els)).takeWhile
    fun e => decide (go.GoStringLt e.1 k)).length

/-- Every index of the stack is the first. -/
def sFirst (els : List elemRef) : Prop := ∀ e ∈ els, e.index'.toNat = 0

/-- Every branch index of the stack is the last, and so is the leaf's (over `es`). -/
def sLast (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Prop :=
  (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
    e.index'.toNat + 1 = (pidKeys v pid).length) ∧
  leafIdx els + 1 = (entsIn es (pathBnd v pids els)).length

/-- **`next`'s move at depth `d`** (`Cursor.next`: `c.stack = c.stack[:d+1]`, `elem.index++` at
`d`, then `goToFirstElementOnTheStack`): `els'` keeps `els` above `d`, is one further at `d`, and
first below. -/
def sSucc (d : Nat) (els els' : List elemRef) : Prop :=
  ∃ e e' R', els[d]? = some e ∧ els' = els.take d ++ e' :: R' ∧
    e'.index'.toNat = e.index'.toNat + 1 ∧ ∀ x ∈ R', x.index'.toNat = 0

/-- **The old stack is at the end below `d`** (what `next`'s upward loop found: no level below
`d` could move): its branch indices below `d` are the last, its leaf index at most its leaf's
entries (`next` moves up from a leaf index `≥ count - 1`: at the last entry, past it after a
`Seek`, or an empty leaf), and its leaf's bounds are ordered. -/
def sEndBelow (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (d : Nat) :
    Prop :=
  (∀ j pid e, pids[j]? = some pid → els[j]? = some e → d < j → j + 1 < els.length →
    e.index'.toNat + 1 = (pidKeys v pid).length) ∧
  leafIdx els ≤ (entsIn es (pathBnd v pids els)).length ∧
  ∀ L H, pathBnd v pids els = (some L, some H) → ¬ go.GoStringLt H L

/-- `els'` is the in-order predecessor of `els`: equal above some depth `d`, one before at `d`,
last below (over the base pages and, at the leaf, `es`). -/
def sPred (v : View) (es : List BoltEnt) (pids' : List Nat) (els els' : List elemRef) : Prop :=
  ∃ d, d < els.length ∧ d < els'.length ∧
    (els'.take d).map (·.index') = (els.take d).map (·.index') ∧
    (∃ e e', els[d]? = some e ∧ els'[d]? = some e' ∧ e'.index'.toNat + 1 = e.index'.toNat) ∧
    ∀ j, d < j → j < els'.length → sLast v es (pids'.drop j) (els'.drop j)

/-! ## Positions (private helpers of the lemmas below) -/

/-- Entries strictly increasing by key. -/
private def esSorted (es : List BoltEnt) : Prop := es.Pairwise (fun a b => go.GoStringLt a.1 b.1)

private theorem bktEnts_sorted' (m : BktData) : esSorted (bktEnts m) := by
  unfold bktEnts esSorted
  have hn : ((m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).map
      Prod.fst).Nodup :=
    (((List.mergeSort_perm m.toList _).map Prod.fst).nodup_iff).2 (GMap.toList_keys_nodup m)
  have hle : (m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).Pairwise
      (fun a b => (!decide (go.GoStringLt b.1 a.1)) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at *
      intro h3
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · exact h1 h
      · rcases Classical.em (go.GoStringLt c.1 b.1) with h' | h'
        · exact h2 h'
        · have e1 := Classical.byContradiction fun hne : ¬ (a.1 = b.1 ∨ go.GoStringLt a.1 b.1) => by
            exact hne (by
              rcases Classical.em (go.GoStringLt a.1 b.1) with h4 | h4
              · exact Or.inr h4
              · exact Or.inl (go.goStringLt_eq_of_not_lt h4 h))
          rcases e1 with e1 | e1
          · rw [e1] at h3; exact h2 h3
          · exact h2 (go.goStringLt_trans h3 e1)
    · intro a b
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true]
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · right; exact go.goStringLt_asymm h
      · left; exact h
  rw [List.Nodup, List.pairwise_map] at hn
  refine (hle.and hn).imp (fun ⟨h1, h2⟩ => ?_)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
  rcases Classical.em (go.GoStringLt _ _) with h | h
  · exact h
  · exact absurd (go.goStringLt_eq_of_not_lt h h1) h2


private theorem len_filter_sum (es : List BoltEnt) (f g h : BoltEnt → Bool)
    (hpt : ∀ e ∈ es, (if f e then 1 else 0) + (if g e then 1 else 0) = (if h e then 1 else 0)) :
    (es.filter f).length + (es.filter g).length = (es.filter h).length := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    have ha := hpt a (List.mem_cons_self ..)
    have ht := ih (fun e he => hpt e (List.mem_cons_of_mem _ he))
    simp only [List.filter_cons]
    split <;> split <;> split <;> simp_all <;> omega

private theorem takeWhile_lt_sorted (es : List BoltEnt) (k : List w8) (hs : esSorted es) :
    es.takeWhile (fun e => decide (go.GoStringLt e.1 k)) =
      es.filter (fun e => decide (go.GoStringLt e.1 k)) := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    unfold esSorted at hs
    rw [List.pairwise_cons] at hs
    simp only [List.takeWhile_cons, List.filter_cons]
    by_cases ha : go.GoStringLt a.1 k
    · simp only [ha, decide_true, ↓reduceIte, ih hs.2]
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_nil_iff]
      intro x hx hxk
      simp only [decide_eq_true_eq] at hxk
      exact ha (go.goStringLt_trans (hs.1 x hx) hxk)

private theorem keyGe_lt {lo : Option (List w8)} {e k : List w8} (hk : keyGe lo k)
    (he : ¬ keyGe lo e) : go.GoStringLt e k := by
  cases lo with
  | none => exact absurd (fun _ h => nomatch h) he
  | some l =>
  have hel : go.GoStringLt e l := Classical.byContradiction fun h => he (fun l' hl => by
    cases hl; exact h)
  have := hk l rfl
  rcases Classical.em (go.GoStringLt l k) with h | h
  · exact go.goStringLt_trans hel h
  · rw [go.goStringLt_eq_of_not_lt this h]; exact hel

private theorem keyLt_lt {hi : Option (List w8)} {e k : List w8} (hk : keyLt k hi)
    (he : go.GoStringLt e k) : keyLt e hi :=
  fun h hh => go.goStringLt_trans he (hk h hh)

open Classical in
/-- The position of a search's leaf index under the bounds `bnd` routing `k`. -/
private theorem seek_count (es : List BoltEnt) (k : List w8) (bnd : Option (List w8) × Option (List w8))
    (hs : esSorted es) (hk : keyIn bnd.1 bnd.2 k) :
    (es.filter fun e => decide (¬ keyGe bnd.1 e.1)).length +
      ((entsIn es bnd).takeWhile fun e => decide (go.GoStringLt e.1 k)).length =
      seekIdx es k := by
  unfold seekIdx entsIn
  rw [takeWhile_lt_sorted es k hs, takeWhile_lt_sorted _ k (List.Pairwise.filter _ hs)]
  rw [List.filter_filter]
  apply len_filter_sum
  intro e _
  by_cases hg : keyGe bnd.1 e.1
  · by_cases hl : go.GoStringLt e.1 k
    · have := keyLt_lt hk.2 hl
      simp [hg, hl, keyIn, this]
    · simp [hg, hl]
  · have hl := keyGe_lt hk.1 hg
    simp [hg, hl, keyIn]

/-- A routed path's leaf bounds contain `k`. -/
private theorem pathBndFrom_route (v : View) (k : List w8) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length → keyIn b.1 b.2 k →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      let ks := pidKeys v pid
      e.index'.toNat < ks.length ∧
      (e.index'.toNat = 0 ∨ ∃ ki, ks[e.index'.toNat]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
      ∀ kn, ks[e.index'.toNat + 1]? = some kn → go.GoStringLt k kn) →
    keyIn (pathBndFrom v b pids els).1 (pathBndFrom v b pids els).2 k
  | [], _, b, _, hb, _ => by cases ‹List Nat› <;> simpa [pathBndFrom] using hb
  | [_], pids, b, hl, hb, _ => by
    match pids, hl with
    | [_], _ => simpa [pathBndFrom] using hb
  | e :: e' :: es, pids, b, hl, hb, hr => by
    match pids, hl with
    | pid :: pid' :: ps, hl =>
      simp only [pathBndFrom]
      apply pathBndFrom_route v k (e' :: es) (pid' :: ps)
      · simpa using hl
      · obtain ⟨_, h0, h1⟩ := hr 0 pid e rfl rfl (by simp)
        refine ⟨?_, ?_⟩
        · simp only [entryBnd, childLo]
          split
          · exact hb.1
          · rcases h0 with h0 | ⟨ki, hki, hnk⟩
            · contradiction
            · intro l hlk
              simp only [Option.some.injEq] at hlk
              subst hlk
              rw [List.getD_eq_getElem?_getD, hki]; exact hnk
        · simp only [entryBnd, childHi]
          split
          · intro h hh
            simp only [Option.some.injEq] at hh
            subst hh
            rw [List.getD_eq_getElem?_getD]
            obtain ⟨kn, hkn⟩ : ∃ kn, (pidKeys v pid)[e.index'.toNat + 1]? = some kn :=
              Option.isSome_iff_exists.mp (by simp [*])
            rw [hkn]; exact h1 kn hkn
          · exact hb.2
      · intro j p x hp hx hj
        exact hr (j + 1) p x (by simpa using hp) (by simpa using hx) (by simp at hj ⊢; omega)

private theorem pathBndFrom_first (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    (∀ e ∈ els, e.index'.toNat = 0) → (pathBndFrom v b pids els).1 = b.1
  | e :: e' :: es, pid :: pid' :: ps, b, hf => by
    simp only [pathBndFrom]
    rw [pathBndFrom_first v (e' :: es) (pid' :: ps) _ (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    simp [entryBnd, childLo, hf e (List.mem_cons_self ..)]
  | [], _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _ => by simp [pathBndFrom]
  | [_], [_], _, _ => by simp [pathBndFrom]
  | [e], _ :: _ :: _, _, hf => by simp [pathBndFrom, entryBnd, childLo, hf e (by simp)]
  | _ :: _ :: _, [], _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _ => by simp [pathBndFrom]

private theorem pathBndFrom_last (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      e.index'.toNat + 1 = (pidKeys v pid).length) → (pathBndFrom v b pids els).2 = b.2
  | e :: e' :: es, pid :: pid' :: ps, b, hl, hr => by
    simp only [pathBndFrom]
    rw [pathBndFrom_last v (e' :: es) (pid' :: ps) _ (by simpa using hl)
      (fun j p x hp hx hj => hr (j + 1) p x (by simpa using hp) (by simpa using hx)
        (by simp at hj ⊢; omega))]
    have := hr 0 pid e rfl rfl (by simp)
    simp [entryBnd, childHi, this]
  | [], _, _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _, _ => by simp [pathBndFrom]
  | [_], [_], _, _, _ => by simp [pathBndFrom]
  | [_], _ :: _ :: _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [], _, _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _, _ => by simp [pathBndFrom]

private theorem stackPos_seek (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (k : List w8) (hs : esSorted es) (hl : pids.length = els.length)
    (hr : sRoutes v es pids els k) : stackPos v es pids els = seekIdx es k := by
  unfold stackPos
  rw [hr.2]
  exact seek_count es k _ hs (pathBndFrom_route v k els pids (none, none) hl
    (show keyIn (none : Option (List w8)) none k by
      unfold keyIn keyGe keyLt; simp)
    hr.1)

private theorem seekIdx_le (es : List BoltEnt) (k : List w8) : seekIdx es k ≤ es.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix _)

private theorem stackPos_first (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (hf : sFirst els) : stackPos v es pids els = 0 := by
  unfold stackPos pathBnd
  rw [pathBndFrom_first v els pids _ hf]
  have : leafIdx els = 0 := by
    unfold leafIdx
    cases h : els.getLast? with
    | none => rfl
    | some e => simp [hf e (List.mem_of_getLast? h)]
  rw [this]
  simp [keyGe]

open Classical in
private theorem stackPos_last (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (hl : pids.length = els.length) (hla : sLast v es pids els) :
    stackPos v es pids els = es.length - 1 := by
  unfold stackPos
  have h2 : (pathBnd v pids els).2 = none := pathBndFrom_last v els pids _ hl hla.1
  have hsum := len_filter_sum es (fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1))
    (fun e => decide (keyIn (pathBnd v pids els).1 (pathBnd v pids els).2 e.1)) (fun _ => true)
    (by intro e _; by_cases h : keyGe (pathBnd v pids els).1 e.1 <;> simp [h, keyIn, keyLt, h2])
  have htrue : (es.filter fun _ => true) = es := List.filter_eq_self.2 (fun _ _ => rfl)
  rw [htrue] at hsum
  have hb := hla.2
  unfold entsIn at hb
  omega

private theorem pathBndFrom_cons (v : View) (b : Option (List w8) × Option (List w8)) (p : Nat)
    (xs : List Nat) (e : elemRef) (es : List elemRef) (hx : xs ≠ []) :
    pathBndFrom v b (p :: xs) (e :: es) =
      pathBndFrom v (entryBnd b (pidKeys v p) e.index'.toNat) xs es := by
  cases xs with
  | nil => exact absurd rfl hx
  | cons x xs => simp [pathBndFrom]

/-- The bounds of a path, split after a prefix: the prefix's bounds, then the rest's. -/
private theorem pathBndFrom_append (v : View) :
    ∀ (E : List elemRef) (P : List Nat) (b : Option (List w8) × Option (List w8))
      (x0 : Nat) (X : List Nat) (Y : List elemRef), P.length = E.length →
    pathBndFrom v b (P ++ x0 :: X) (E ++ Y) =
      pathBndFrom v (pathBndFrom v b (P ++ [x0]) E) (x0 :: X) Y
  | [], [], b, x0, X, Y, _ => by simp [pathBndFrom]
  | e :: E, p :: P, b, x0, X, Y, hl => by
    simp only [List.cons_append]
    rw [pathBndFrom_cons v b p _ e _ (by simp), pathBndFrom_cons v b p _ e _ (by simp)]
    exact pathBndFrom_append v E P _ x0 X Y (by simpa using hl)
  | [], _ :: _, _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, _, hl => by simp at hl

private theorem leafIdx_append (E R : List elemRef) (hR : R ≠ []) : leafIdx (E ++ R) = leafIdx R := by
  unfold leafIdx; rw [List.getLast?_append]
  cases h : R.getLast? with
  | none => simp at h; exact absurd h hR
  | some x => simp

open Classical in
/-- **`next`'s position, one level up** (`d` above the leaf): the old stack is at the end of
every level below `d` (branch indices the last, its leaf index at or past the leaf's last
entry), the new one one further at `d` and first below. The new position is the old one plus
what was left of the old leaf (one, or none past its end). -/
private theorem stackPos_succ_up (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (Q Q' : List Nat) (e e' : elemRef) (R R' : List elemRef)
    (hPE : P.length = E.length) (hQR : Q.length = R.length) (hQR' : Q'.length = R'.length)
    (hR : R ≠ []) (hR' : R' ≠ [])
    (hidx : e'.index'.toNat = e.index'.toNat + 1)
    (hlt : e'.index'.toNat < (pidKeys v p).length)
    (hlast : ∀ j pid x, Q[j]? = some pid → R[j]? = some x → j + 1 < R.length →
      x.index'.toNat + 1 = (pidKeys v pid).length)
    (hfirst : ∀ x ∈ R', x.index'.toNat = 0)
    (hbnd : ∀ L H, pathBnd v (P ++ p :: Q) (E ++ e :: R) = (some L, some H) →
      ¬ go.GoStringLt H L)
    (hle : leafIdx R ≤ (entsIn es (pathBnd v (P ++ p :: Q) (E ++ e :: R))).length) :
    stackPos v es (P ++ p :: Q') (E ++ e' :: R') + leafIdx R =
      stackPos v es (P ++ p :: Q) (E ++ e :: R) +
        (entsIn es (pathBnd v (P ++ p :: Q) (E ++ e :: R))).length := by
  obtain ⟨q0, Q0, rfl⟩ : ∃ q0 Q0, Q = q0 :: Q0 := by
    cases Q with
    | nil => cases R with | nil => exact absurd rfl hR | cons _ _ => simp at hQR
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  obtain ⟨q0', Q0', rfl⟩ : ∃ q0 Q0, Q' = q0 :: Q0 := by
    cases Q' with
    | nil => cases R' with | nil => exact absurd rfl hR' | cons _ _ => simp at hQR'
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  have hold : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R) =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p) e.index'.toNat) (q0 :: Q0) R := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e _ (by simp)]
  have hnew : pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R') =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p) e'.index'.toNat) (q0' :: Q0') R' := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e' _ (by simp)]
  have hhi : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R)).2 = some ((pidKeys v p).getD (e.index'.toNat + 1) []) := by
    rw [hold, pathBndFrom_last v R (q0 :: Q0) _ hQR hlast]
    simp only [entryBnd, childHi]
    rw [if_pos (show _ by omega)]
  have hlo : (pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R')).1 = some ((pidKeys v p).getD (e.index'.toNat + 1) []) := by
    rw [hnew, pathBndFrom_first v R' (q0' :: Q0') _ hfirst]
    simp only [entryBnd, childLo, hidx]
    simp
  have hli' : leafIdx (E ++ e' :: R') = 0 := by
    rw [show E ++ e' :: R' = (E ++ [e']) ++ R' by simp, leafIdx_append _ _ hR']
    unfold leafIdx
    cases h : R'.getLast? with
    | none => rfl
    | some x => simp [hfirst x (List.mem_of_getLast? h)]
  have hli : leafIdx (E ++ e :: R) = leafIdx R := by
    rw [show E ++ e :: R = (E ++ [e]) ++ R by simp, leafIdx_append _ _ hR]
  unfold stackPos
  rw [hli', hli, hlo]
  generalize hK : ((pidKeys v p).getD (e.index'.toNat + 1) []) = K at hhi hlo
  generalize hlo' : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R)).1 = lo
  have hb : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R) = (lo, some K) := by
    rw [← hhi, ← hlo']
  have hlK : keyGe lo K := by
    intro L hL; exact hbnd L K (by rw [hb, hL])
  have hcount := len_filter_sum es (fun x => decide (¬ keyGe lo x.1))
    (fun x => decide (keyIn lo (some K) x.1)) (fun x => decide (¬ keyGe (some K) x.1))
    (by
      intro x _
      by_cases hg : keyGe lo x.1
      · by_cases hk : go.GoStringLt x.1 K
        · have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
          simp [hg, keyIn, keyLt, hk, this]
        · have : keyGe (some K) x.1 := by intro l hl; cases hl; exact hk
          simp [hg, keyIn, keyLt, hk, this]
      · have hk := keyGe_lt hlK hg
        have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
        simp [hg, keyIn, this])
  unfold entsIn at hle ⊢
  rw [hb] at hle ⊢
  simp only at hle ⊢
  omega

/-- **`next`'s position at the leaf**: the leaf index one further. -/
private theorem stackPos_succ_leaf (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (e e' : elemRef) (hPE : P.length = E.length)
    (hidx : e'.index'.toNat = e.index'.toNat + 1) :
    stackPos v es (P ++ [p]) (E ++ [e']) = stackPos v es (P ++ [p]) (E ++ [e]) + 1 := by
  have h : ∀ x, pathBnd v (P ++ [p]) (E ++ [x]) = pathBndFrom v (none, none) (P ++ [p]) E := by
    intro x; unfold pathBnd
    rw [pathBndFrom_append v E P _ p [] [x] hPE]; simp [pathBndFrom]
  unfold stackPos
  rw [h, h, leafIdx_append _ _ (by simp), leafIdx_append _ _ (by simp)]
  simp [leafIdx, hidx]; omega

private theorem split_at {α : Type} (l : List α) (d : Nat) (h : d < l.length) :
    ∃ P x Q, l = P ++ x :: Q ∧ P.length = d ∧ l[d]? = some x := by
  refine ⟨l.take d, l[d], l.drop (d + 1), ?_, by simp; omega, by simp [h]⟩
  rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

private theorem pidKeys_length (v : View) (pid : Nat) (pg : List w8)
    (h : v.pages !! pid = some pg) : (pidKeys v pid).length = pageCount pg := by
  simp [pidKeys, h]

/-- **`next`'s positions** (U6 fix): at the leaf (`d` its depth) one further; one level up or
more, the old position plus what was left of the old leaf (one at its last entry, none past its
end or in an empty leaf). -/
theorem stackPos_next (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (n : GoString) (els els' : List elemRef) (pids pids' : List Nat) (d : Nat)
    (hp : sPath nl v b n els pids) (hp' : sPath nl v b n els' pids') (hs : sSucc d els els')
    (hlen : d + 1 < els.length ↔ d + 1 < els'.length)
    (hend : d + 1 < els.length → sEndBelow v es pids els d) :
    (d + 1 = els.length → stackPos v es pids' els' = stackPos v es pids els + 1) ∧
    (d + 1 < els.length → stackPos v es pids' els' + leafIdx els =
      stackPos v es pids els + (entsIn es (pathBnd v pids els)).length) := by
  obtain ⟨e, e', R', he, rfl, hidx, hfirst⟩ := hs
  have hd : d < els.length := by
    rcases Nat.lt_or_ge d els.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at he
  obtain ⟨E, e0, R, rfl, hE, he0⟩ := split_at els d hd
  rw [he] at he0; cases he0
  have htk : (E ++ e :: R).take d = E := by
    rw [← hE]; simp
  rw [htk] at hp' hlen ⊢
  have hpl := hp.2.1
  have hpl' := hp'.2.1
  simp only [List.length_append, List.length_cons] at hpl hpl' hlen
  obtain ⟨P, p, Q, rfl, hP, -⟩ := split_at pids d (by omega)
  obtain ⟨P', p', Q', rfl, hP', -⟩ := split_at pids' d (by omega)
  simp only [List.length_append, List.length_cons] at hpl hpl'
  -- the paths agree up to `d`
  have hpre : ∀ j, j ≤ d → (P' ++ p' :: Q')[j]? = (P ++ p :: Q)[j]? := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := hp.2.2.1
      have h2 := hp'.2.2.1
      rw [List.head?_eq_getElem?] at h1 h2
      rw [h1, h2]
    | succ j ih =>
      intro hj
      have hjE : j < E.length := by omega
      obtain ⟨pid, hpid⟩ : ∃ pid, (P ++ p :: Q)[j]? = some pid :=
        Option.isSome_iff_exists.mp (by simp; omega)
      have hx : (E ++ e :: R)[j]? = some E[j] := by
        rw [List.getElem?_append_left hjE]; simp
      have hx' : (E ++ e' :: R')[j]? = some E[j] := by
        rw [List.getElem?_append_left hjE]; simp
      obtain ⟨pg, hpg, -, -, hnx⟩ :=
        (hp.2.2.2 j _ pid hx hpid).2.2.1 (by simp; omega)
      obtain ⟨pg', hpg', -, -, hnx'⟩ :=
        (hp'.2.2.2 j _ pid hx' (by rw [ih (by omega)]; exact hpid)).2.2.1 (by simp; omega)
      rw [hpg] at hpg'; cases hpg'
      rw [hnx, hnx']
  have hPP : P = P' := by
    apply List.ext_getElem?
    intro j
    rcases Nat.lt_or_ge j d with h | h
    · have := hpre j (by omega)
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at this
      exact this.symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hPP
  have hpp : p = p' := by
    have := hpre d (Nat.le_refl _)
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)] at this
    simpa [hP, hP'] using this.symm
  subst hpp
  have hPE : P.length = E.length := by omega
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · -- at the leaf: `R`, `R'`, `Q`, `Q'` are empty
    have hR : R = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    have hR' : R' = [] := List.eq_nil_of_length_eq_zero (by
      have : ¬ d + 1 < E.length + (R'.length + 1) := fun h => by
        have := hlen.2 h; simp at hl; omega
      omega)
    subst hR hR'
    have hQ : Q = [] := List.eq_nil_of_length_eq_zero (by simp at hpl; omega)
    have hQ' : Q' = [] := List.eq_nil_of_length_eq_zero (by simp at hpl'; omega)
    subst hQ hQ'
    exact stackPos_succ_leaf v es P E p e e' hPE hidx
  · obtain ⟨hlast, hle, hbnd⟩ := hend hl
    have hl' := hlen.1 (by simpa using hl)
    have hRne : R ≠ [] := fun h => by subst h; simp at hl; omega
    have hRne' : R' ≠ [] := fun h => by subst h; simp at hl'; omega
    obtain ⟨pg, hpg, -, hlt, -⟩ :=
      (hp'.2.2.2 d e' p (by rw [List.getElem?_append_right (by omega)]; simp [hE])
        (by rw [List.getElem?_append_right (by omega)]; simp [hP])).2.2.1 (by simp; omega)
    have hli : leafIdx (E ++ e :: R) = leafIdx R := by
      rw [show E ++ e :: R = (E ++ [e]) ++ R by simp, leafIdx_append _ _ hRne]
    rw [hli]
    refine stackPos_succ_up v es P E p Q Q' e e' R R' hPE (by omega)
      (by omega) hRne hRne' hidx
      (by rw [pidKeys_length v p pg hpg]; exact hlt) ?_ hfirst hbnd
      (by rw [hli] at hle; exact hle)
    intro j pid x hq hr hj
    refine hlast (d + 1 + j) pid x ?_ ?_ (by omega) (by simp; omega)
    · rw [List.getElem?_append_right (by omega)]
      simpa [hP, show d + 1 + j - d = j + 1 by omega] using hq
    · rw [List.getElem?_append_right (by omega)]
      simpa [hE, show d + 1 + j - d = j + 1 by omega] using hr

/-! ## Lemma statements (U6) -/

/-- `Seek`'s descent reaches `seekIdx` (readers). -/
theorem rStackAt_seek (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (k : List w8) (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null)
    (hr : sRoutes v (bktEnts ((v.data !! n).getD ∅)) pids els k) :
    rStackAt v n els (some (seekIdx (bktEnts ((v.data !! n).getD ∅)) k)) := by
  refine ⟨⟨pids, hp, ?_⟩, hnode⟩
  rw [stackPos_seek v _ pids els k (bktEnts_sorted' _) hp.2.1 hr]
  exact (Nat.min_eq_left (seekIdx_le _ _)).symm

theorem rStackAt_first (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null) (hf : sFirst els) :
    rStackAt v n els (some 0) := by
  refine ⟨⟨pids, hp, ?_⟩, hnode⟩
  rw [stackPos_first _ _ _ _ hf]; simp

theorem rStackAt_last (v : View) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hv : viewWF v) (hp : sPath (fun _ => none) v null n els pids)
    (hnode : ∀ e ∈ els, e.node' = null)
    (hl : sLast v (bktEnts ((v.data !! n).getD ∅)) pids els) :
    rStackAt v n els (some ((bktEnts ((v.data !! n).getD ∅)).length - 1)) := by
  refine ⟨⟨pids, hp, ?_⟩, hnode⟩
  rw [stackPos_last _ _ _ _ hp.2.1 hl]
  exact (Nat.min_eq_left (Nat.sub_le _ _)).symm

/-- `next` (readers; `stackPos_next`): the new stack's position, from the old one's. -/
theorem rStackAt_next (v : View) (n : GoString) (els els' : List elemRef) (pids pids' : List Nat)
    (d : Nat) (hp : sPath (fun _ => none) v null n els pids)
    (hp' : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sSucc d els els') (hlen : d + 1 < els.length ↔ d + 1 < els'.length)
    (hend : d + 1 < els.length → sEndBelow v (bktEnts ((v.data !! n).getD ∅)) pids els d) :
    let es := bktEnts ((v.data !! n).getD ∅)
    rStackAt v n els' (some (min (stackPos v es pids' els') es.length)) ∧
    (d + 1 = els.length → stackPos v es pids' els' = stackPos v es pids els + 1) ∧
    (d + 1 < els.length → stackPos v es pids' els' + leafIdx els =
      stackPos v es pids els + (entsIn es (pathBnd v pids els)).length) :=
  ⟨⟨⟨pids', hp', rfl⟩, hnode⟩, stackPos_next _ v _ null n els els' pids pids' d hp hp' hs hlen hend⟩

theorem rStackAt_prev (v : View) (n : GoString) (els els' : List elemRef) (pids' : List Nat)
    (i : Nat) (hv : viewWF v) (h : rStackAt v n els (some i)) (hi : 0 < i)
    (hp : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sPred v (bktEnts ((v.data !! n).getD ∅)) pids' els els') :
    rStackAt v n els' (some (i - 1)) := by
  sorry

/-- The writer's facts the writer lemmas take: `X` well-formed, `T.cur` its data, its base view
`v`, its registry at least `nl`, `b` the handle of bucket `n`. -/
def wCtx (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc)
    (n : GoString) : Prop :=
  wOK X ∧ T.cur = wtxData X ∧ X.v = v ∧ (∀ x y, nl x = some y → X.nloc !! x = some y) ∧
    bktLoc X n = some b

theorem wStackAt_seek (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat) (k : List w8)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids)
    (hr : sRoutes v (bktEnts ((T.cur !! n).getD ∅)) pids els k) :
    wStackAt nl v T b n els (some (seekIdx (bktEnts ((T.cur !! n).getD ∅)) k)) := by
  refine ⟨pids, hp, ?_⟩
  rw [stackPos_seek v _ pids els k (bktEnts_sorted' _) hp.2.1 hr]
  exact (Nat.min_eq_left (seekIdx_le _ _)).symm

theorem wStackAt_first (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids) (hf : sFirst els) :
    wStackAt nl v T b n els (some 0) := by
  refine ⟨pids, hp, ?_⟩
  rw [stackPos_first _ _ _ _ hf]; simp

theorem wStackAt_last (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els : List elemRef) (pids : List Nat)
    (hc : wCtx X nl v T b n) (hp : sPath nl v b n els pids)
    (hl : sLast v (bktEnts ((T.cur !! n).getD ∅)) pids els) :
    wStackAt nl v T b n els (some ((bktEnts ((T.cur !! n).getD ∅)).length - 1)) := by
  refine ⟨pids, hp, ?_⟩
  rw [stackPos_last _ _ _ _ hp.2.1 hl]
  exact (Nat.min_eq_left (Nat.sub_le _ _)).symm

/-- `next` (writers; `stackPos_next`): the new stack's position, from the old one's. Its
skipping of empty leaves keeps the position (an empty leaf's index `0` is its end). -/
theorem wStackAt_next (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els els' : List elemRef) (pids pids' : List Nat) (d : Nat)
    (hp : sPath nl v b n els pids) (hp' : sPath nl v b n els' pids') (hs : sSucc d els els')
    (hlen : d + 1 < els.length ↔ d + 1 < els'.length)
    (hend : d + 1 < els.length → sEndBelow v (bktEnts ((T.cur !! n).getD ∅)) pids els d) :
    let es := bktEnts ((T.cur !! n).getD ∅)
    wStackAt nl v T b n els' (some (min (stackPos v es pids' els') es.length)) ∧
    (d + 1 = els.length → stackPos v es pids' els' = stackPos v es pids els + 1) ∧
    (d + 1 < els.length → stackPos v es pids' els' + leafIdx els =
      stackPos v es pids els + (entsIn es (pathBnd v pids els)).length) :=
  ⟨⟨pids', hp', rfl⟩, stackPos_next nl v _ b n els els' pids pids' d hp hp' hs hlen hend⟩

/-- **A stack stays valid at the same `T` as the registry grows** (R6). -/
theorem wStackAt_stable (nl nl' : Loc → Option (Loc × Nat)) (v : View) (T : TxView) (b : Loc)
    (n : GoString) (els : List elemRef) (pos : Option Nat)
    (hgrow : ∀ x y, nl x = some y → nl' x = some y) (h : wStackAt nl v T b n els pos) :
    wStackAt nl' v T b n els pos := by
  unfold wStackAt at *
  cases pos with
  | none => trivial
  | some i =>
    obtain ⟨pids, hp, hi⟩ := h
    refine ⟨pids, ⟨hp.1, hp.2.1, hp.2.2.1, fun j e pid he hpid => ?_⟩, hi⟩
    obtain ⟨a, b, c, d⟩ := hp.2.2.2 j e pid he hpid
    exact ⟨fun hn => hgrow _ _ (a hn), b, c, d⟩

end cursor

end bbolt
end EtcdGrove
end Perennial
