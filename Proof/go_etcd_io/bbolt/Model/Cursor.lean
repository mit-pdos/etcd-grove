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

/-- `els'` (path `pids'`) is the in-order successor of `els`: equal above some depth `d`, one
further at `d`, first below. -/
def sSucc (els els' : List elemRef) : Prop :=
  ∃ d, d < els.length ∧ d < els'.length ∧
    (els'.take d).map (·.index') = (els.take d).map (·.index') ∧
    (∃ e e', els[d]? = some e ∧ els'[d]? = some e' ∧ e'.index'.toNat = e.index'.toNat + 1) ∧
    ∀ j e', d < j → els'[j]? = some e' → e'.index'.toNat = 0

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

theorem rStackAt_next (v : View) (n : GoString) (els els' : List elemRef) (pids' : List Nat)
    (i : Nat) (hv : viewWF v) (h : rStackAt v n els (some i))
    (hp : sPath (fun _ => none) v null n els' pids') (hnode : ∀ e ∈ els', e.node' = null)
    (hs : sSucc els els') :
    rStackAt v n els' (some (min (i + 1) (bktEnts ((v.data !! n).getD ∅)).length)) := by
  sorry

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

/-- `next` (with its skipping of empty leaves, which keeps the position). -/
theorem wStackAt_next (X : WX) (nl : Loc → Option (Loc × Nat)) (v : View) (T : TxView)
    (b : Loc) (n : GoString) (els els' : List elemRef) (pids' : List Nat) (i : Nat)
    (hc : wCtx X nl v T b n) (h : wStackAt nl v T b n els (some i))
    (hp : sPath nl v b n els' pids') (hs : sSucc els els') :
    wStackAt nl v T b n els' (some (min (i + 1) (bktEnts ((T.cur !! n).getD ∅)).length)) := by
  sorry

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
