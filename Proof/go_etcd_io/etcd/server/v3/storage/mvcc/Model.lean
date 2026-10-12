/-
The pure model of etcd's mvcc KV core (`server/v3/storage/mvcc`): revisions, the log of
changes, the states it determines, the key index and the backend's key bucket as functions
of the log. Lean-first (no Rocq counterpart); see `notes/decisions.md`, "mvcc".

**The log.** The store's history is a log `Log`: `log[r]` are the changes of revision `r`
(`Change`: a put of a key with a value and a lease, or a delete of a key), in sub-revision
order. Revision 0 is empty, and a fresh store starts at revision 1 with no changes
(`NewStore` sets `currentRev = 1`): `[[], []]`. The state at revision `r` (`stateAt`) is the
changes of revisions `0, ..., r` applied in order, a put being the client model's `putKv`
(`InvEtcdTxn.lean`: a new key is created at `r` with version 1, an existing one keeps its
create revision and gets version + 1) and a delete removing the key. So the state is the
client model's state, and etcd's history laws (`etcdState_revs`, ...) are theorems of this
model.

**The key index** (`index.go`, `key_index.go`) is a function of the log's events (`Ev`: a
revision `(main, sub)`, a key, and whether it is a tombstone): `indexOf (evsOf log)`, the
sorted list of `(key, KeyIndex)` built by `kiPut`/`kiTombstone` event by event, as the code
does. `kiGet` mirrors `keyIndex.get` (`kiFindGen` its `findGeneration`, `genWalk` its
`walk`), and the model's main theorem (`kiGet_indexOf`, `LogLemmas.lean`) says what it returns
of a key at a revision: the key-value of the state at that revision (its mod revision, create
revision and version), or nothing if the key is absent.

**The key bucket** (the backend's `Key` bucket) maps the bytes of a revision
(`revBytes`: 8 big-endian bytes of the main, `_`, 8 of the sub, and `t` for a tombstone) to
the protobuf encoding of the key-value the change wrote (`kvEncode`, an opaque encoding:
`proto.Marshal`/`Unmarshal` are the trust boundary; a tombstone's value is the key alone,
`zeroKv`): `bucketOf log`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## Revisions -/

/-- `mvcc.Revision`: a main revision and the sub-revision of a change in it. -/
structure Rev where
  main : w64
  sub : w64
deriving DecidableEq, Inhabited

/-- `Revision.GreaterThan`: lexicographic on `(main, sub)`, as signed integers. -/
def Rev.gt (a b : Rev) : Bool :=
  decide (sint.Z b.main < sint.Z a.main) ||
    (decide (a.main = b.main) && decide (sint.Z b.sub < sint.Z a.sub))

/-- The strict order on revisions `Rev.gt` decides. -/
def Rev.lt (a b : Rev) : Prop :=
  sint.Z a.main < sint.Z b.main ∨ (a.main = b.main ∧ sint.Z a.sub < sint.Z b.sub)

instance Rev.lt_dec : DecidableRel Rev.lt := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem Rev.gt_iff (a b : Rev) : Rev.gt a b = true ↔ Rev.lt b a := by
  unfold Rev.gt Rev.lt
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1.symm, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1.symm, h2⟩

theorem Rev.lt_irrefl (a : Rev) : ¬ Rev.lt a a := by
  unfold Rev.lt; omega

theorem Rev.lt_trans {a b c : Rev} (h1 : Rev.lt a b) (h2 : Rev.lt b c) : Rev.lt a c := by
  unfold Rev.lt at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by rw [← h2]; exact h1)
  · exact Or.inl (by rw [h1]; exact h2)
  · exact Or.inr ⟨h1.trans h2, by omega⟩

theorem Rev.gt_true_of_main_lt {a b : Rev} (h : sint.Z b.main < sint.Z a.main) :
    Rev.gt a b = true := by
  unfold Rev.gt; simp [h]

theorem Rev.gt_false_of_main_lt {a b : Rev} (h : sint.Z a.main < sint.Z b.main) :
    Rev.gt a b = false := by
  unfold Rev.gt
  have h1 : ¬ sint.Z b.main < sint.Z a.main := by omega
  have h2 : a.main ≠ b.main := by intro e; rw [e] at h; omega
  simp [h1, h2]

theorem Rev.gt_of_main_eq {a b : Rev} (h : a.main = b.main) :
    Rev.gt a b = decide (sint.Z b.sub < sint.Z a.sub) := by
  unfold Rev.gt; simp [h]

/-- The zero revision (`Revision{}`). -/
def Rev.zero : Rev := ⟨W64 0, W64 0⟩

/-! ## Changes and the log -/

/-- A change: a put of `key` with `value` and `lease`, or a delete of `key`. -/
inductive Change where
  | put (key value : GoString) (lease : w64)
  | del (key : GoString)

def Change.key : Change → GoString
  | .put k _ _ => k
  | .del k => k

def Change.isDel : Change → Bool
  | .put .. => false
  | .del _ => true

/-- One change of revision `r` applied to a state: a put is the client model's `putKv`, a
delete removes the key. -/
def applyChange (r : w64) (s : List EtcdKv) : Change → List EtcdKv
  | .put k v l => putKv r k v l s
  | .del k => s.filter (fun x => !decide (x.key = k))

/-- The changes of revision `r`, in order. -/
def applyChanges (r : w64) (s : List EtcdKv) (cs : List Change) : List EtcdKv :=
  cs.foldl (applyChange r) s

/-- The log: `log[r]` are the changes of revision `r`, in sub-revision order. -/
abbrev Log := List (List Change)

/-- The state after every revision of `log`. -/
def stateAfter (log : Log) : List EtcdKv :=
  log.zipIdx.foldl (fun s p => applyChanges (W64 p.2) s p.1) []

/-- The state at revision `r`: after revisions `0, ..., r`. -/
def stateAt (log : Log) (r : Nat) : List EtcdKv := stateAfter (log.take (r + 1))

/-- The key-value of `k` in a state. -/
def findKey (k : GoString) (s : List EtcdKv) : Option EtcdKv := s.find? (fun v => decide (v.key = k))

/-- The state's keys are strictly increasing. -/
def Sorted (s : List EtcdKv) : Prop := s.Pairwise etcdKvLess

/-! ## Events: what the key index sees of a change -/

/-- An event of the key index: the revision of a change, its key, and whether it is a
tombstone (a delete). -/
structure Ev where
  rev : Rev
  key : GoString
  tomb : Bool

/-- The events of revision `r`'s changes `cs`. -/
def evsOfRev (r : Nat) (cs : List Change) : List Ev :=
  cs.zipIdx.map fun p => { rev := ⟨W64 r, W64 p.2⟩, key := p.1.key, tomb := p.1.isDel }

/-- The events of the whole log, in order. -/
def evsOf (log : Log) : List Ev :=
  (log.zipIdx.map fun p => evsOfRev p.2 p.1).flatten

/-! ## The key index (`key_index.go`) -/

/-- A generation of a key: its versions' revisions, the revision it was created at and the
number of versions (`ver`); a generation ends with the tombstone that deletes the key, and
a new, empty one follows it. -/
structure Gen where
  ver : w64
  created : Rev
  revs : List Rev
deriving Inhabited

def Gen.empty : Gen := { ver := W64 0, created := Rev.zero, revs := [] }

/-- The mutable part of a `keyIndex` (its key is fixed): the revision of its last change and
its generations, oldest first (at least one once a revision was put). -/
structure KeyIndex where
  modified : Rev
  gens : List Gen
deriving Inhabited

/-- A fresh `keyIndex{key: k}`: no generations. -/
def KeyIndex.fresh : KeyIndex := { modified := Rev.zero, gens := [] }

/-- `g.revs = append(g.revs, rev); g.ver++`, and `g.created = rev` if `g` was empty. -/
def genPut (g : Gen) (rev : Rev) : Gen :=
  { ver := g.ver + W64 1, created := if g.revs = [] then rev else g.created,
    revs := g.revs ++ [rev] }

/-- `keyIndex.put(main, sub)` (the revision must be above `modified`): the revision is
appended to the last generation (a first one is made if there is none). -/
def kiPut (ki : KeyIndex) (rev : Rev) : KeyIndex :=
  let gens := if ki.gens = [] then [Gen.empty] else ki.gens
  { modified := rev, gens := gens.dropLast ++ [genPut (gens.getLastD Gen.empty) rev] }

/-- The generations `kiPut` starts from: a first one if there is none. -/
def gensOrEmpty (gens : List Gen) : List Gen := if gens = [] then [Gen.empty] else gens

theorem gensOrEmpty_ne_nil (gens : List Gen) : gensOrEmpty gens ≠ [] := by
  unfold gensOrEmpty; split <;> simp_all

theorem kiPut_gens (ki : KeyIndex) (rev : Rev) :
    (kiPut ki rev).gens =
      (gensOrEmpty ki.gens).dropLast ++ [genPut ((gensOrEmpty ki.gens).getLastD Gen.empty) rev] := rfl

theorem kiPut_modified (ki : KeyIndex) (rev : Rev) : (kiPut ki rev).modified = rev := rfl

/-- Setting the last element. -/
theorem set_last {α : Type} (l : List α) (x : α) (h : l ≠ []) :
    l.set (l.length - 1) x = l.dropLast ++ [x] := by
  apply List.ext_getElem?
  intro j
  have hpos : 0 < l.length := List.length_pos_iff.2 h
  have hdl : l.dropLast.length = l.length - 1 := List.length_dropLast
  by_cases hj : j = l.length - 1
  · subst hj
    rw [List.getElem?_set_self (by omega), List.getElem?_append_right (by omega), hdl]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hj)]
    by_cases hlt : j < l.length - 1
    · rw [List.getElem?_append_left (by omega)]
      simp only [List.getElem?_dropLast, hlt, ↓reduceIte]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega), hdl]
      rw [List.getElem?_eq_none (by simp only [List.length_singleton]; omega)]

/-- The last element, as the index `length - 1`. -/
theorem getElem?_last {α : Type} [Inhabited α] (l : List α) (h : l ≠ []) :
    l[l.length - 1]? = some (l.getLastD default) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  obtain ⟨x, hx⟩ : ∃ x, l[l.length - 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by have := List.length_pos_iff.2 h; omega)⟩
  rw [hx]; rfl

/-- `keyIndex.tombstone(main, sub)` when the last generation is not empty: a put, then a new
empty generation. -/
def kiTombstone (ki : KeyIndex) (rev : Rev) : KeyIndex :=
  let ki' := kiPut ki rev
  { ki' with gens := ki'.gens ++ [Gen.empty] }

/-- `keyIndex.isEmpty()`: one generation, with no revision. -/
def kiIsEmpty (ki : KeyIndex) : Bool :=
  match ki.gens with
  | [g] => decide (g.revs = [])
  | _ => false

/-- The last generation is empty (`tombstone` then returns `ErrRevisionNotFound`). -/
def kiLastEmpty (ki : KeyIndex) : Bool :=
  decide ((ki.gens.getLastD Gen.empty).revs = [])

/-- `generation.walk(f)`: the revisions are visited from the last to the first until `f`
returns false; the position where it stopped, or `-1` if it did not. With `p` the
predicate `f` decides: the largest index whose revision fails `p`. -/
def genWalk (revs : List Rev) (p : Rev → Bool) : Int :=
  match revs.reverse.findIdx? (fun r => !p r) with
  | some i => (revs.length - 1 - i : Nat)
  | none => -1

theorem genWalk_eq_none {revs : List Rev} {p : Rev → Bool} (h : ∀ r ∈ revs, p r = true) :
    genWalk revs p = -1 := by
  unfold genWalk
  rw [List.findIdx?_eq_none_iff.2 (fun r hr => by simp [h r (List.mem_reverse.1 hr)])]

theorem genWalk_eq_some {revs : List Rev} {p : Rev → Bool} (j : Nat) (hj : j < revs.length)
    (hfail : p (revs[j]'hj) = false)
    (hpass : ∀ (k : Nat) (hk : k < revs.length), j < k → p (revs[k]'hk) = true) :
    genWalk revs p = (j : Int) := by
  unfold genWalk
  have hlen : revs.reverse.length = revs.length := List.length_reverse
  have hi : revs.length - 1 - j < revs.reverse.length := by rw [hlen]; omega
  rw [List.findIdx?_eq_some_iff_getElem.2 ⟨hi, ?_, ?_⟩]
  · show ((revs.length - 1 - (revs.length - 1 - j) : Nat) : Int) = (j : Int)
    congr 1
    omega
  · rw [List.getElem_reverse]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
    have e : revs.length - 1 - (revs.length - 1 - j) = j := by omega
    simp only [e]
    exact hfail
  · intro k hk
    rw [List.getElem_reverse]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
    exact hpass _ (by omega) (by omega)

theorem set_same {α : Type} {l : List α} {i : Nat} {gm : α} (h : l[i]? = some gm) : l.set i gm = l := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j = i
  · subst hj; rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 h).1, h]
  · rw [List.getElem?_set_ne (Ne.symm hj)]

/-- `keyIndex.findGeneration(rev)`, from the last generation down (`fuel` generations are
left to look at): an empty generation is skipped; a generation that is not the last and
whose tombstone (its last revision) is at or before `rev` means the key is absent at `rev`;
a generation whose first revision is at or before `rev` is the key's at `rev`. -/
def kiFindGenAux (gens : List Gen) (rev : w64) : Nat → Option Nat
  | 0 => none
  | cg + 1 =>
    let g := gens.getD cg Gen.empty
    if g.revs = [] then kiFindGenAux gens rev cg
    else if cg ≠ gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z rev then none
    else if sint.Z (g.revs.headD Rev.zero).main ≤ sint.Z rev then some cg
    else kiFindGenAux gens rev cg

def kiFindGen (ki : KeyIndex) (rev : w64) : Option Nat := kiFindGenAux ki.gens rev ki.gens.length

/-- One step of the scan, from generation `cg`. -/
theorem kiFindGenAux_succ (gens : List Gen) (rev : w64) (cg : Nat) :
    kiFindGenAux gens rev (cg + 1) =
      (let g := gens.getD cg Gen.empty
       if g.revs = [] then kiFindGenAux gens rev cg
       else if cg ≠ gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z rev then none
       else if sint.Z (g.revs.headD Rev.zero).main ≤ sint.Z rev then some cg
       else kiFindGenAux gens rev cg) := rfl

theorem kiFindGenAux_skip {gens : List Gen} {rev : w64} {cg : Nat}
    (h : (gens.getD cg Gen.empty).revs = []) :
    kiFindGenAux gens rev (cg + 1) = kiFindGenAux gens rev cg := by
  rw [kiFindGenAux_succ]; simp only [h, ↓reduceIte]

theorem kiFindGenAux_tomb {gens : List Gen} {rev : w64} {cg : Nat}
    (hne : (gens.getD cg Gen.empty).revs ≠ []) (hcg : cg ≠ gens.length - 1)
    (ht : sint.Z ((gens.getD cg Gen.empty).revs.getLastD Rev.zero).main ≤ sint.Z rev) :
    kiFindGenAux gens rev (cg + 1) = none := by
  rw [kiFindGenAux_succ]
  simp only [hne, ↓reduceIte, hcg, ht, ne_eq, not_false_eq_true, and_self]

theorem kiFindGenAux_found {gens : List Gen} {rev : w64} {cg : Nat}
    (hne : (gens.getD cg Gen.empty).revs ≠ [])
    (hnot : ¬ (cg ≠ gens.length - 1 ∧
      sint.Z ((gens.getD cg Gen.empty).revs.getLastD Rev.zero).main ≤ sint.Z rev))
    (hf : sint.Z ((gens.getD cg Gen.empty).revs.headD Rev.zero).main ≤ sint.Z rev) :
    kiFindGenAux gens rev (cg + 1) = some cg := by
  rw [kiFindGenAux_succ]; simp only [hne, ↓reduceIte, hnot, hf]

theorem kiFindGenAux_next {gens : List Gen} {rev : w64} {cg : Nat}
    (hne : (gens.getD cg Gen.empty).revs ≠ [])
    (hnot : ¬ (cg ≠ gens.length - 1 ∧
      sint.Z ((gens.getD cg Gen.empty).revs.getLastD Rev.zero).main ≤ sint.Z rev))
    (hnf : ¬ sint.Z ((gens.getD cg Gen.empty).revs.headD Rev.zero).main ≤ sint.Z rev) :
    kiFindGenAux gens rev (cg + 1) = kiFindGenAux gens rev cg := by
  rw [kiFindGenAux_succ]; simp only [hne, ↓reduceIte, hnot, hnf]

theorem kiFindGenAux_lt {gens : List Gen} {rev : w64} : ∀ {fuel i : Nat},
    kiFindGenAux gens rev fuel = some i → i < fuel
  | 0, i, h => by simp [kiFindGenAux] at h
  | cg + 1, i, h => by
    rw [kiFindGenAux_succ] at h
    simp only at h
    split at h
    · exact Nat.lt_succ_of_lt (kiFindGenAux_lt h)
    · split at h
      · cases h
      · split at h
        · cases h; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (kiFindGenAux_lt h)

theorem kiFindGen_lt {ki : KeyIndex} {rev : w64} {i : Nat} (h : kiFindGen ki rev = some i) :
    i < ki.gens.length := kiFindGenAux_lt h

theorem genWalk_range (revs : List Rev) (p : Rev → Bool) :
    -1 ≤ genWalk revs p ∧ genWalk revs p < revs.length := by
  unfold genWalk
  split
  · rename_i i hi
    have := (List.findIdx?_eq_some_iff_getElem.1 hi).1
    rw [List.length_reverse] at this
    constructor <;> omega
  · constructor <;> omega

/-- `get`'s walk predicate: the revision is above `atRev`. -/
def pAbove (atRev : w64) (r : Rev) : Bool := decide (sint.Z atRev < sint.Z r.main)

/-- `keyIndex.get(atRev)` on a non-empty key index: the key's revision at `atRev` (its last
revision at or before `atRev`), the revision its generation was created at, and its version
(the number of its generation's revisions up to it); nothing if the key is absent at
`atRev`. -/
def kiGet (ki : KeyIndex) (atRev : w64) : Option (Rev × Rev × w64) :=
  match kiFindGen ki atRev with
  | none => none
  | some gi =>
    let g := ki.gens.getD gi Gen.empty
    if g.revs = [] then none
    else
      let n := genWalk g.revs (pAbove atRev)
      if n = -1 then none
      else some (g.revs.getD n.toNat Rev.zero, g.created,
        g.ver - W64 (g.revs.length - n.toNat - 1))

/-! ## The index (`index.go`): key indexes by key -/

/-- The index: `(key, keyIndex)` pairs, keys strictly increasing. -/
abbrev IndexM := List (GoString × KeyIndex)

/-- The btree's order on the index's items: by key (`keyIndex.Less`). -/
def idxLess (a b : GoString × KeyIndex) : Prop := go.GoStringLt a.1 b.1

instance idxLess_dec : DecidableRel idxLess := fun a b => go.goStringLt_dec a.1 b.1

/-- The key index of `k`, if any. -/
def idxGet (idx : IndexM) (k : GoString) : Option KeyIndex :=
  (btFind idxLess (k, KeyIndex.fresh) idx).map Prod.snd

/-- `treeIndex.Put(key, rev)` on the index: the key's index gets the revision (a fresh one
is inserted if the key has none). -/
def idxPut (idx : IndexM) (k : GoString) (rev : Rev) : IndexM :=
  match idxGet idx k with
  | some ki => btInsert idxLess (k, kiPut ki rev) idx
  | none => btInsert idxLess (k, kiPut KeyIndex.fresh rev) idx

/-- `treeIndex.Tombstone(key, rev)` on the index, when the key has an index whose last
generation is not empty (otherwise the code returns `ErrRevisionNotFound` and changes
nothing: the model leaves the index as it is). -/
def idxTombstone (idx : IndexM) (k : GoString) (rev : Rev) : IndexM :=
  match idxGet idx k with
  | some ki => if kiLastEmpty ki then idx else btInsert idxLess (k, kiTombstone ki rev) idx
  | none => idx

/-- One event applied to the index. -/
def idxApply (idx : IndexM) (ev : Ev) : IndexM :=
  if ev.tomb then idxTombstone idx ev.key ev.rev else idxPut idx ev.key ev.rev

/-- The index after the events `evs`. -/
def indexOf (evs : List Ev) : IndexM := evs.foldl idxApply []

/-! ## The key bucket -/

/-- The protobuf encoding of a `mvccpb.KeyValue` (`proto.Marshal`): opaque; its only
properties are the trusted specs of `Marshal` and `Unmarshal`. -/
opaque kvEncode : EtcdKv → GoString

/-- The bytes of a revision as a key of the backend's `Key` bucket (`BucketKeyToBytes`): the
main and the sub in big-endian, separated by `_`, and `t` appended for a tombstone. -/
def revBytes (rev : Rev) (tomb : Bool) : GoString :=
  u64Be rev.main ++ [W8 95] ++ u64Be rev.sub ++ (if tomb then [W8 116] else [])

theorem revBytes_length (rev : Rev) (tomb : Bool) :
    (revBytes rev tomb).length = if tomb then 18 else 17 := by
  unfold revBytes
  cases tomb <;> simp [u64Be_length]

/-- The key-value a change of revision `r` at position `i` of `cs` writes (`stateBefore` is
the state before the changes of `r`): for a put, the key's new key-value; for a delete, the
key alone (`zeroKv`). -/
def changeKv (r : w64) (before : List EtcdKv) (cs : List Change) (i : Nat) : Option EtcdKv :=
  match cs[i]? with
  | some (.put k _ _) => findKey k (applyChanges r before (cs.take (i + 1)))
  | some (.del k) => some (zeroKv k)
  | none => none

/-- The bucket's entries of revision `r` (changes `cs`, state `before` before them): the
bytes of each change's revision, with the encoding of what it wrote. -/
def bucketOfRev (r : Nat) (before : List EtcdKv) (cs : List Change) : List (GoString × GoString) :=
  cs.zipIdx.filterMap fun p =>
    (changeKv (W64 r) before cs p.2).map fun kv => (revBytes ⟨W64 r, W64 p.2⟩ p.1.isDel, kvEncode kv)

/-- The bucket of the whole log: the entries of every revision. -/
def bucketOf (log : Log) : List (GoString × GoString) :=
  (log.zipIdx.map fun p => bucketOfRev p.2 (stateAt log (p.2 - 1)) p.1).flatten

/-- The bucket as a map (the backend's view): the entries' keys are distinct
(`bucketOf_nodup`, `Lemmas.lean`). -/
def bucketMap (log : Log) : GMap GoString GoString :=
  (bucketOf log).foldl (fun m p => GMap.insert p.1 p.2 m) GMap.empty

/-! ## Well-formed logs -/

/-- Revision 0 is empty, and every delete is of a key present at that point (the code deletes
only keys the index finds at the revision). -/
def LogWf (log : Log) : Prop :=
  log[0]? = some [] ∧
  ∀ (r : Nat) (cs : List Change) (i : Nat) (k : GoString), log[r]? = some cs →
    cs[i]? = some (.del k) →
    (findKey k (applyChanges (W64 r) (stateAt log (r - 1)) (cs.take i))).isSome

end mvcc
end EtcdGrove
end Perennial
