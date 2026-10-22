/-
Lean-first (no Rocq counterpart).

# The Kubernetes etcd3 store's model (phase 2 of `notes/k8s-etcd3-plan.md`)

A Lean copy of Kubernetes' storage test model, `correctness.Model`
(`staging/src/k8s.io/apiserver/pkg/storage/testing/correctness/model.go`, kubernetes master
`d9cafe4`), for its unary operations: `create`, `delete`, `update` (`GuaranteedUpdate`) and
`get`. Objects are abstract (`Obj`, D30b): an item is an object without its resource version, the
resource version (the etcd key-value's mod revision), and whether its stored value is what the
store would write for it now (`canon`, D30g). The state is the items by etcd key (the store's
prepared key, `Model.Prefix + key`) and the resource version (etcd's revision).

The one difference from `correctness.Model` is `canon`. The store skips a no-op update only when
the stored value is canonical and not stale (`store.go:547`), so `KSt.update` writes unless the
object is unchanged *and* the item is canonical. `correctness.Model.update` skips every update
that leaves the object unchanged (`KSt.updateM`, the Model's), which rejects the store's
behavior on non-canonical data (`issues/k8s-correctness-model-noop-rewrite.md`). On a state
whose items are all canonical the two agree (`KSt.update_eq_updateM`).

The abstraction (D30i) goes through linkv's model of etcd's KV state (`linkv.MSt`, `absSt`):
`absK dec pfx m` decodes every key under the store's prefix with the codec's `dec` (what a
stored value reads as). Each operation's transaction (`createTxn`, `deleteTxn`, `updateTxn`:
`OptimisticPut`'s and `OptimisticDelete`'s, `linkv.txnOf`) moves `absK` as the operation, at the
level of `linkv.mStep` (the `absK_*` theorems below). `TxnModelKV.lean`'s `absSt_kvOpStep`
lifts this to etcd's `kvOpStep`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.TxnModel
public import Perennial.Std.ByteString

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace k8s

open linkv

variable {Obj : Type} [DecidableEq Obj]

/-! ## The model -/

/-- An item: an object without its resource version, its resource version, and whether its
stored value is the store's current encoding of it, not stale (`canon`, D30g). -/
structure KItem (Obj : Type) where
  obj : Obj
  rv : Nat
  canon : Bool

/-- **The model's state**: the items by etcd key and the current resource version
(`correctness.Model`'s `Items`, keyed by `Prefix + key`, and `ResourceVersion`). -/
structure KSt (Obj : Type) where
  items : GoString → Option (KItem Obj)
  rv : Nat

/-- The items with `k` set to `it`. -/
def KSt.setItem (s : KSt Obj) (k : GoString) (it : KItem Obj) : GoString → Option (KItem Obj) :=
  fun k' => if k' = k then some it else s.items k'

/-- The items without `k`. -/
def KSt.delItem (s : KSt Obj) (k : GoString) : GoString → Option (KItem Obj) :=
  fun k' => if k' = k then none else s.items k'

/-- An error the model answers with: `storage.NewKeyNotFoundError(key, rv)`,
`storage.NewKeyExistsError(key, 0)`, `storage.ErrResourceVersionSetOnCreate`,
`storage.NewTooLargeResourceVersionError(req, cur, 0)`, or a caller's error (a failed
precondition, `validateDeletion`'s or `tryUpdate`'s), of the caller's type `E`. -/
inductive KErr (E : Type) where
  | notFound (key : GoString) (rv : Nat)
  | keyExists (key : GoString)
  | rvSetOnCreate
  | tooLarge (req cur : Nat)
  | user (e : E)

/-- An answer: an object at a resource version (`Response{Object: obj}`, the object's resource
version set), the zero object (`NewFunc()`: `Get` with `IgnoreNotFound`), or an error. -/
inductive KResp (Obj E : Type) where
  | obj (o : Obj) (rv : Nat)
  | zero
  | err (e : KErr E)

variable {E : Type}

/-- **`create`** of the object `o` (input resource version `inRv`) at `k`: an error if the input
has a resource version or the key exists, else the item at the next resource version. A new
item is the store's encoding, so canonical. -/
def KSt.create (s : KSt Obj) (k : GoString) (o : Obj) (inRv : Nat) : KSt Obj × KResp Obj E :=
  if inRv ≠ 0 then (s, .err .rvSetOnCreate)
  else match s.items k with
    | some _ => (s, .err (.keyExists k))
    | none => (⟨s.setItem k ⟨o, s.rv + 1, true⟩, s.rv + 1⟩, .obj o (s.rv + 1))

/-- **`delete`** of `k`, with the preconditions `pre` and the callback `validate` (`none`: they
pass; `some e`: they fail with `e`) on the stored object and its resource version: not found,
their error, or the item gone at the next resource version, answered with the deleted object at
that resource version. -/
def KSt.delete (s : KSt Obj) (k : GoString) (pre validate : Obj → Nat → Option E) :
    KSt Obj × KResp Obj E :=
  match s.items k with
  | none => (s, .err (.notFound k s.rv))
  | some it => match pre it.obj it.rv with
    | some e => (s, .err (.user e))
    | none => match validate it.obj it.rv with
      | some e => (s, .err (.user e))
      | none => (⟨s.delItem k, s.rv + 1⟩, .obj it.obj (s.rv + 1))

/-- The object an update starts from: the item's, or (with `ignoreNotFound`, no item) the zero
object `z` at resource version `0`, as not stored. -/
def KSt.current (s : KSt Obj) (k : GoString) (ignoreNotFound : Bool) (z : Obj) :
    Option (Obj × Nat) :=
  match s.items k with
  | some it => some (it.obj, it.rv)
  | none => if ignoreNotFound then some (z, 0) else none

/-- **`update`** (`GuaranteedUpdate`) of `k` by `f` (`tryUpdate`, a function of the current
object and resource version: its result or its error), after the preconditions `pre`. A stored
item whose object `f` leaves unchanged is answered as it is, when it is canonical (D30g);
otherwise the result is written at the next resource version. -/
def KSt.update (s : KSt Obj) (k : GoString) (ignoreNotFound : Bool) (z : Obj)
    (pre : Obj → Nat → Option E) (f : Obj → Nat → Except E Obj) : KSt Obj × KResp Obj E :=
  match s.current k ignoreNotFound z with
  | none => (s, .err (.notFound k s.rv))
  | some (o, r) => match pre o r with
    | some e => (s, .err (.user e))
    | none => match f o r with
      | .error e => (s, .err (.user e))
      | .ok o' =>
        match s.items k with
        | some it =>
          if o' = it.obj ∧ it.canon then (s, .obj it.obj it.rv)
          else (⟨s.setItem k ⟨o', s.rv + 1, true⟩, s.rv + 1⟩, .obj o' (s.rv + 1))
        | none => (⟨s.setItem k ⟨o', s.rv + 1, true⟩, s.rv + 1⟩, .obj o' (s.rv + 1))

/-- `correctness.Model.update` as Kubernetes wrote it: a stored item whose object `f` leaves
unchanged is never rewritten (it ignores `canon`). -/
def KSt.updateM (s : KSt Obj) (k : GoString) (ignoreNotFound : Bool) (z : Obj)
    (pre : Obj → Nat → Option E) (f : Obj → Nat → Except E Obj) : KSt Obj × KResp Obj E :=
  match s.current k ignoreNotFound z with
  | none => (s, .err (.notFound k s.rv))
  | some (o, r) => match pre o r with
    | some e => (s, .err (.user e))
    | none => match f o r with
      | .error e => (s, .err (.user e))
      | .ok o' =>
        match s.items k with
        | some it =>
          if o' = it.obj then (s, .obj it.obj it.rv)
          else (⟨s.setItem k ⟨o', s.rv + 1, true⟩, s.rv + 1⟩, .obj o' (s.rv + 1))
        | none => (⟨s.setItem k ⟨o', s.rv + 1, true⟩, s.rv + 1⟩, .obj o' (s.rv + 1))

/-- **`get`** of `k` at a requested minimum resource version `req` (`0`: none): too large a
version, the item, the zero object (`ignoreNotFound`), or not found. -/
def KSt.get (s : KSt Obj) (k : GoString) (req : Nat) (ignoreNotFound : Bool) : KResp Obj E :=
  if req > s.rv then .err (.tooLarge req s.rv)
  else match s.items k with
    | some it => .obj it.obj it.rv
    | none => if ignoreNotFound then .zero else .err (.notFound k s.rv)

/-- Every item is canonical (D30g): what `TestCorrectness`'s runs keep. -/
def KSt.AllCanon (s : KSt Obj) : Prop := ∀ k it, s.items k = some it → it.canon = true

/-- **On canonical states the model is `correctness.Model`'s** (D30g). -/
theorem KSt.update_eq_updateM (s : KSt Obj) (hc : s.AllCanon) (k : GoString)
    (ignoreNotFound : Bool) (z : Obj) (pre : Obj → Nat → Option E)
    (f : Obj → Nat → Except E Obj) :
    s.update k ignoreNotFound z pre f = s.updateM k ignoreNotFound z pre f := by
  unfold KSt.update KSt.updateM
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i o' _
        cases hk : s.items k with
        | none => rfl
        | some it =>
          simp only [hc k it hk, and_true]

/-- Every write keeps the items canonical. -/
theorem KSt.AllCanon_create (s : KSt Obj) (hc : s.AllCanon) (k : GoString) (o : Obj) (inRv : Nat) :
    (s.create (E := E) k o inRv).1.AllCanon := by
  unfold KSt.create
  split
  · exact hc
  · split
    · exact hc
    · intro k' it h
      simp only [KSt.setItem] at h
      split at h
      · cases h; rfl
      · exact hc k' it h

theorem KSt.AllCanon_delete (s : KSt Obj) (hc : s.AllCanon) (k : GoString)
    (pre validate : Obj → Nat → Option E) : (s.delete k pre validate).1.AllCanon := by
  unfold KSt.delete
  split
  · exact hc
  · split
    · exact hc
    · split
      · exact hc
      · intro k' it h
        simp only [KSt.delItem] at h
        split at h
        · cases h
        · exact hc k' it h

theorem KSt.AllCanon_update (s : KSt Obj) (hc : s.AllCanon) (k : GoString)
    (ignoreNotFound : Bool) (z : Obj) (pre : Obj → Nat → Option E)
    (f : Obj → Nat → Except E Obj) : (s.update k ignoreNotFound z pre f).1.AllCanon := by
  have hset : ∀ (o' : Obj), (KSt.mk (s.setItem k ⟨o', s.rv + 1, true⟩) (s.rv + 1)).AllCanon := by
    intro o' k' it h
    simp only [KSt.setItem] at h
    split at h
    · cases h; rfl
    · exact hc k' it h
  unfold KSt.update
  split
  · exact hc
  · split
    · exact hc
    · split
      · exact hc
      · split
        · split
          · exact hc
          · exact hset _
        · exact hset _

/-! ## The abstraction of etcd's state -/

/-- A stored value's reading (the codec contract's `dec`, D30b): its object and whether it is
canonical (D30g), or `none` if it does not decode. -/
abbrev Dec (Obj : Type) := GoString → Option (Obj × Bool)

/-- A key-value's item: its value decoded, its mod revision. -/
def itemOf (dec : Dec Obj) (x : VR GoString) : Option (KItem Obj) :=
  (dec x.val).map fun oc => ⟨oc.1, uint.nat x.mod, oc.2⟩

/-- **The model state of linkv's state** under the prefix `pfx`: every key under it, decoded. -/
def absK (dec : Dec Obj) (pfx : GoString) (m : MSt GoString GoString) : KSt Obj :=
  ⟨fun k => if pfx <+: k then (m.kv k).bind (itemOf dec) else none, m.rev⟩

/-- **The state is the store's** (the store invariant of phase 1): every value under the prefix
decodes, every mod revision is a revision so far (above `0`), and the revision is below `2^63`
(etcd's, `int64`). -/
def KWf (dec : Dec Obj) (pfx : GoString) (m : MSt GoString GoString) : Prop :=
  (∀ k x, pfx <+: k → m.kv k = some x → (dec x.val).isSome) ∧
  (∀ k x, m.kv k = some x → 0 < uint.nat x.mod ∧ uint.nat x.mod ≤ m.rev) ∧
  m.rev + 1 < 2 ^ 63

/-! ## The store's transactions -/

/-- `OptimisticPut(key, value, rev, PutOptions{GetOnFailure: g})`'s transaction: if the key's mod
revision is `rev` (`0`: absent), put the value, else get the key if `g`. -/
def putTxn (k v : GoString) (rev : w64) (g : Bool) : MIn GoString GoString :=
  .txn [.mod k rev] [.put k v] (if g then [.get k] else [])

/-- `OptimisticDelete(key, rev, DeleteOptions{GetOnFailure: g})`'s transaction. -/
def delTxn (k : GoString) (rev : w64) (g : Bool) : MIn GoString GoString :=
  .txn [.mod k rev] [.del k] (if g then [.get k] else [])

/-- A key's mod revision in the store, `0` if absent (`ModRevision(key)`'s operand). -/
def modOf (m : MStore GoString GoString) (k : GoString) : w64 :=
  ((m k).map VR.mod).getD (W64 0)

/-- The comparison holds exactly when the key's mod revision is `rev`. -/
theorem holds_mod (m : MStore GoString GoString) (k : GoString) (rev : w64) :
    [MCmp.mod k rev].all (MCmp.holds m) = decide (modOf m k = rev) := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, MCmp.holds, modOf]
  exact decide_eq_decide.2 Iff.rfl

/-- A put transaction: its step and answer, by its comparison. -/
theorem mStep_putTxn (ks : List GoString) (m : MSt GoString GoString) (k v : GoString)
    (rev : w64) (g : Bool) :
    mStep ks (putTxn k v rev g) m =
      if modOf m.kv k = rev then (⟨m.kv.put (m.rev + 1) k v, m.rev + 1⟩, .txn (m.rev + 1) true [.put])
      else (m, .txn m.rev false (if g then [.get (m.kv k)] else [])) := by
  unfold putTxn
  simp only [mStep, holds_mod]
  by_cases h : modOf m.kv k = rev
  · simp [h, runOps, MOp.run]
  · cases g <;> simp [h, runOps, MOp.run]

/-- A delete transaction: its step and answer, by its comparison (a present key: a mod revision
above `0`, so a matching nonzero `rev` means the key is there). -/
theorem mStep_delTxn (ks : List GoString) (m : MSt GoString GoString) (k : GoString)
    (rev : w64) (g : Bool) (x : VR GoString) (hx : m.kv k = some x) :
    mStep ks (delTxn k rev g) m =
      if x.mod = rev then (⟨m.kv.del k, m.rev + 1⟩, .txn (m.rev + 1) true [.del 1])
      else (m, .txn m.rev false (if g then [.get (some x)] else [])) := by
  have hmod : modOf m.kv k = x.mod := by simp [modOf, hx]
  unfold delTxn
  simp only [mStep, holds_mod, hmod]
  by_cases h : x.mod = rev
  · simp [h, runOps, MOp.run, hx]
  · cases g <;> simp [h, runOps, MOp.run, hx]

/-! ## The store's transactions move the abstraction as the model -/

section abs
variable (dec : Dec Obj) (pfx : GoString)

theorem uint_nat_W64 (r : Nat) (h : r < 2 ^ 63) : uint.nat (W64 (r : Int)) = r := by
  have : (r : Int) < 2 ^ 64 := by omega
  simp only [uint.nat, W64]
  rw [BitVec.toNat_ofInt]
  omega

/-- A put of a value that reads as the canonical `o` sets the key's item at the next revision. -/
theorem absK_put (m : MSt GoString GoString) (hwf : KWf dec pfx m) (k v : GoString) (o : Obj)
    (hk : pfx <+: k) (hv : dec v = some (o, true)) :
    absK dec pfx ⟨m.kv.put (m.rev + 1) k v, m.rev + 1⟩ =
      ⟨(absK dec pfx m).setItem k ⟨o, m.rev + 1, true⟩, m.rev + 1⟩ := by
  obtain ⟨-, -, hb⟩ := hwf
  unfold absK KSt.setItem
  simp only [KSt.mk.injEq, and_true]
  funext k'
  by_cases h : k' = k
  · subst h
    simp [MStore.put, hk, itemOf, hv]
    omega
  · simp [MStore.put, h]

/-- A delete removes the key's item. -/
theorem absK_del (m : MSt GoString GoString) (k : GoString) :
    absK dec pfx ⟨m.kv.del k, m.rev + 1⟩ = ⟨(absK dec pfx m).delItem k, m.rev + 1⟩ := by
  unfold absK KSt.delItem
  simp only [KSt.mk.injEq, and_true]
  funext k'
  by_cases h : k' = k
  · subst h; simp [MStore.del]
  · simp [MStore.del, h]

/-- A present key under the prefix has an item, with its mod revision as resource version. -/
theorem absK_some (m : MSt GoString GoString) (hwf : KWf dec pfx m) (k : GoString)
    (hk : pfx <+: k) (x : VR GoString) (hx : m.kv k = some x) :
    ∃ it, (absK dec pfx m).items k = some it ∧ it.rv = uint.nat x.mod := by
  obtain ⟨hd, -, -⟩ := hwf
  obtain ⟨oc, hoc⟩ := Option.isSome_iff_exists.1 (hd k x hk hx)
  exact ⟨⟨oc.1, uint.nat x.mod, oc.2⟩, by simp [absK, hk, hx, itemOf, hoc], rfl⟩

/-- An absent key has no item. -/
theorem absK_none (m : MSt GoString GoString) (k : GoString) (hx : m.kv k = none) :
    (absK dec pfx m).items k = none := by
  simp [absK, hx]

/-- A key's item's resource version determines its mod revision (both below `2^63`). -/
theorem mod_eq_of_rv (x : VR GoString) (r : Nat) (hr : r < 2 ^ 63) :
    x.mod = W64 (r : Int) ↔ uint.nat x.mod = r := by
  constructor
  · intro h; rw [h]; exact uint_nat_W64 r hr
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := uint_nat_W64 r hr
    simp only [uint.nat] at h this
    rw [h, this]

/-- **`Create`'s transaction is the model's `create`** (`OptimisticPut(key, data, 0)` of an
object with no resource version): it succeeds exactly when the key is absent, and then the
model state is `create`'s; if it fails, the key exists, nothing changed, and the model answers
that it exists. -/
theorem absK_create (ks : List GoString) (m : MSt GoString GoString) (hwf : KWf dec pfx m)
    (k v : GoString) (o : Obj) (hk : pfx <+: k) (hv : dec v = some (o, true)) :
    let p := mStep ks (putTxn k v (W64 0) false) m
    absK dec pfx p.1 = ((absK dec pfx m).create (E := E) k o 0).1 ∧
      (match p.2 with
        | .txn r true _ => ((absK dec pfx m).create (E := E) k o 0).2 = .obj o r
        | .txn _ false _ => ((absK dec pfx m).create (E := E) k o 0).2 = .err (.keyExists k)
        | _ => False) := by
  intro p
  have hp : p = mStep ks (putTxn k v (W64 0) false) m := rfl
  rw [mStep_putTxn] at hp
  cases hx : m.kv k with
  | none =>
    have hm : modOf m.kv k = W64 0 := by simp [modOf, hx]
    simp only [hm, ↓reduceIte] at hp
    rw [hp]
    have hn := absK_none dec pfx m k hx
    simp only [KSt.create, ne_eq, not_true_eq_false, ↓reduceIte, hn]
    exact ⟨absK_put dec pfx m hwf k v o hk hv, rfl⟩
  | some x =>
    have hpos := hwf.2.1
    have hx0 := (hpos k x hx).1
    have hm : modOf m.kv k ≠ W64 0 := by
      simp only [modOf, hx, Option.map_some, Option.getD_some]
      intro h; rw [h] at hx0; simp [uint.nat] at hx0
    simp only [hm, ↓reduceIte, Bool.false_eq_true] at hp
    rw [hp]
    obtain ⟨it, hit, -⟩ := absK_some dec pfx m hwf k hk x hx
    simp only [KSt.create, ne_eq, not_true_eq_false, ↓reduceIte, hit]
    constructor <;> first | rfl | trivial

/-- A delete transaction on an absent key: nothing changes (its comparison of a nonzero `rev`
fails), and the else branch gets nothing. -/
theorem mStep_delTxn_none (ks : List GoString) (m : MSt GoString GoString) (k : GoString)
    (rev : w64) (g : Bool) (hx : m.kv k = none) (hr : rev ≠ W64 0) :
    mStep ks (delTxn k rev g) m = (m, .txn m.rev false (if g then [.get none] else [])) := by
  have hmod : modOf m.kv k = W64 0 := by simp [modOf, hx]
  unfold delTxn
  simp only [mStep, holds_mod, hmod]
  have hne : ¬ (0#64 = rev) := fun h => hr (by rw [← h]; rfl)
  cases g <;> simp [hne, runOps, MOp.run, hx]

/-- **`deleteOnce`'s transaction at the item's resource version is the model's `delete`**
(`OptimisticDelete(key, r, GetOnFailure)` after the preconditions and `validateDeletion` passed
on the stored object): the item goes at the next revision, answered with the object there. -/
theorem absK_delete (ks : List GoString) (m : MSt GoString GoString) (k : GoString)
    (hk : pfx <+: k) (x : VR GoString) (hx : m.kv k = some x) (o : Obj) (c : Bool)
    (hd : dec x.val = some (o, c)) (r : Nat) (hr : r < 2 ^ 63) (hm : x.mod = W64 (r : Int))
    (pre validate : Obj → Nat → Option E) (hpre : pre o r = none) (hval : validate o r = none) :
    let p := mStep ks (delTxn k (W64 (r : Int)) true) m
    p = (⟨m.kv.del k, m.rev + 1⟩, .txn (m.rev + 1) true [.del 1]) ∧
      absK dec pfx p.1 = ((absK dec pfx m).delete k pre validate).1 ∧
      ((absK dec pfx m).delete k pre validate).2 = .obj o (m.rev + 1) := by
  intro p
  have hp : p = _ := mStep_delTxn ks m k (W64 (r : Int)) true x hx
  simp only [hm, ↓reduceIte] at hp
  have hrv : uint.nat x.mod = r := (mod_eq_of_rv x r hr).1 hm
  have hit : (absK dec pfx m).items k = some ⟨o, r, c⟩ := by
    simp [absK, hk, hx, itemOf, hd, hrv]
  refine ⟨hp, ?_, ?_⟩
  · rw [hp]
    simp only [KSt.delete, hit, hpre, hval]
    exact absK_del dec pfx m k
  · simp only [KSt.delete, hit, hpre, hval]
    rfl

/-- A transaction whose comparison fails (a conflict: the key's mod revision is not the
attempt's) changes nothing: the store then retries from the current key-value its else branch
got. -/
theorem mStep_putTxn_conflict (ks : List GoString) (m : MSt GoString GoString) (k v : GoString)
    (rev : w64) (h : modOf m.kv k ≠ rev) :
    mStep ks (putTxn k v rev true) m = (m, .txn m.rev false [.get (m.kv k)]) := by
  rw [mStep_putTxn]; simp [h]

/-- **`updateOnce`'s transaction at the item's resource version is the model's `update`**, when
the store writes (`OptimisticPut(key, data, r, GetOnFailure)`): `tryUpdate` gave `o'` on the
stored object, whose new value `v` reads as `o'` (canonical), and the store did not skip the
write (`hw`: not both unchanged and canonical, `store.go:547`). -/
theorem absK_update (ks : List GoString) (m : MSt GoString GoString) (hwf : KWf dec pfx m)
    (k : GoString) (hk : pfx <+: k) (x : VR GoString) (hx : m.kv k = some x) (o : Obj) (c : Bool)
    (hd : dec x.val = some (o, c)) (r : Nat) (hr : r < 2 ^ 63) (hm : x.mod = W64 (r : Int)) (ign : Bool) (z : Obj)
    (pre : Obj → Nat → Option E) (f : Obj → Nat → Except E Obj) (hpre : pre o r = none)
    (o' : Obj) (hf : f o r = .ok o') (v : GoString) (hv : dec v = some (o', true))
    (hw : ¬ (o' = o ∧ c = true)) :
    let p := mStep ks (putTxn k v (W64 (r : Int)) true) m
    p = (⟨m.kv.put (m.rev + 1) k v, m.rev + 1⟩, .txn (m.rev + 1) true [.put]) ∧
      absK dec pfx p.1 = ((absK dec pfx m).update k ign z pre f).1 ∧
      ((absK dec pfx m).update k ign z pre f).2 = .obj o' (m.rev + 1) := by
  intro p
  have hmod : modOf m.kv k = W64 (r : Int) := by simp [modOf, hx, hm]
  have hp : p = _ := mStep_putTxn ks m k v (W64 (r : Int)) true
  simp only [hmod, ↓reduceIte] at hp
  have hrv : uint.nat x.mod = r := (mod_eq_of_rv x r hr).1 hm
  have hit : (absK dec pfx m).items k = some ⟨o, r, c⟩ := by
    simp [absK, hk, hx, itemOf, hd, hrv]
  have hw' : ¬ (o' = o ∧ c = true) := hw
  refine ⟨hp, ?_, ?_⟩
  · rw [hp]
    simp only [KSt.update, KSt.current, hit, hpre, hf, hw', ↓reduceIte]
    exact absK_put dec pfx m hwf k v o' hk hv
  · simp only [KSt.update, KSt.current, hit, hpre, hf, hw', ↓reduceIte]
    simp [absK]

/-- **The no-op update answers the item as it is** (no transaction: a read linearizes it, D30h):
`tryUpdate` left the object unchanged and the item is canonical. -/
theorem update_noop (s : KSt Obj) (k : GoString) (it : KItem Obj) (hit : s.items k = some it)
    (ign : Bool) (z : Obj) (pre : Obj → Nat → Option E) (f : Obj → Nat → Except E Obj)
    (hpre : pre it.obj it.rv = none) (hf : f it.obj it.rv = .ok it.obj) (hc : it.canon = true) :
    s.update k ign z pre f = (s, .obj it.obj it.rv) := by
  simp [KSt.update, KSt.current, hit, hpre, hf, hc]

end abs

end k8s
end EtcdGrove
end Perennial
