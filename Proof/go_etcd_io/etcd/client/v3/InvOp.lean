/-
The vocabulary of the `clientv3` functions translated for etcd's cache
(`client/v3/op.go`): the `Op` getters' model, `GetPrefixRangeEnd`, and how a `Get`'s `Op` is
built from its options (`OpGet`, `NewOp`, `applyOpts`, `IsOptsWithPrefix`/`FromKey`, the
`With*` options). Lean-first (no Rocq counterpart).

**`Op` models.** `OpModel` is what the cache reads of an `Op` through its getters and `opAt op o`
relates them (moved from `InvCache.lean`). `OpFull` adds the fields an option can change and
etcd's `KV.Get` reads that the getters do not (the operation type `t`, the key, `keysOnly`, and
the two flags `OpGet`'s check reads, and the lease `OpWatch`'s check reads), so that `OpFull` covers every field `Op.toRangeRequest`
sends: `key`, `end`, `rev`, `limit`, `sort` (only whether it is set: the client's statement
in `InvEtcd.lean` asks for none), `serializable`, `keysOnly`, `countOnly` and the four
revision filters. `opFullAt op o` adds them to `opAt` (the key, like the range end, read-only).

**Options.** An `OpOption` is a closure on `*Op`; `optSpec f g` says the closure `f` changes an
`Op` modelled by `o` into one modelled by `g o` (persistent, like `keyPredSpec`), and `optsAt sl
gs` that the read-only slice `sl` holds closures with the transformers `gs`, in order.
`OpGet(key, opts...)` applies them to `Op{t: tRange, key: []byte(key)}` (`opGetModel`), after
checking (by applying them to `NewOp()` twice) that not both `WithPrefix` and `WithFromKey`
were given, which panics (`opGetPanics`). The models of the `With*` options: `withLimitM`,
`withRevM`, `withPrefixM`, `withRangeM`, `withFromKeyM`, `withSerializableM`,
`withCountOnlyM`, and of the watch options `withProgressNotifyM`, `withCreatedNotifyM`.
`OpWatch(key, opts...)` applies them to the same start (`opWatchModel`) and panics if the
result asks for something a watch cannot do (`OpFull.watchPanics`, `opWatchPanics`).

**Puts and deletes** (for `client/v3/concurrency`'s transactions, `InvEtcdTxn.lean`): `OpFull`
also covers what `toRequestOp` sends of them: the value `val`, the sort option's target and
order (`opSortAt`: the `*SortOption`, read-only), `ignoreValue`/`ignoreLease`, and whether
`end` may be non-nil (`rangeEndSet`: `OpPut` panics on a non-nil `end`, which the contents
`rangeEnd` cannot tell). `OpPut(key, val, opts...)` (`opPutModel`, `putPanics`) and
`OpDelete(key, opts...)` (`opDeleteModel`, `opDeletePanics`) apply the options to their starts;
the new options are `withLeaseM`, `withMaxCreateRevM`, `withSortM` and `withTopM`
(`WithFirstCreate`, `WithLastCreate`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-! ## `GetPrefixRangeEnd` -/

/-- `clientv3.GetPrefixRangeEnd(prefix)` (`getPrefix`): drop the trailing `0xff` bytes and
increment the last remaining one; `[0]` ("from key") if every byte is `0xff` (or there is
none). -/
def prefixRangeEnd (p : GoString) : GoString :=
  match p.reverse.dropWhile (fun b => b == W8 255) with
  | [] => [W8 0]
  | b :: r => r.reverse ++ [b + W8 1]

/-- `getPrefix`'s loop finds a byte below `0xff` at `i`, with only `0xff` after it. -/
theorem prefixRangeEnd_of_lt (p : GoString) (i : Nat) (b : w8) (hi : p[i]? = some b)
    (hb : b ≠ W8 255) (hafter : ∀ j, i < j → ∀ x, p[j]? = some x → x = W8 255) :
    prefixRangeEnd p = p.take i ++ [b + W8 1] := by
  have hlen : i < p.length := by
    rcases Nat.lt_or_ge i p.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have hsplit : p = p.take i ++ b :: p.drop (i + 1) := by
    have := List.take_append_drop i p
    rw [List.drop_eq_getElem_cons hlen] at this
    rw [List.getElem?_eq_getElem hlen] at hi
    cases hi
    exact this.symm
  have hff : ∀ x ∈ p.drop (i + 1), x = W8 255 := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    apply hafter (i + 1 + k) (by omega) x
    rw [List.getElem_drop] at hkx
    rw [List.getElem?_eq_getElem (by simp at hk; omega), hkx]
  unfold prefixRangeEnd
  conv => lhs; rw [hsplit]
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    List.dropWhile_append_of_pos (by
      intro x hx
      rw [List.mem_reverse] at hx
      simp [hff x hx])]
  rw [List.dropWhile_cons_of_neg (by simpa using hb)]
  simp

/-- `getPrefix`'s loop finds only `0xff` bytes. -/
theorem prefixRangeEnd_of_all (p : GoString) (hall : ∀ x ∈ p, x = W8 255) :
    prefixRangeEnd p = [W8 0] := by
  have hnil : ∀ l : List w8, (∀ x ∈ l, x = W8 255) →
      l.dropWhile (fun b => b == W8 255) = [] := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.dropWhile_cons_of_pos (by simp [hl x (List.mem_cons_self ..)])]
      exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
  unfold prefixRangeEnd
  rw [hnil _ (fun x hx => hall x (List.mem_reverse.1 hx))]

/-! ## `clientv3.Op`: what the cache reads -/

/-- What the cache reads of a `clientv3.Op` (through its getters). -/
structure OpModel where
  countOnly : Bool
  prevKV : Bool
  /-- `sort != nil` -/
  sortSet : Bool
  limit : w64
  minModRev : w64
  maxModRev : w64
  minCreateRev : w64
  maxCreateRev : w64
  fragment : Bool
  createdNotify : Bool
  filterPut : Bool
  filterDelete : Bool
  /-- the contents of the range end `end` (`RangeBytes()`) -/
  rangeEnd : GoString
  rev : w64
  serializable : Bool
  progressNotify : Bool

/-- `validateGet`'s unsupported options. -/
def OpModel.getUnsupported (o : OpModel) : Bool :=
  decide (o.countOnly = true ∨ o.prevKV = true ∨ o.sortSet = true ∨ o.limit ≠ W64 0 ∨
    o.minModRev ≠ W64 0 ∨ o.maxModRev ≠ W64 0 ∨ o.minCreateRev ≠ W64 0 ∨
    o.maxCreateRev ≠ W64 0)

/-- `validateWatch`'s unsupported options. -/
def OpModel.watchUnsupported (o : OpModel) : Bool :=
  decide (o.prevKV = true ∨ o.fragment = true ∨ o.createdNotify = true ∨ o.filterPut = true ∨
    o.filterDelete = true)

/-- The pure part of `opAt`: the scalar fields. -/
def OpFields [FfiSyntax] (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel) : Prop :=
  op.countOnly' = o.countOnly ∧ op.prevKV' = o.prevKV ∧ (op.sort' ≠ null ↔ o.sortSet = true) ∧
  op.limit' = o.limit ∧ op.minModRev' = o.minModRev ∧ op.maxModRev' = o.maxModRev ∧
  op.minCreateRev' = o.minCreateRev ∧ op.maxCreateRev' = o.maxCreateRev ∧
  op.fragment' = o.fragment ∧ op.createdNotify' = o.createdNotify ∧
  op.filterPut' = o.filterPut ∧ op.filterDelete' = o.filterDelete ∧ op.rev' = o.rev ∧
  op.serializable' = o.serializable ∧ op.progressNotify' = o.progressNotify

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `Op` value `op` is modelled by `o`; its range end is a read-only byte slice. -/
def opAt (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel) : IProp GF :=
  iprop(⌜OpFields op o⌝ ∗ op.end' ↦*□ o.rangeEnd)

instance opAt_persistent (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel) :
    Persistent (opAt (GF := GF) op o) := by
  unfold opAt; infer_instance

end defs


/-! ## `clientv3.Op`: what a `Get` sends -/

/-- An `Op` as etcd's `KV.Get` reads it (`Op.toRangeRequest`), and as the options change it:
the getters' `OpModel`, the operation type, the key, `keysOnly`, `OpGet`'s two flags, and the
lease (`OpWatch` panics on one). -/
structure OpFull where
  base : OpModel
  /-- `t` (`opType`: `tRange` is `1`) -/
  t : w64
  /-- the contents of `key` -/
  key : GoString
  keysOnly : Bool
  /-- `isOptsWithPrefix` -/
  withPrefix : Bool
  /-- `isOptsWithFromKey` -/
  withFromKey : Bool
  /-- `leaseID` (`WithLease`) -/
  leaseID : w64
  /-- the contents of `val` (a put's value) -/
  val : GoString
  /-- `end != nil` may hold (an option set the range end); `false` means `end` is nil
  (`OpPut` panics on a non-nil `end`, which the contents `rangeEnd` cannot tell) -/
  rangeEndSet : Bool
  /-- `sort.Target`, `sort.Order` (meaningful when `base.sortSet`) -/
  sortTarget : w64
  sortOrder : w64
  ignoreValue : Bool
  ignoreLease : Bool

/-- The zero `OpModel` (a zero `Op`). -/
def OpModel.zero : OpModel :=
  { countOnly := false, prevKV := false, sortSet := false, limit := W64 0,
    minModRev := W64 0, maxModRev := W64 0, minCreateRev := W64 0, maxCreateRev := W64 0,
    fragment := false, createdNotify := false, filterPut := false, filterDelete := false,
    rangeEnd := [], rev := W64 0, serializable := false, progressNotify := false }

/-- `NewOp()`: `&Op{key: []byte("")}`. -/
def OpFull.newOp : OpFull :=
  { base := .zero, t := W64 0, key := [], keysOnly := false, withPrefix := false,
    withFromKey := false, leaseID := W64 0, val := [], rangeEndSet := false,
    sortTarget := W64 0, sortOrder := W64 0, ignoreValue := false, ignoreLease := false }

/-- What `OpGet(key, ...)` starts from: `Op{t: tRange, key: []byte(key)}`. -/
def OpFull.getInit (key : GoString) : OpFull := { OpFull.newOp with t := W64 1, key := key }

/-- The options' transformers applied in order (`applyOpts`). -/
def opFold (gs : List (OpFull → OpFull)) (o : OpFull) : OpFull := gs.foldl (fun o g => g o) o

/-- The `Op` `OpGet(key, opts...)` returns, for options with transformers `gs`. -/
def opGetModel (key : GoString) (gs : List (OpFull → OpFull)) : OpFull :=
  opFold gs (OpFull.getInit key)

/-- `OpGet` panics: the options set both `WithPrefix` and `WithFromKey` (`IsOptsWithPrefix`,
`IsOptsWithFromKey`, which apply them to `NewOp()`). -/
def opGetPanics (gs : List (OpFull → OpFull)) : Prop :=
  (opFold gs .newOp).withPrefix = true ∧ (opFold gs .newOp).withFromKey = true

/-- The `Op` `OpWatch(key, opts...)` returns, for options with transformers `gs`: the same as
`OpGet`'s (`Op{t: tRange, key: []byte(key)}` with the options applied). -/
def opWatchModel (key : GoString) (gs : List (OpFull → OpFull)) : OpFull :=
  opFold gs (OpFull.getInit key)

/-- `OpWatch`'s `switch`: the `Op` has a lease, a limit, a sort order, is serializable or
count-only, or has a revision filter. -/
def OpFull.watchPanics (o : OpFull) : Prop :=
  o.leaseID ≠ W64 0 ∨ o.base.limit ≠ W64 0 ∨ o.base.sortSet = true ∨
    o.base.serializable = true ∨ o.base.countOnly = true ∨
    o.base.minModRev ≠ W64 0 ∨ o.base.maxModRev ≠ W64 0 ∨
    o.base.minCreateRev ≠ W64 0 ∨ o.base.maxCreateRev ≠ W64 0

/-- `OpWatch(key, opts...)` panics: the options (applied to its start) set one of the fields
its `switch` rules out. -/
def opWatchPanics (key : GoString) (gs : List (OpFull → OpFull)) : Prop :=
  (opWatchModel key gs).watchPanics

/-- `WithLimit(n)` -/
def withLimitM (n : w64) (o : OpFull) : OpFull := { o with base := { o.base with limit := n } }
/-- `WithRev(rev)` -/
def withRevM (rev : w64) (o : OpFull) : OpFull := { o with base := { o.base with rev := rev } }
/-- `WithSerializable()` -/
def withSerializableM (o : OpFull) : OpFull :=
  { o with base := { o.base with serializable := true } }
/-- `WithCountOnly()` -/
def withCountOnlyM (o : OpFull) : OpFull := { o with base := { o.base with countOnly := true } }
/-- `WithProgressNotify()` -/
def withProgressNotifyM (o : OpFull) : OpFull :=
  { o with base := { o.base with progressNotify := true } }
/-- `WithCreatedNotify()` -/
def withCreatedNotifyM (o : OpFull) : OpFull :=
  { o with base := { o.base with createdNotify := true } }
/-- `WithRange(endKey)` -/
def withRangeM (endKey : GoString) (o : OpFull) : OpFull :=
  { o with base := { o.base with rangeEnd := endKey }, rangeEndSet := true }
/-- `WithFromKey()`: from `key` on (`"\x00"` for an empty key). -/
def withFromKeyM (o : OpFull) : OpFull :=
  { o with key := (if o.key = [] then [W8 0] else o.key),
           base := { o.base with rangeEnd := [W8 0] }, withFromKey := true, rangeEndSet := true }
/-- `WithPrefix()`: the keys with prefix `key` (every key, from `"\x00"`, for an empty key). -/
def withPrefixM (o : OpFull) : OpFull :=
  if o.key = [] then
    { o with key := [W8 0], base := { o.base with rangeEnd := [W8 0] }, withPrefix := true,
             rangeEndSet := true }
  else { o with base := { o.base with rangeEnd := prefixRangeEnd o.key }, withPrefix := true,
                rangeEndSet := true }
/-- `WithLease(id)` -/
def withLeaseM (id : w64) (o : OpFull) : OpFull := { o with leaseID := id }
/-- `WithMaxCreateRev(rev)` -/
def withMaxCreateRevM (rev : w64) (o : OpFull) : OpFull :=
  { o with base := { o.base with maxCreateRev := rev } }
/-- `WithMaxModRev(rev)` -/
def withMaxModRevM (rev : w64) (o : OpFull) : OpFull :=
  { o with base := { o.base with maxModRev := rev } }
/-- `WithMinModRev(rev)` -/
def withMinModRevM (rev : w64) (o : OpFull) : OpFull :=
  { o with base := { o.base with minModRev := rev } }
/-- `WithSort(target, order)`: a sort by key in ascending order is no sort (`SortNone`), since
etcd returns keys in that order anyway. -/
def withSortM (target order : w64) (o : OpFull) : OpFull :=
  { o with base := { o.base with sortSet := true }, sortTarget := target,
           sortOrder := (if target = W64 0 ∧ order = W64 1 then W64 0 else order) }
/-- `withTop(target, order)` (`WithFirstCreate()`, `WithLastCreate()`, ...): the options
`WithPrefix(), WithSort(target, order), WithLimit(1)`. -/
def withTopM (target order : w64) : List (OpFull → OpFull) :=
  [withPrefixM, withSortM target order, withLimitM (W64 1)]

/-- `WithKeysOnly()` -/
def withKeysOnlyM (o : OpFull) : OpFull := { o with keysOnly := true }
/-- `WithIgnoreLease()` -/
def withIgnoreLeaseM (o : OpFull) : OpFull := { o with ignoreLease := true }
/-- `OpTxn(cmps, thenOps, elseOps)`'s `Op` (`Op{t: tTxn, cmps, thenOps, elseOps}`): no key, no
value, no option (the lists are `OpT`'s, `InvEtcdTxnOwn.lean`). -/
def OpFull.txnInit : OpFull := { OpFull.newOp with t := W64 4 }

/-! ### `OpPut`, `OpDelete` -/

/-- What `OpPut(key, val, ...)` starts from: `Op{t: tPut, key: []byte(key), val: []byte(val)}`. -/
def OpFull.putInit (key val : GoString) : OpFull :=
  { OpFull.newOp with t := W64 2, key := key, val := val }

/-- The `Op` `OpPut(key, val, opts...)` returns, for options with transformers `gs`. -/
def opPutModel (key val : GoString) (gs : List (OpFull → OpFull)) : OpFull :=
  opFold gs (OpFull.putInit key val)

/-- `OpPut`'s `switch` may panic: an option set a range end (`rangeEndSet`: conservative, since
the model keeps the contents of `end`, not whether it is nil), a limit, a revision, a sort, made
it serializable or count-only, set a revision filter, an event filter or `createdNotify`. -/
def OpFull.putPanics (o : OpFull) : Prop :=
  o.rangeEndSet = true ∨ o.base.limit ≠ W64 0 ∨ o.base.rev ≠ W64 0 ∨ o.base.sortSet = true ∨
    o.base.serializable = true ∨ o.base.countOnly = true ∨
    o.base.minModRev ≠ W64 0 ∨ o.base.maxModRev ≠ W64 0 ∨
    o.base.minCreateRev ≠ W64 0 ∨ o.base.maxCreateRev ≠ W64 0 ∨
    o.base.filterDelete = true ∨ o.base.filterPut = true ∨ o.base.createdNotify = true

/-- What `OpDelete(key, ...)` starts from: `Op{t: tDeleteRange, key: []byte(key)}`. -/
def OpFull.deleteInit (key : GoString) : OpFull := { OpFull.newOp with t := W64 3, key := key }

/-- The `Op` `OpDelete(key, opts...)` returns, for options with transformers `gs`. -/
def opDeleteModel (key : GoString) (gs : List (OpFull → OpFull)) : OpFull :=
  opFold gs (OpFull.deleteInit key)

/-- `OpDelete`'s `switch` panics: a lease, a limit, a revision, a sort, serializable,
count-only, a revision filter, an event filter or `createdNotify`. -/
def OpFull.deletePanics (o : OpFull) : Prop :=
  o.leaseID ≠ W64 0 ∨ o.base.limit ≠ W64 0 ∨ o.base.rev ≠ W64 0 ∨ o.base.sortSet = true ∨
    o.base.serializable = true ∨ o.base.countOnly = true ∨
    o.base.minModRev ≠ W64 0 ∨ o.base.maxModRev ≠ W64 0 ∨
    o.base.minCreateRev ≠ W64 0 ∨ o.base.maxCreateRev ≠ W64 0 ∨
    o.base.filterDelete = true ∨ o.base.filterPut = true ∨ o.base.createdNotify = true

/-- `OpDelete(key, opts...)` panics: both `WithPrefix` and `WithFromKey` (as `OpGet`), or the
`switch`. -/
def opDeletePanics (key : GoString) (gs : List (OpFull → OpFull)) : Prop :=
  opGetPanics gs ∨ (opDeleteModel key gs).deletePanics

section opdefs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The sort option `p` (`op.sort`) holds, for good, `o`'s sort target and order, if set. -/
def opSortAt (p : Loc) (o : OpFull) : IProp GF :=
  if o.base.sortSet then
    iprop(p ↦□ ({ Target' := o.sortTarget, Order' := o.sortOrder } :
      go_etcd_io.etcd.client.v3.SortOption))
  else iprop(True)

instance opSortAt_persistent (p : Loc) (o : OpFull) : Persistent (opSortAt (GF := GF) p o) := by
  unfold opSortAt; split <;> infer_instance

/-- The `Op` value `op` is modelled by `o` (`opAt` and the other fields `OpFull` covers; the
key and the value are read-only byte slices, the sort option read-only). -/
def opFullAt (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull) : IProp GF :=
  iprop(opAt op o.base ∗ op.key' ↦*□ o.key ∗
    ⌜op.t' = o.t ∧ op.keysOnly' = o.keysOnly ∧ op.isOptsWithPrefix' = o.withPrefix ∧
      op.isOptsWithFromKey' = o.withFromKey ∧ op.leaseID' = o.leaseID ∧
      op.ignoreValue' = o.ignoreValue ∧ op.ignoreLease' = o.ignoreLease ∧
      (o.rangeEndSet = false → op.end' = slice.nil)⌝ ∗
    op.val' ↦*□ o.val ∗ opSortAt op.sort' o)

instance opFullAt_persistent (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull) :
    Persistent (opFullAt (GF := GF) op o) := by
  unfold opFullAt; infer_instance

/-- The `OpOption` closure `f` changes an `Op` modelled by `o` into one modelled by `g o`. -/
def optSpec (f : GoFunc) (g : OpFull → OpFull) : IProp GF :=
  iprop(□ ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
    {{ opp ↦ op ∗ opFullAt op o }} (App (Val #f) (Val #opp))
    {{ (op' : go_etcd_io.etcd.client.v3.Op), RET #(); opp ↦ op' ∗ opFullAt op' (g o) }})

instance optSpec_persistent (f : GoFunc) (g : OpFull → OpFull) :
    Persistent (optSpec (GF := GF) f g) := by
  unfold optSpec; infer_instance

/-- The `[]OpOption` slice `sl` (read-only) holds closures with the transformers `gs`. -/
def optsAt (sl : GoSlice) (gs : List (OpFull → OpFull)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : OpFull → OpFull), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      optSpec f g)

instance optsAt_persistent (sl : GoSlice) (gs : List (OpFull → OpFull)) :
    Persistent (optsAt (GF := GF) sl gs) := by
  unfold optsAt; infer_instance

/-- **An `OpOption` closure that needs a resource** `R` (and gives it back): `f` changes an `Op`
modelled by `o` into one modelled by `g o`. For a closure that writes a variable it captured
(`WithSort(SortByKey, SortAscend)` rewrites its `order` to `SortNone`): a client calls an
`OpOption` slice's closures one at a time, in the caller's goroutine, so `R` (the variable)
passes from call to call; `optSpec` is the case without (`optSpec_res`).
`client/v3/experimental/recipes`' addition (`WithFirstKey`). -/
def optSpecRes (f : GoFunc) (g : OpFull → OpFull) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
    {{ R ∗ opp ↦ op ∗ opFullAt op o }} (App (Val #f) (Val #opp))
    {{ (op' : go_etcd_io.etcd.client.v3.Op), RET #(); R ∗ opp ↦ op' ∗ opFullAt op' (g o) }})

instance optSpecRes_persistent (f : GoFunc) (g : OpFull → OpFull) (R : IProp GF) :
    Persistent (optSpecRes f g R) := by
  unfold optSpecRes; infer_instance

/-- The `[]OpOption` slice `sl` (read-only) holds closures with the transformers `gs`, each needing
the resource `R` (`optSpecRes`). -/
def optsAtRes (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : OpFull → OpFull), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      optSpecRes f g R)

instance optsAtRes_persistent (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF) :
    Persistent (optsAtRes sl gs R) := by
  unfold optsAtRes; infer_instance

end opdefs


/-! ## Lemmas about the option models -/

theorem opFold_take_succ (gs : List (OpFull → OpFull)) (o : OpFull) (n : Nat)
    (g : OpFull → OpFull) (h : gs[n]? = some g) :
    opFold (gs.take (n + 1)) o = g (opFold (gs.take n) o) := by
  unfold opFold
  rw [List.take_add_one, h]
  simp

end EtcdGrove
end Perennial
