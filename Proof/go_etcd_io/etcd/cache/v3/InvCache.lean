/-
etcd's cache `Cache` (`cache/cache.go`, `cache/predicate.go`): the vocabulary of the
request-side helpers' specs (`Spec/{ExactKey,FromKey,Range,KeyPredForRange}.lean`,
`Spec/Cache__validate*.lean`, `Spec/Cache__{Ready,WaitReady,RequestProgress}.lean`) and of
the `clientv3` functions they call (`Spec/Op__*.lean`, `Spec/GetPrefixRangeEnd.lean`,
`Spec/getPrefix.lean`). Lean-first (no Rocq counterpart).

**Keys.** A Go `[]byte` key is modelled by its contents, a `GoString` (`List w8`, as Go's
`string([]byte)` conversion is): `sl ↦*{dq} k`. `bytes.Equal`/`bytes.Compare` are Go's `==`
and `<` on the strings (`bytes.wp_Equal`, `bytes.wp_Compare`), so a key predicate is a
function `GoString → Bool` in terms of `go.GoStringLt`, the order of the store's maps
(`InvStore.lean`). `keyPredForRange start end` is the predicate `KeyPredForRange` builds;
it is `kvRange`'s membership test (`mem_kvRange`), so `Get`'s range and `Watch`'s filter
select the same keys.

**Ranges.** `validRange prefix start end` is `Cache.validateRange`: the range must lie
within the cache's prefix (`prefixRangeEnd`, `clientv3.GetPrefixRangeEnd`, is the least key
above every key with the prefix; `[0]` if there is none).

**`clientv3.Op`.** An `Op` is a struct value; `OpModel` is what the cache's helpers read of
it through its getters, `opAt op o` relates them (the range end is a read-only byte slice).

**The `Cache`'s fields.** `isCacheFields c cf γr γd cap` is a *partial* predicate: the
fields `prefix`, `cfg`, `ready` and `demux`, read-only, with `ready`'s and `demux`'s
persistent predicates. The `Cache` stage extends it (store, watcher, wait group, ...).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux
public import Proof.go_etcd_io.etcd.cache.v3.InvReady

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-! ## Key predicates -/

/-- `ExactKey(key)`: `k == key`. -/
def exactKeyPred (key : GoString) (k : GoString) : Bool := decide (k = key)

/-- `FromKey(start)`: `k >= start`. -/
def fromKeyPred (start : GoString) (k : GoString) : Bool := !decide (go.GoStringLt k start)

/-- `Range(start, end)`: `start <= k < end`. -/
def rangePred (start end_ : GoString) (k : GoString) : Bool :=
  !decide (go.GoStringLt k start) && decide (go.GoStringLt k end_)

/-- `KeyPredForRange(start, end)`: the key `start` alone if `end` is empty, the keys from
`start` on if `end` is `"\x00"`, the keys in `[start, end)` otherwise. -/
def keyPredForRange (start end_ : GoString) : GoString → Bool :=
  if end_ = [] then exactKeyPred start
  else if end_ = [W8 0] then fromKeyPred start
  else rangePred start end_

/-- `kvRange` (`snapshot.Range`, the store's `Get`) filters by `keyPredForRange`. -/
theorem kvRange_eq_filter (start end_ : GoString) (m : KvMap) :
    kvRange start end_ m = m.filter (fun e => keyPredForRange start end_ e.1) := by
  unfold kvRange keyPredForRange exactKeyPred fromKeyPred rangePred
  split <;> (try split) <;> rfl

/-- An entry is in `kvRange start end m` iff it is in `m` and its key satisfies
`keyPredForRange start end`. -/
theorem mem_kvRange (start end_ : GoString) (m : KvMap) (e : KvEntry) :
    e ∈ kvRange start end_ m ↔ e ∈ m ∧ keyPredForRange start end_ e.1 = true := by
  rw [kvRange_eq_filter, List.mem_filter]

/-! ## `bytes.Compare` -/

theorem goStringLt_asymm {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => goStringLt_irrefl a (goStringLt_trans h h')

theorem compareResult_lt (a b : GoString) :
    sint.Z (bytes.compareResult a b) < 0 ↔ go.GoStringLt a b := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, iff_true]; decide
  · simp only [h, ↓reduceIte, iff_false]
    split <;> decide

theorem compareResult_ge (a b : GoString) :
    0 ≤ sint.Z (bytes.compareResult a b) ↔ ¬ go.GoStringLt a b := by
  rw [← compareResult_lt]; omega

theorem compareResult_gt (a b : GoString) :
    0 < sint.Z (bytes.compareResult a b) ↔ go.GoStringLt b a := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_asymm h)⟩
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · subst he; simp only [↓reduceIte]
      exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_irrefl a)⟩
    · simp only [he, ↓reduceIte]
      refine ⟨fun _ => ?_, fun _ => by decide⟩
      exact Classical.byContradiction fun h' => he (goStringLt_eq_of_not_lt h h')

theorem compareResult_le (a b : GoString) :
    sint.Z (bytes.compareResult a b) ≤ 0 ↔ ¬ go.GoStringLt b a := by
  rw [← compareResult_gt]; omega

/-! ## Ranges -/

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

/-- `Cache.validateRange(start, end)` on a cache with prefix `pfx`: a single key (`end`
empty) must be in the prefix's range `[pfx, prefixRangeEnd pfx)`; a "from key" range (`end`
is `"\x00"`) needs the root cache (`pfx` empty); a range `[start, end)` must be non-empty and
within `[pfx, prefixRangeEnd pfx]`. The root cache accepts every key and every non-empty
range. -/
def validRange (pfx start end_ : GoString) : Bool :=
  if end_ = [] then
    decide (pfx = []) ||
      (!decide (go.GoStringLt start pfx) && decide (go.GoStringLt start (prefixRangeEnd pfx)))
  else if end_ = [W8 0] then decide (pfx = [])
  else
    decide (go.GoStringLt start end_) &&
      (decide (pfx = []) ||
        (!decide (go.GoStringLt start pfx) && !decide (go.GoStringLt (prefixRangeEnd pfx) end_)))

/-! ## `clientv3.Op` -/

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

/-! ## The `Cache`'s fields -/

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&c.prefix` -/
abbrev cachePrefixAddr (c : Loc) : Loc := structFieldRef Cache go!"prefix" c
/-- `&c.cfg` -/
abbrev cacheCfgAddr (c : Loc) : Loc := structFieldRef Cache go!"cfg" c
/-- `&c.ready` -/
abbrev cacheReadyAddr (c : Loc) : Loc := structFieldRef Cache go!"ready" c
/-- `&c.demux` -/
abbrev cacheDemuxAddr (c : Loc) : Loc := structFieldRef Cache go!"demux" c

end addrs

/-- The values of the `Cache` fields `isCacheFields` covers (fixed by `newCache`). -/
structure CacheFields [FfiSyntax] where
  pfx : GoString
  cfg : Config
  ready : Loc
  demux : Loc

section cache
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- Part of the `Cache` predicate (persistent): `prefix`, `cfg`, `ready` and `demux` point
for good to `cf`'s values, `cf.ready` is a `ready` (ghost names `γr`) and `cf.demux` a demux
(ghost names `γd`, history capacity `cap`). The `Cache` stage extends it with the other
fields. -/
def isCacheFields (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames)
    (cap : Nat) : IProp GF :=
  iprop("#Hprefix" ∷ cachePrefixAddr c ↦□ cf.pfx ∗
    "#Hcfg" ∷ cacheCfgAddr c ↦□ cf.cfg ∗
    "#Hready" ∷ cacheReadyAddr c ↦□ cf.ready ∗
    "#Hdemux" ∷ cacheDemuxAddr c ↦□ cf.demux ∗
    "#HisReady" ∷ isReady cf.ready γr ∗
    "#HisDemux" ∷ isDemux cf.demux γd cap)

instance isCacheFields_persistent (c : Loc) (cf : CacheFields) (γr : ReadyNames)
    (γd : DemuxNames) (cap : Nat) : Persistent (isCacheFields (GF := GF) c cf γr γd cap) := by
  unfold isCacheFields; infer_instance

/-- What `validateRange` returns: `nil` for a `validRange`, else the value of
`ErrKeyRangeInvalid`. -/
def rangeErr (pfx start end_ : GoString) (err : GoInterface) : IProp GF :=
  if validRange pfx start end_ then iprop(⌜err = GoInterface.nil⌝)
  else iprop(globalAddr ErrKeyRangeInvalid ↦□ err)

instance rangeErr_persistent (pfx start end_ : GoString) (err : GoInterface) :
    Persistent (rangeErr (GF := GF) pfx start end_ err) := by
  unfold rangeErr; split <;> infer_instance

/-- What `validateGet`/`validateWatch` return, for a request on `key` with range end
`rangeEnd` on a cache with prefix `pfx`: a non-nil error (`fmt.Errorf` wrapping
`ErrUnsupportedRequest`; the wrapping is not modelled) and no predicate if `unsupported`;
otherwise the value of `ErrKeyRangeInvalid` and no predicate if the range is not
`validRange`; otherwise `nil` and the `KeyPredForRange` closure. -/
def validateResult (unsupported : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : IProp GF :=
  if unsupported then iprop(⌜f = func.nil ∧ ∃ e, err = GoInterface.ok e⌝)
  else if validRange pfx key rangeEnd then
    iprop(⌜err = GoInterface.nil ∧ f ≠ func.nil⌝ ∗ keyPredSpec f (keyPredForRange key rangeEnd))
  else iprop(⌜f = func.nil⌝ ∗ globalAddr ErrKeyRangeInvalid ↦□ err)

instance validateResult_persistent (u : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : Persistent (validateResult (GF := GF) u pfx key rangeEnd f err) := by
  unfold validateResult; split
  · infer_instance
  · split <;> infer_instance

end cache

end EtcdGrove
end Perennial
