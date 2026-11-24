/-
Lean-first (no Rocq counterpart).

# Kubernetes' checker's `Model`, as pure functions (k8s 7g step 2, `notes/k8s-7g-scope.md` §5)

`examples/k8s/etcd3/correctness/model.go` (upstream's `correctness.Model`, plus the D30g patch) on
the requests the driver makes (`realRequest(in)`, `realcheck.go`: the input `x : Input` itself
names the request) and on the values the driver's store returns. Each function below is what one
Go function computes, as its spec (step 3) will state it:

- `RM`: a `*Model`'s contents: `Items` (the store keys to the objects), `ResourceVersion`,
  `Prefix` and (D30g) `NeedsRewrite`. `CompactResourceVersion` is always `0` (no compactions: the
  checker's `compact` is not translated), and `NewFunc`, `NewListFunc`, `Versioner` are the
  driver's (`newObj`, `newObjList`, `versioner{}`), so they are not recorded.
- `RResp`: a `Response`, as `reflect.DeepEqual` reads it: the object's deep value
  (`k8sDeep.DeepV`, the vocabulary of `reflect.DeepEqual.spec_k8s`) and the error's (`RErr`):
  a deep value, storage's too-large error (an `*apierrors.StatusError`, which has no `DeepV`), or
  an error that only requests outside the driver's reach produce (`other`).
- `RChange`: a `*Change` (the write's key and resource version, the object after and before).
- the operations: `rcreateL`, `rupdateL`, `rdeleteL`, `rgetL`, `rlistL` (with `listConsL`,
  `ListReadConsistency`), `rexecL` (`execute`);
- the read checks: `rvalidateGetL`, `rvalidateListL`, `equalListRespL`, `listRespRVL`,
  `listItemsL`; and `rstepL` (`Step`).

The objects' resource versions: the Model sets them with `SetResourceVersion(FormatUint(rv, 10))`,
which the driver's `Obj.SetResourceVersion` parses (decimal) into the field, and reads them with
the versioner, whose string form `rvStr` `parseRVD` parses back (`parseRVD_rvStr`); the field is
all either sees. The selectors are the driver's (`selOkL`, `predEmptyL`: `predicate(in)`), the
scope test is `keyInScopeL` (the checker's `keyInScope` is the driver's text), the continue token
`encL` (the store and the checker call one `EncodeContinue`).

Branches the driver's requests never reach (a key `PrepareKey` rejects, a resource version that
does not parse, the panics of `list` on selectors, limits and timestamps) answer `RErr.other` or
any value: the specs of step 3 take the request facts that exclude them. `IsTooManyRequests` is
false on every output error here (none has reason `TooManyRequests` or code 429), so `Step`'s
first branch is never taken and is not modeled.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Deep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section go
variable [GooseExts]

deriving instance DecidableEq for k8sDeep.DeepV

/-! ## Values -/

/-- **A `Response.Err`, as the checker reads it**: a deep value (`deep .nil`: no error; a
`*storage.StorageError`; an `errors.New` error); storage's too-large error
(`NewTooLargeResourceVersionError`, an `*apierrors.StatusError` of reason `Timeout`), with whether
its details ask for a retry (`RetryAfterSeconds > 0`: `SuggestsClientDelay`'s answer); or an
error none of the driver's requests produce (`PrepareKey`'s, a resource version that does not
parse, `ListReadConsistency`'s). -/
inductive RErr where
  | deep (d : DeepV)
  | tooLarge (delay : Bool)
  | other
deriving DecidableEq

/-- No error. -/
abbrev RErr.none : RErr := .deep .nil

/-- **A `Response`**: its object's deep value (`.nil`: none) and its error. -/
structure RResp where
  obj : DeepV
  err : RErr
deriving DecidableEq

/-- **A `Change`**: the key, the resource version, the object written (`none`: deleted) and the
one before (`none`: created). -/
structure RChange where
  key : GoString
  rv : w64
  obj : Option Obj
  prev : Option Obj
deriving DecidableEq

/-- **A `*Model`'s contents** (see the file header): the items by store key, the resource
version, the prefix of the errors' keys, and the keys the store rewrites on a no-op update
(D30g). -/
structure RM where
  items : GMap GoString Obj
  rv : w64
  pfx : GoString
  rewrites : GMap GoString Bool

/-- `s.NeedsRewrite[key]` (false for a missing key). -/
def needsRewriteL (m : RM) (key : GoString) : Bool := (m.rewrites !! key).getD false

/-- `err != nil`. -/
def errNonNil : RErr → Bool
  | .deep .nil => false
  | _ => true

/-- `storage.IsTooLargeResourceVersion(err)`. -/
def isTooLargeE : RErr → Bool
  | .tooLarge _ => true
  | _ => false

/-- `storage.IsNotFound(err)`: a `*StorageError` of code `ErrCodeKeyNotFound` (1). -/
def isNotFoundE : RErr → Bool
  | .deep (.storageErr c _ _ _) => decide (c = W64 1)
  | _ => false

/-- `apierrors.SuggestsClientDelay(err)`'s boolean: only storage's too-large error, if its
details ask for a retry (its reason is `Timeout`, not `ServerTimeout`); a `*StorageError`, an
`errors.New` error and nil are no `APIStatus`. -/
def delayE : RErr → Bool
  | .tooLarge d => d
  | _ => false

/-- **`reflect.DeepEqual` of two `Response`s**: equal deep values (`reflect.DeepEqual.spec_k8s`,
clause 2). The checker never compares two too-large errors, nor an `other` one; `false` there. -/
def respEqL (a b : RResp) : Bool :=
  match a.err, b.err with
  | .deep ea, .deep eb => decide (a.obj = b.obj ∧ ea = eb)
  | _, _ => false

/-- `min`/`max` of `uint64`s. -/
def wmin (a b : w64) : w64 := if uint.nat a ≤ uint.nat b then a else b
def wmax (a b : w64) : w64 := if uint.nat a ≤ uint.nat b then b else a

/-! ## The items in key order -/

/-- `slices.Sorted(maps.Keys(m))`: the keys of `m`, increasing (`sortedKeysL_spec`; the only such
list, `sortedKeysL_unique`). -/
def sortedKeysL {V : Type} (M : GMap GoString V) : List GoString :=
  M.domList.mergeSort (fun a b => decide (go.GoStringLe a b))

/-- Two strictly increasing lists with the same elements are equal. -/
theorem sorted_unique : ∀ (l1 l2 : List GoString), l1.Pairwise go.GoStringLt →
    l2.Pairwise go.GoStringLt → (∀ k, k ∈ l1 ↔ k ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha := (h a).1 (List.mem_cons_self ..)
      have hb := (h b).2 (List.mem_cons_self ..)
      rcases List.mem_cons.1 ha with e | ha'
      · exact e
      rcases List.mem_cons.1 hb with e | hb'
      · exact e.symm
      exact absurd (h1.1 b hb') (go.goStringLt_asymm (h2.1 a ha'))
    subst hab
    congr 1
    apply sorted_unique t1 t2 h1.2 h2.2
    intro k
    constructor
    · intro hk
      have hk' := (h k).1 (List.mem_cons_of_mem _ hk)
      rcases List.mem_cons.1 hk' with e | e
      · subst e; exact absurd (h1.1 _ hk) (go.goStringLt_irrefl _)
      · exact e
    · intro hk
      have hk' := (h k).2 (List.mem_cons_of_mem _ hk)
      rcases List.mem_cons.1 hk' with e | e
      · subst e; exact absurd (h2.1 _ hk) (go.goStringLt_irrefl _)
      · exact e

theorem goStringLe_trans (a b c : GoString) (h1 : go.GoStringLe a b) (h2 : go.GoStringLe b c) :
    go.GoStringLe a c := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  · exact Or.inr (go.goStringLt_trans h1 h2)

theorem goStringLe_total (a b : GoString) : go.GoStringLe a b ∨ go.GoStringLe b a := by
  by_cases h1 : go.GoStringLt a b
  · exact Or.inl (Or.inr h1)
  by_cases h2 : go.GoStringLt b a
  · exact Or.inr (Or.inr h2)
  exact Or.inl (Or.inl (go.goStringLt_eq_of_not_lt h1 h2))

/-- `sortedKeysL M` holds `M`'s keys, strictly increasing. -/
theorem sortedKeysL_spec {V : Type} (M : GMap GoString V) :
    (∀ k, k ∈ sortedKeysL M ↔ (M !! k).isSome) ∧ (sortedKeysL M).Pairwise go.GoStringLt := by
  have hperm := List.mergeSort_perm M.domList (fun a b => decide (go.GoStringLe a b))
  have hmem : ∀ k, k ∈ sortedKeysL M ↔ (M !! k).isSome := fun k => by
    unfold sortedKeysL; rw [hperm.mem_iff]; exact GMap.mem_dom_list M k
  refine ⟨hmem, ?_⟩
  have hsort : (sortedKeysL M).Pairwise (fun a b => decide (go.GoStringLe a b) = true) :=
    List.pairwise_mergeSort (le := fun a b => decide (go.GoStringLe a b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact goStringLe_trans a b c h1 h2)
      (fun a b => by simpa using goStringLe_total a b) M.domList
  have hnd : (sortedKeysL M).Nodup := hperm.nodup_iff.2 (GMap.nodup_dom_list M)
  rw [List.Nodup] at hnd
  refine (hsort.and hnd).imp ?_
  rintro a b ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  rcases h1 with e | h1
  · exact absurd e h2
  · exact h1

/-- Any strictly increasing list of `M`'s keys is `sortedKeysL M` (`maps.Keys.spec_objMap`'s
`Sorted` result). -/
theorem sortedKeysL_unique {V : Type} (M : GMap GoString V) (ks : List GoString)
    (hm : ∀ k, k ∈ ks ↔ (M !! k).isSome) (hs : ks.Pairwise go.GoStringLt) :
    ks = sortedKeysL M :=
  sorted_unique ks _ hs (sortedKeysL_spec M).2 fun k => by
    rw [hm, (sortedKeysL_spec M).1]

/-- The items of `m`, in key order: `for _, k := range slices.Sorted(maps.Keys(s.Items))` with
`s.Items[k]`. -/
def itemsL (m : RM) : List (GoString × Obj) :=
  (sortedKeysL m.items).filterMap fun k => (m.items !! k).map (k, ·)

/-- The items of `m` a list (or watch) of `key` (recursive if `r`) selects: `keyInScope`. -/
def scopeR (key : GoString) (r : Bool) (m : RM) : List (GoString × Obj) :=
  (itemsL m).filter fun ko => keyInScopeL key r ko.1

/-! ## The operations (`model.go`) -/

/-- `checkKey(key, false)`: `PrepareKey("", key, false)` accepts it. -/
def keyOkL (key : GoString) : Bool := (k8s.prepareKeyM [] key false).isSome

/-- `storage.NewKeyNotFoundError(s.Prefix+key, int64(s.ResourceVersion))`. -/
def notFoundE (m : RM) (key : GoString) : RErr := .deep (.storageErr (W64 1) (m.pfx ++ key) m.rv .nil)

/-- `storage.NewKeyExistsError(s.Prefix+key, 0)`. -/
def existsE (m : RM) (key : GoString) : RErr := .deep (.storageErr (W64 2) (m.pfx ++ key) 0 .nil)

/-- `storage.NewInvalidObjError(s.Prefix+key, msg)`: code `ErrCodeInvalidObj` (4), the inner
error `errors.New(msg)`. -/
def invalidE (m : RM) (key msg : GoString) : RErr :=
  .deep (.storageErr (W64 4) (m.pfx ++ key) 0 (.errString msg))

/-- The callbacks' errors (`errUpdateRejected`, `errDeleteRejected`: `errors.New`). -/
def updRejE : RErr := .deep (.errString go!"k8setcd3: update rejected")
def delRejE : RErr := .deep (.errString go!"k8setcd3: deletion rejected")

/-- `storage.NewTooLargeResourceVersionError(rv, s.ResourceVersion, 0)`: no retry asked. -/
def tooLargeE : RErr := .tooLarge false

/-- **`preconditions(in).Check(key, o)`'s message**, if it fails (`storage/interfaces.go:145`):
the UID first, then the resource version as the versioner's string (`GetResourceVersion`); `%v`
of a string is the string. -/
def checkMsgL (x : Input) (o : Obj) : Option GoString :=
  if x.HasPreUID' && !decide (x.PreUID' = o.UID') then
    some (go!"Precondition failed: UID in precondition: " ++ x.PreUID' ++
      go!", UID in object meta: " ++ o.UID')
  else if x.HasPreRV' && !decide (x.PreRV' = rvStr o.ResourceVersion') then
    some (go!"Precondition failed: ResourceVersion in precondition: " ++ x.PreRV' ++
      go!", ResourceVersion in object meta: " ++ rvStr o.ResourceVersion')
  else none

theorem checkMsgL_none (x : Input) (o : Obj) : checkMsgL x o = none ↔ preOkL x o = true := by
  unfold checkMsgL preOkL
  by_cases h1 : x.HasPreUID' <;> by_cases h2 : x.PreUID' = o.UID' <;>
    by_cases h3 : x.HasPreRV' <;> by_cases h4 : x.PreRV' = rvStr o.ResourceVersion' <;> simp [*]

/-- One operation's result: the response, the next state, the change. -/
abbrev RRes := RResp × RM × Option RChange

/-- A failed operation: the error, the state unchanged, no change. -/
def failR (m : RM) (e : RErr) : RRes := (⟨.nil, e⟩, m, none)

/-- **`create(key, obj)`** on `realRequest(in)`'s object (resource version 0, so
`ErrResourceVersionSetOnCreate` is not reached): "key exists", or the object at the next
resource version. -/
def rcreateL (x : Input) (m : RM) : RRes :=
  let key := storeKeyL x.Key'
  if !keyOkL key then failR m .other
  else if key ∈ m.items then failR m (existsE m key)
  else
    let o : Obj := ⟨(splitKeyL x.Key').1, (splitKeyL x.Key').2, x.UID', x.Val', x.Node', x.App',
      m.rv + W64 1, false⟩
    (⟨.obj o, .none⟩, { m with items := (<[key := o]> m.items), rv := m.rv + W64 1 },
      some ⟨key, m.rv + W64 1, some o, none⟩)

/-- `update`'s write of `u` at the next resource version (D30g: the key's rewrite cleared). -/
def updWriteL (m : RM) (key : GoString) (stored : Option Obj) (u : Obj) : RRes :=
  let o : Obj := { u with ResourceVersion' := m.rv + W64 1 }
  (⟨.obj o, .none⟩,
    { m with
      items := (<[key := o]> m.items), rv := m.rv + W64 1, rewrites := GMap.delete key m.rewrites },
    some ⟨key, m.rv + W64 1, some o, stored⟩)

/-- **`update(key, ignoreNotFound, preconditions, tryUpdate, _)`** with `tryUpdateFor(in)`: "not
found" for a missing key without `IgnoreNotFound`, else from the stored object (or `NewFunc()`'s
zero object): the preconditions, the callback (`updGo`, or its rejection), the no-op shortcut
(D30g: unless the key needs a rewrite; `DeepEqual` of the two objects with their resource versions
cleared) and the write. -/
def rupdateL (x : Input) (m : RM) : RRes :=
  let key := storeKeyL x.Key'
  if !keyOkL key then failR m .other
  else
    let stored := m.items !! key
    if stored.isNone && !x.IgnoreNotFound' then failR m (notFoundE m key)
    else
      let cur := stored.getD zObj
      match checkMsgL x cur with
      | some msg => failR m (invalidE m key msg)
      | none =>
        if rejects x.HasReject' x.Reject' cur.Node' then failR m updRejE
        else
          let u := updGo x cur
          match stored with
          | some s =>
            if !needsRewriteL m key &&
                decide ({ s with ResourceVersion' := 0 } = { u with ResourceVersion' := 0 }) then
              (⟨.obj s, .none⟩, m, none)
            else updWriteL m key stored u
          | none => updWriteL m key stored u

/-- **`delete(ctx, key, preconditions, validateDeletion)`** with `validateFor`: "not found", the
preconditions, the callback, and the delete at the next resource version, answering the object
at it (D30g: the key's rewrite cleared). -/
def rdeleteL (x : Input) (m : RM) : RRes :=
  let key := storeKeyL x.Key'
  if !keyOkL key then failR m .other
  else match m.items !! key with
    | none => failR m (notFoundE m key)
    | some s =>
      match checkMsgL x s with
      | some msg => failR m (invalidE m key msg)
      | none =>
        if rejects x.HasReject' x.Reject' s.Node' then failR m delRejE
        else
          (⟨.obj { s with ResourceVersion' := m.rv + W64 1 }, .none⟩,
            { m with
              items := GMap.delete key m.items, rv := m.rv + W64 1,
              rewrites := GMap.delete key m.rewrites },
            some ⟨key, m.rv + W64 1, none, some s⟩)

/-- **`get(key, opts)`** with `opts` `realRequest(in)`'s (`ResourceVersion` `MinRV`,
`IgnoreNotFound`): too large above the state's resource version, else the stored object, the zero
object (`NewFunc()`, `IgnoreNotFound`) or "not found". -/
def rgetL (x : Input) (m : RM) : RResp :=
  let key := storeKeyL x.Key'
  if !keyOkL key then ⟨.nil, .other⟩
  else match parseRVD x.MinRV' with
    | none => ⟨.nil, .other⟩
    | some rv =>
      if uint.nat m.rv < uint.nat rv then ⟨.nil, tooLargeE⟩
      else match m.items !! key with
        | none => if x.IgnoreNotFound' then ⟨.obj zObj, .none⟩ else ⟨.nil, notFoundE m key⟩
        | some s => ⟨.obj s, .none⟩

/-- A read's consistency (`ReadConsistency`). -/
inductive RCons where
  | consistent
  | exact
  | notOlderThan
deriving DecidableEq

/-- **`ListReadConsistency("", versioner, listOptions(in))`**: no `SendInitialEvents` and no
continue token in a driver's list; none for its errors. The match is `matchOpt(in)`: `Match` 1
`NotOlderThan`, 2 `Exact`, anything else the legacy `""`. -/
def listConsL (x : Input) : Option (RCons × w64) :=
  if x.MinRV' = [] then (if x.Match' = W64 1 ∨ x.Match' = W64 2 then none else some (.consistent, 0))
  else match parseRVD x.MinRV' with
    | none => none
    | some rv =>
      if x.Match' = W64 1 then some (.notOlderThan, rv)
      else if x.Match' = W64 2 then (if rv = 0 then none else some (.exact, rv))
      else if x.Recursive' && decide (0 < sint.Z x.Limit') && decide (rv ≠ 0) then some (.exact, rv)
      else some (.notOlderThan, rv)

/-- **`list(key, opts)`** with `listOptions(in)` (key `ListKey`): too large above the state's
resource version; else the loop on the items in scope (`ListModel.loop`, the driver's: the first
`limit` matches, `total`, `hasMore`), `PrepareContinueToken` (a token and, for an empty
predicate, the remaining count iff more), and the list `NewListFunc()` with `meta.SetList`'s
non-nil items and `UpdateList`'s resource version, token and count. -/
def rlistL (x : Input) (m : RM) : RResp :=
  match k8s.prepareKeyM [] x.ListKey' x.Recursive' with
  | none => ⟨.nil, .other⟩
  | some prepared =>
    match listConsL x with
    | none => ⟨.nil, .other⟩
    | some (_, rv) =>
      if uint.nat m.rv < uint.nat rv then ⟨.nil, tooLargeE⟩
      else
        let s := ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m)
        if s.more then
          let kl := s.last.getD [] ++ [W8 0]
          if encOkL kl prepared then
            ⟨.list (some s.items.reverse) m.rv (encL kl prepared m.rv)
              (if predEmptyL x then some (W64 (s.total : Int) - x.Limit') else none), .none⟩
          else ⟨.nil, .other⟩
        else ⟨.list (some s.items.reverse) m.rv [] none, .none⟩

/-- **`listItems(key, opts)`**: the items in scope the predicate matches, in key order (no
limit). -/
def listItemsL (x : Input) (key : GoString) (m : RM) : List Obj :=
  ((scopeR key x.Recursive' m).filter fun ko => selOkL x ko.2).map Prod.snd

/-- **`execute(realRequest(in))`**: `realRequest`'s kinds (a list for `KList`, a create, delete
or update for theirs, a get for any other). Reads leave the state. -/
def rexecL (x : Input) (m : RM) : RRes :=
  if x.Kind' = W64 4 then (rlistL x m, m, none)
  else if x.Kind' = W64 0 then rcreateL x m
  else if x.Kind' = W64 1 then rdeleteL x m
  else if x.Kind' = W64 2 then rupdateL x m
  else (rgetL x m, m, none)

/-! ## The read checks -/

/-- **`validateGet(opts, expected, output)`**: an expected too-large error asks one of the output;
another expected error but "not found" asks the same response; a consistent read (no
`MinRV`) the same response; a stale one (`NotOlderThan`) a too-large output that asks a retry, a
"not found" at a resource version in `[reqRV, s.RV]` (and positive), or an object no newer than
the state. -/
def rvalidateGetL (x : Input) (m : RM) (exp out : RResp) : Bool :=
  if isTooLargeE exp.err then decide (out.obj = .nil) && isTooLargeE out.err
  else if errNonNil exp.err && !isNotFoundE exp.err then respEqL exp out
  else if errNonNil out.err && decide (out.obj ≠ .nil) then false
  else
    let reqRV := (parseRVD x.MinRV').getD 0
    if x.MinRV' = [] then respEqL exp out
    else if delayE out.err && decide (0 < uint.nat reqRV) && isTooLargeE out.err then true
    else match out.err with
      | .deep (.storageErr c _ r _) =>
        if c = W64 1 then
          decide (0 < uint.nat r ∧ uint.nat reqRV ≤ uint.nat r ∧ uint.nat r ≤ uint.nat m.rv)
        else false
      | .deep .nil =>
        match out.obj with
        | .obj o => decide (uint.nat o.ResourceVersion' ≤ uint.nat m.rv)
        | _ => false
      | _ => false

/-- **An error `reflect.DeepEqual` can compare** (`reflect.DeepEqual.spec_k8s` clause 2): one with a
deep view (no error, a `*StorageError`, an `errors.New` error). -/
def deepErrE : RErr → Prop
  | .deep _ => True
  | _ => False

/-- **An output object `meta.ListAccessor` can take**: nil or a list (`listResponseRV`'s premise:
`ListAccessor`'s spec has no row for the driver's `*Obj` or an error value). -/
def listOrNilD : DeepV → Prop
  | .nil => True
  | .list _ _ _ _ => True
  | _ => False

/-- **`listResponseRV(output)`**: a list output's resource version, if positive (no error, a
non-nil `*ObjList`: `meta.ListAccessor` fails on anything else). -/
def listRespRVL (out : RResp) : Option w64 :=
  if errNonNil out.err then none
  else match out.obj with
    | .list _ rv _ _ => if rv = 0 then none else some rv
    | _ => none

/-- **`validCacherContinue(key, opts, _, outContinue)`**: an output without a token is the
cacher's index-backed answer, allowed when the predicate selects and exactly `limit` items
match. -/
def validCacherContinueL (x : Input) (m : RM) (outC : GoString) : Bool :=
  decide (outC = []) && !predEmptyL x &&
    decide (((listItemsL x x.ListKey' m).length : Int) = sint.Z x.Limit')

/-- **`equalListResponse(key, opts, expected, output)`**: the same response, or, with a limit,
two lists that differ only by the output's missing continue token (`validCacherContinueL`). The
expected list is compared through `DeepCopyObject`'s copy, whose items are never nil (`append([]Obj{},
...)`). -/
def equalListRespL (x : Input) (m : RM) (exp out : RResp) : Bool :=
  respEqL exp out ||
    (decide (0 < sint.Z x.Limit') && !errNonNil exp.err && !errNonNil out.err &&
      match exp.obj, out.obj with
      | .list ei erv ec erem, .list _ _ oc _ =>
        decide (ec ≠ []) && validCacherContinueL x m oc &&
          decide (DeepV.list (some (ei.getD [])) erv oc erem = out.obj)
      | _, _ => false)

/-- **`validateList(key, opts, expected, output)`**: an expected too-large error asks one of the
output; another expected error the same response; else, by `ListReadConsistency`: a too-large
output that asks a retry passes a stale read; a consistent read `equalListRespL`; an exact one a
list at the requested resource version; a `NotOlderThan` one a list in `[reqRV, s.RV]`. -/
def rvalidateListL (x : Input) (m : RM) (exp out : RResp) : Bool :=
  if isTooLargeE exp.err then decide (out.obj = .nil) && isTooLargeE out.err
  else if errNonNil exp.err then respEqL exp out
  else match listConsL x with
    | none => false
    | some (c, reqRV) =>
      if delayE out.err && decide (0 < uint.nat reqRV) && decide (out.obj = .nil) &&
          isTooLargeE out.err then true
      else match c with
        | .consistent => equalListRespL x m exp out
        | .exact => decide (listRespRVL out = some reqRV)
        | .notOlderThan =>
          match listRespRVL out with
          | some r => decide (uint.nat reqRV ≤ uint.nat r ∧ uint.nat r ≤ uint.nat m.rv)
          | none => false

/-- **`Step(realRequest(in), output)`**: a get or a list is checked (`rvalidateGetL`,
`rvalidateListL`) and leaves the state; a write must answer exactly what `execute` answers, and
then moves to its next state with its change. -/
def rstepL (x : Input) (m : RM) (out : RResp) : Bool × RM × Option RChange :=
  if x.Kind' = W64 4 then (rvalidateListL x m (rexecL x m).1 out, m, none)
  else if x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 then
    if respEqL (rexecL x m).1 out then (true, (rexecL x m).2.1, (rexecL x m).2.2)
    else (false, m, none)
  else (rvalidateGetL x m (rexecL x m).1 out, m, none)

/-! ## The initial model -/

/-- A map of a list has at most its length's keys. -/
theorem size_ofList_le {V : Type} (l : List (GoString × V)) : GMap.size (GMap.ofList l) ≤ l.length := by
  induction l with
  | nil => show GMap.size (∅ : GMap GoString V) ≤ 0; rw [GMap.map_size_empty]; exact Nat.le_refl 0
  | cons a l ih =>
    obtain ⟨k, v⟩ := a
    show GMap.size (<[k := v]> (GMap.ofList l)) ≤ _
    have := GMap.map_size_insert (GMap.ofList l) k v
    simp only [List.length_cons]
    split at this <;> omega

/-- **`initialModel(st0)`** (`realcheck.go`), and the abstraction of a driver's store: the items
at their store keys, the resource version, the prefix `/registry`, and (D30g) the keys whose
stored data is not canonical. -/
def absR (st : GSt) : RM :=
  ⟨GMap.ofList (st.items.map fun it => (storeKeyL it.key', it.obj')), st.rv, go!"/registry",
    GMap.ofList ((st.items.filter fun it => !it.canon').map fun it => (storeKeyL it.key', true))⟩

/-! ## Facts -/

theorem rexecL_read (x : Input) (m : RM) (h : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) :
    (rexecL x m).2 = (m, none) := by
  simp only [not_or] at h
  unfold rexecL
  split
  · rfl
  · simp_all

theorem w64_add_one_ne (n : w64) : (n + W64 1 = n) ↔ False := by
  constructor
  · intro e; bv_omega
  · intro e; exact e.elim

/-- A write either fails (the state unchanged, no change) or moves the resource version by one. -/
theorem rcreateL_cases (x : Input) (m : RM) :
    (rcreateL x m).2 = (m, none) ∨ (rcreateL x m).2.1.rv = m.rv + W64 1 := by
  unfold rcreateL failR
  dsimp only
  (repeat' split) <;> simp

theorem rdeleteL_cases (x : Input) (m : RM) :
    (rdeleteL x m).2 = (m, none) ∨ (rdeleteL x m).2.1.rv = m.rv + W64 1 := by
  unfold rdeleteL failR
  dsimp only
  (repeat' split) <;> simp

theorem rupdateL_cases (x : Input) (m : RM) :
    (rupdateL x m).2 = (m, none) ∨ (rupdateL x m).2.1.rv = m.rv + W64 1 := by
  unfold rupdateL failR updWriteL
  dsimp only
  (repeat' split) <;> simp

theorem rcreateL_rv_same (x : Input) (m : RM) (h : (rcreateL x m).2.1.rv = m.rv) :
    (rcreateL x m).2 = (m, none) :=
  (rcreateL_cases x m).resolve_right fun e => (w64_add_one_ne m.rv).1 (e ▸ h)

theorem rdeleteL_rv_same (x : Input) (m : RM) (h : (rdeleteL x m).2.1.rv = m.rv) :
    (rdeleteL x m).2 = (m, none) :=
  (rdeleteL_cases x m).resolve_right fun e => (w64_add_one_ne m.rv).1 (e ▸ h)

theorem rupdateL_rv_same (x : Input) (m : RM) (h : (rupdateL x m).2.1.rv = m.rv) :
    (rupdateL x m).2 = (m, none) :=
  (rupdateL_cases x m).resolve_right fun e => (w64_add_one_ne m.rv).1 (e ▸ h)

/-- An operation that does not move the resource version leaves the state and makes no
change. -/
theorem rexecL_rv_same (x : Input) (m : RM) (h : (rexecL x m).2.1.rv = m.rv) :
    (rexecL x m).2 = (m, none) := by
  unfold rexecL at h ⊢
  split
  · rfl
  next k4 =>
  split
  next k0 => rw [ite_eq_right_of_eq_false _ _ (eq_false k4), ite_eq_left_of_eq_true _ _ (eq_true k0)] at h; exact rcreateL_rv_same x m h
  next k0 =>
  split
  next k1 => rw [ite_eq_right_of_eq_false _ _ (eq_false k4), ite_eq_right_of_eq_false _ _ (eq_false k0), ite_eq_left_of_eq_true _ _ (eq_true k1)] at h; exact rdeleteL_rv_same x m h
  next k1 =>
  split
  next k2 => rw [ite_eq_right_of_eq_false _ _ (eq_false k4), ite_eq_right_of_eq_false _ _ (eq_false k0), ite_eq_right_of_eq_false _ _ (eq_false k1), ite_eq_left_of_eq_true _ _ (eq_true k2)] at h; exact rupdateL_rv_same x m h
  next => rfl

end go

end k8s_correctness
end EtcdGrove
end Perennial
