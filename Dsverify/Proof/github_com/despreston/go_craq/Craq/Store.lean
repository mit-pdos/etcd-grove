/-
The store's interface (the lab's `Iface.lean`, its store part; notes/dsv-craq.md): the abstract
contents `StoreS` (a store's items `(key, version, value, committed)` in arrival order), the
client's share `storeOwn`, and `isStore`, the logically atomic specs of the `store.Storer` methods
the node uses, on the interface value. The store's error for an absent key or version is
`errNotFound` (`store.ErrNotFound`'s value, an `errors.New` error), stated over Perennial's
`errors.newVar` (the lab's used the rpc model's `errMsg`; this module needs no rpc).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.store.Base
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Theory.Map
public import Iris.ProgramLogic.Atomic

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- A store's abstract contents: its items `(key, version, value, committed)` in arrival order. -/
abbrev StoreS := List (GoString × w64 × GoString × Bool)

namespace StoreS

/-- The items of `k`: `(version, value, committed)`. -/
def items (S : StoreS) (k : GoString) : List (w64 × GoString × Bool) :=
  (S.filter (fun e => decide (e.1 = k))).map (·.2)

/-- `Write(k, x, v)`: a dirty item appended. -/
def write (S : StoreS) (k : GoString) (x : GoString) (v : w64) : StoreS :=
  S ++ [(k, v, x, false)]

/-- Some item of `k` has version `v`. -/
def hasVer (S : StoreS) (k : GoString) (v : w64) : Bool := (S.items k).any (fun e => decide (e.1 = v))

/-- `Commit(k, v)` of a version the store has: its items committed, the older versions of `k`
cleared. -/
def commit (S : StoreS) (k : GoString) (v : w64) : StoreS :=
  S.filterMap fun e =>
    if e.1 ≠ k then some e
    else if uint.Z e.2.1 < uint.Z v then none
    else if e.2.1 = v then some (e.1, e.2.1, e.2.2.1, true) else some e

/-- The highest committed version of `k` (0 if none). -/
def maxCommitted (S : StoreS) (k : GoString) : w64 :=
  (S.items k).foldl (fun m e => if e.2.2 = true ∧ uint.Z m < uint.Z e.1 then e.1 else m) (W64 0)

end StoreS

/-- The request's version of `k` (0 if absent). -/
def reqVer (req : GMap GoString w64) (k : GoString) : w64 := (req.lookup k).getD (W64 0)

section store
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [store.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The store's contents (fractional): `q` of the client's half (the store keeps the other half
under its lock). Its name is the store's. -/
def storeOwn (γs : GName) (q : Qp) (S : StoreS) : IProp GF := ghostVar γs q.half S

/-- Item `p` is `x` at version `v` of `k` (persistent; its `Committed` flag is the store's). -/
def itemPtr (p : Loc) (k : GoString) (v : w64) (x : GoString) : IProp GF :=
  iprop(structFieldRef store.Item go!"Key" p ↦□ k ∗ structFieldRef store.Item go!"Version" p ↦□ v ∗
    ∃ sl : GoSlice, structFieldRef store.Item go!"Value" p ↦□ sl ∗ sl ↦*□ x)

/-- A slice of items, each in `S` (as of the call), with the predicate `P` on `(k, v, x, c)`. -/
def itemsIn (sl : GoSlice) (S : StoreS) (P : GoString → w64 → GoString → Bool → Prop) :
    IProp GF :=
  iprop(∃ (ps : List Loc) (es : List (GoString × w64 × GoString × Bool)),
    sl ↦* ps ∗ ⌜ps.length = es.length ∧ ∀ e ∈ es, (e.2.1, e.2.2.1, e.2.2.2) ∈ S.items e.1 ∧
      P e.1 e.2.1 e.2.2.1 e.2.2.2⌝ ∗
    [∗list] i ↦ p ∈ ps, ∃ e, ⌜es[i]? = some e⌝ ∗ itemPtr p e.1 e.2.1 e.2.2.1)

/-- A slice of each key's newest committed item in `S`, for the keys whose newest committed
version is newer than the request's. -/
def newestIn (sl : GoSlice) (S : StoreS) (req : GMap GoString w64) : IProp GF :=
  iprop(∃ (ps : List Loc) (es : List (GoString × w64 × GoString)),
    sl ↦* ps ∗ ⌜ps.length = es.length ∧ (es.map Prod.fst).Nodup ∧
      (∀ e ∈ es, (e.2.1, e.2.2, true) ∈ S.items e.1 ∧ e.2.1 = S.maxCommitted e.1) ∧
      (∀ k, uint.Z (reqVer req k) < uint.Z (S.maxCommitted k) → ∃ e ∈ es, e.1 = k)⌝ ∗
    [∗list] i ↦ p ∈ ps, ∃ e, ⌜es[i]? = some e⌝ ∗ itemPtr p e.1 e.2.1 e.2.2)

/-- The store's error for an absent key or version: `store.ErrNotFound`'s value, an `errors.New`
error with its message (persistent). -/
def errNotFound (err : GoInterface) : IProp GF :=
  iprop(∃ x : Loc, ⌜err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ ∗
    globalAddr store.ErrNotFound ↦□ err ∗
    x.[errors.errorString, go!"s"] ↦□ go!"that key does not exist" ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #go!"that key does not exist" -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x)) (Val #()))
        {{ Φ }})

instance errNotFound_persistent (err : GoInterface) : Persistent (errNotFound (hG := hG) err) := by
  unfold errNotFound; infer_instance

/-- `st` is a store whose contents are `γs`'s (persistent): the logically atomic specs of the
methods the node uses. -/
def isStore (st : GoInterface) (γs : GName) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜st = interface.ok e⌝ ∗ □ (
    -- Write(k, val, v)
    (∀ (k : GoString) (sl : GoSlice) (x : GoString) (v : w64), sl ↦*□ x -∗
      <<{ ∀∀ S, storeOwn γs 1 S }>>
        (App (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) (Val #v)) @ ∅
      <<{ storeOwn γs 1 (S.write k x v) | RET #interface.nil; True }>>) ∧
    -- Commit(k, v)
    (∀ (k : GoString) (v : w64),
      <<{ ∀∀ S, storeOwn γs 1 S }>>
        (App (App (Val #(methods e.ty go!"Commit" e.v)) (Val #k)) (Val #v)) @ ∅
      <<{ storeOwn γs 1 (if S.hasVer k v then S.commit k v else S) |
          (err : GoInterface), RET #err;
          if S.hasVer k v then ⌜err = interface.nil⌝ else errNotFound err }>>) ∧
    -- ReadVersion(k, v)
    (∀ (k : GoString) (v : w64),
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (App (Val #(methods e.ty go!"ReadVersion" e.v)) (Val #k)) (Val #v)) @ ∅
      <<{ ∃∃ (r : Option GoString), storeOwn γs q S ∗
            ⌜∀ x, r = some x → ∃ c, (v, x, c) ∈ S.items k⌝ ∗ ⌜r = none → S.hasVer k v = false⌝ |
          (p : Loc) (err : GoInterface), RET (PairV #p #err);
          match r with
          | some x => ⌜err = interface.nil⌝ ∗ itemPtr p k v x
          | none => errNotFound err }>>) ∧
    -- AllCommitted()
    (<<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods e.ty go!"AllCommitted" e.v)) (Val #())) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          itemsIn sl S (fun _ _ _ c => c = true) }>>) ∧
    -- AllDirty()
    (<<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods e.ty go!"AllDirty" e.v)) (Val #())) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          itemsIn sl S (fun _ _ _ c => c = false) }>>) ∧
    -- AllNewerDirty(req)
    (∀ (mp : Loc) (req : GMap GoString w64) (dq0 : DFrac), ownMap mp dq0 req -∗
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods e.ty go!"AllNewerDirty" e.v)) (Val #mp)) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          ownMap mp dq0 req ∗ itemsIn sl S (fun _ _ _ c => c = false) }>>) ∧
    -- AllNewerCommitted(req): each key's newest committed item, if newer than the request's
    (∀ (mp : Loc) (req : GMap GoString w64) (dq0 : DFrac), ownMap mp dq0 req -∗
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods e.ty go!"AllNewerCommitted" e.v)) (Val #mp)) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          ownMap mp dq0 req ∗ newestIn sl S req }>>)))

instance isStore_persistent (st : GoInterface) (γs : GName) :
    Persistent (isStore (hG := hG) st γs) := by
  unfold isStore; infer_instance

end store

end github_com.despreston.go_craq

end Perennial
