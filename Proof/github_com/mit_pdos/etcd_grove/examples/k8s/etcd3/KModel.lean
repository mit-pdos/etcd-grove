/-
Lean-first (no Rocq counterpart).

# The driver's model, as pure functions (stage 6a of `notes/k8s-etcd3-plan.md`)

`examples/k8s/etcd3/k8s_etcd3.go`'s `Model(st0)` (a Go copy of `correctness.Model`, D30m) computes
on Go values: a store (`mstore`: the items sorted by key, each an object with its resource
version and the canonical bit, D30g; the resource version) and the failed writes that may still
take effect. Here are the pure functions its helpers compute, as their specs state them
(`Spec/.../k8setcd3/<fn>.lean`): `lookupL`, `setItemL`, `delItemL`, `notFoundL`, `invalidObjL`,
`objOutL`, `preOkL`, `sameObjL`, `mcreateL`, `mdeleteL`, `mupdateL`, `mgetL`, `mstepL` (`mstep`)
and `isWriteL`. Stage 7b: UIDs, the preconditions (`preOkL`, an `EInvalid` answer), updates with
`ignoreNotFound` (from the zero object), and a `Get`'s minimum resource version (`EOther` above
the store's).

**The driver's model is these functions**: `kSpec st0`, linkv's `PendSpec` of `mstepL` from the
seeded store `st0` (`linkv/PendModel.lean`: failed writes pending, taking effect later or never).
The Go model's states are its configurations' lists (`Steps.lean`). Unlike linkvtxn's, the model
is stated on the Go records themselves, with Go's 64-bit resource versions; how the store's
model (`Model.lean`'s `KSt`) refines it is stage 6b.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.PendModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Callbacks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## Decidable equality of the Go records -/

instance Obj_decEq : DecidableEq Obj := fun a b =>
  decidable_of_iff (a.Name' = b.Name' ∧ a.UID' = b.UID' ∧ a.Value' = b.Value' ∧
      a.ResourceVersion' = b.ResourceVersion') (by cases a; cases b; simp)

instance item_decEq : DecidableEq item := fun a b =>
  decidable_of_iff (a.key' = b.key' ∧ a.obj' = b.obj' ∧ a.canon' = b.canon')
    (by cases a; cases b; simp)

instance Input_decEq : DecidableEq Input := fun a b =>
  decidable_of_iff (a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧
      a.Reject' = b.Reject' ∧ a.NoOp' = b.NoOp' ∧ a.IgnoreNotFound' = b.IgnoreNotFound' ∧
      a.UID' = b.UID' ∧ a.HasPreUID' = b.HasPreUID' ∧ a.PreUID' = b.PreUID' ∧
      a.HasPreRV' = b.HasPreRV' ∧ a.PreRV' = b.PreRV' ∧ a.UseCached' = b.UseCached' ∧
      a.Cached' = b.Cached' ∧ a.MinRV' = b.MinRV' ∧ a.Client' = b.Client')
    (by cases a; cases b; simp)

instance Output_decEq : DecidableEq Output := fun a b =>
  decidable_of_iff (a.Err' = b.Err' ∧ a.ErrKey' = b.ErrKey' ∧ a.ErrRV' = b.ErrRV' ∧
      a.Name' = b.Name' ∧ a.UID' = b.UID' ∧ a.Value' = b.Value' ∧ a.RV' = b.RV')
    (by cases a; cases b; simp)

/-! ## The store's helpers -/

/-- The zero `item` (`item{}`). -/
def zItem : item := ⟨[], ⟨[], [], [], W64 0⟩, false⟩

/-- `lookup(items, k)`: `k`'s first item. -/
def lookupL (its : List item) (k : GoString) : item × Bool :=
  match its.find? (fun it => decide (it.key' = k)) with
  | some it => (it, true)
  | none => (zItem, false)

/-- One iteration of `setItem`'s loop on `(out, done)`. -/
def setStepI (it : item) (st : List item × Bool) (e : item) : List item × Bool :=
  let st := if st.2 = false ∧ go.GoStringLt it.key' e.key' then (st.1 ++ [it], true) else st
  if e.key' = it.key' then (if st.2 = false then (st.1 ++ [it], true) else st)
  else (st.1 ++ [e], st.2)

/-- `setItem(items, it)`. -/
def setItemL (its : List item) (it : item) : List item :=
  let st := its.foldl (setStepI it) ([], false)
  if st.2 then st.1 else st.1 ++ [it]

/-- `delItem(items, k)`. -/
def delItemL (its : List item) (k : GoString) : List item :=
  its.filter (fun e => !decide (e.key' = k))

/-- `storeKey(name)`. -/
def storeKeyL (name : GoString) : GoString := go!"/objs/" ++ name

/-- The model's key of a name (`Prefix + storeKey(name)`). -/
def mkeyL (name : GoString) : GoString := go!"/registry" ++ storeKeyL name

/-! ## The answers -/

/-- A store's contents: its items and resource version. -/
structure GSt where
  items : List item
  rv : w64

instance GSt_decEq : DecidableEq GSt := fun a b =>
  decidable_of_iff (a.items = b.items ∧ a.rv = b.rv) (by cases a; cases b; simp)

/-- `notFound(st, key)` of a store at the resource version `rv`. -/
def notFoundL (rv : w64) (key : GoString) : Output := ⟨W64 1, mkeyL key, rv, [], [], [], 0⟩

/-- `invalidObj(key)`: a failed precondition (stage 7b). -/
def invalidObjL (key : GoString) : Output := ⟨W64 5, mkeyL key, 0, [], [], [], 0⟩

/-- `objOut(o)`. -/
def objOutL (o : Obj) : Output := ⟨W64 0, [], 0, o.Name', o.UID', o.Value', o.ResourceVersion'⟩

/-- "key exists" (`Output{Err: EExists, ...}`). -/
def existsL (key : GoString) : Output := ⟨W64 2, mkeyL key, W64 0, [], [], [], 0⟩

/-- A callback's rejection (`Output{Err: ERejected}`). -/
def rejectedL : Output := ⟨W64 3, [], 0, [], [], [], 0⟩

/-- Any other error (`Output{Err: EOther}`): a `Get`'s minimum resource version above the store's
or not parsing (stage 7b, T2 (b)). -/
def otherL : Output := ⟨W64 4, [], 0, [], [], [], 0⟩

/-- The zero object's answer (`Output{Err: ENone}`). -/
def zeroOutL : Output := ⟨W64 0, [], 0, [], [], [], 0⟩

/-- The zero object (`Obj{}`). -/
def zObj : Obj := ⟨[], [], [], W64 0⟩

/-- `preOk(in, o)`: the preconditions, where given, are `o`'s UID and resource version (its
string, `rvString`). -/
def preOkL (x : Input) (o : Obj) : Bool :=
  (if x.HasPreUID' then decide (x.PreUID' = o.UID') else true) &&
    (if x.HasPreRV' then decide (x.PreRV' = rvStr o.ResourceVersion') else true)

/-- `sameObj(a, b)`: equal but for the resource versions. -/
def sameObjL (a b : Obj) : Bool :=
  decide (a.Name' = b.Name') && decide (a.UID' = b.UID') && decide (a.Value' = b.Value')

/-! ## One operation -/

/-- `mcreate(in, st)`. -/
def mcreateL (x : Input) (st : GSt) : GSt × Output :=
  if (lookupL st.items x.Key').2 then (st, existsL x.Key')
  else
    let o : Obj := ⟨x.Key', x.UID', x.Val', st.rv + W64 1⟩
    (⟨setItemL st.items ⟨x.Key', o, true⟩, st.rv + W64 1⟩, objOutL o)

/-- `mdelete(in, st)`. -/
def mdeleteL (x : Input) (st : GSt) : GSt × Output :=
  let it := (lookupL st.items x.Key').1
  if !(lookupL st.items x.Key').2 then (st, notFoundL st.rv x.Key')
  else if !preOkL x it.obj' then (st, invalidObjL x.Key')
  else if rejects x.Reject' it.obj'.Value' then (st, rejectedL)
  else
    (⟨delItemL st.items x.Key', st.rv + W64 1⟩,
      objOutL { it.obj' with ResourceVersion' := st.rv + W64 1 })

/-- `updated(in, o)`'s object (`updObj` on the Go record): the value `in.Val` and, for the zero
object, the name `in.Key`, unless `in.NoOp`. -/
def updatedL (x : Input) (o : Obj) : Obj :=
  if x.NoOp' then o
  else { o with Name' := if o.Name' = [] then x.Key' else o.Name', Value' := x.Val' }

/-- `mupdate(in, st)`: from the stored object, or the zero object for a missing key with
`ignoreNotFound` (stage 7b). -/
def mupdateL (x : Input) (st : GSt) : GSt × Output :=
  let it := (lookupL st.items x.Key').1
  let ok := (lookupL st.items x.Key').2
  if !ok && !x.IgnoreNotFound' then (st, notFoundL st.rv x.Key')
  else
    let cur := if ok then it.obj' else zObj
    if !preOkL x cur then (st, invalidObjL x.Key')
    else if rejects x.Reject' cur.Value' then (st, rejectedL)
    else
      let r := updatedL x cur
      if ok = true ∧ sameObjL r it.obj' = true ∧ it.canon' = true then
        (st, objOutL it.obj')
      else
        let o := { r with ResourceVersion' := st.rv + W64 1 }
        (⟨setItemL st.items ⟨x.Key', o, true⟩, st.rv + W64 1⟩, objOutL o)

/-- `mget(in, st)`: an `EOther` for a minimum resource version that does not parse or is above
the store's (stage 7b), else the stored object, the zero object (`IgnoreNotFound`) or "not
found". -/
def mgetL (x : Input) (st : GSt) : Output :=
  match parseRVD x.MinRV' with
  | none => otherL
  | some req =>
    if uint.nat st.rv < uint.nat req then otherL
    else if !(lookupL st.items x.Key').2 then
      (if x.IgnoreNotFound' then zeroOutL else notFoundL st.rv x.Key')
    else objOutL (lookupL st.items x.Key').1.obj'

/-- `mstep(in, st)`. -/
def mstepL (x : Input) (st : GSt) : GSt × Output :=
  if x.Kind' = W64 0 then mcreateL x st
  else if x.Kind' = W64 1 then mdeleteL x st
  else if x.Kind' = W64 2 then mupdateL x st
  else (st, mgetL x st)

/-- `isWrite(in)`. -/
def isWriteL (x : Input) : Bool := decide (x.Kind' ≠ W64 3)

/-- **The driver's model** from the seeded store `st0` (see the file header). -/
abbrev kSpec (st0 : GSt) : linkv.PendSpec GSt Input Output := ⟨st0, mstepL, isWriteL⟩

/-- A call's answer: an output whose error is `EOther` is a failed call (its effect unknown). -/
def ansOf (y : Output) : linkv.Ans Output := if y.Err' = W64 4 then .err else .ok y

end go

end k8s_etcd3
end EtcdGrove
end Perennial
