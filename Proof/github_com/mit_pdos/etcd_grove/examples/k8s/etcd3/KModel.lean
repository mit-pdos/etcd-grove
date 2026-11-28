/-
Lean-first (no Rocq counterpart).

# The driver's model, as pure functions (stage 6a of `notes/k8s-etcd3-plan.md`)

`examples/k8s/etcd3/k8s_etcd3.go`'s `Model(st0)` (a Go copy of `correctness.Model`, D30m) computes
on Go values: a store (`mstore`: the items sorted by key, each an object with its resource
version and the canonical bit, D30g; the resource version) and the failed writes that may still
take effect. Here are the pure functions its helpers compute, as their specs state them
(`Spec/.../k8setcd3/<fn>.lean`): `lookupL`, `setItemL`, `delItemL`, `notFoundL`, `invalidObjL`,
`preMsgL`, `objOutL`, `preOkL`, `sameObjL`, `mcreateL`, `mdeleteL`, `mupdateL`, `mgetL`, `mstepL` (`mstep`)
and `isWriteL`. Stage 7b: UIDs, the preconditions (`preOkL`, an `EInvalid` answer), updates with
`ignoreNotFound` (from the zero object), and a `Get`'s minimum resource version (`EOther` above
the store's).

**The driver's model is these functions**, with the list and the store's history of
`KList.lean` (stage 7e): `kSpec h0` there, linkv's `PendSpec` of `kstepL` (`mstepL`, or `mlistL`
for a list) from the seeded store and its history `h0` (`linkv/PendModel.lean`: failed writes
pending, taking effect later or never).
The Go model's states are its configurations' lists (`Steps.lean`). Unlike linkvtxn's, the model
is stated on the Go records themselves, with Go's 64-bit resource versions; how the store's
model (`Model.lean`'s `KSt`) refines it is stage 6b.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.PendModel
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
  decidable_of_iff (a.Namespace' = b.Namespace' ∧ a.Name' = b.Name' ∧ a.UID' = b.UID' ∧
      a.Value' = b.Value' ∧ a.Node' = b.Node' ∧ a.App' = b.App' ∧
      a.ResourceVersion' = b.ResourceVersion' ∧ a.Annotated' = b.Annotated')
    (by cases a; cases b; simp)

instance item_decEq : DecidableEq item := fun a b =>
  decidable_of_iff (a.key' = b.key' ∧ a.obj' = b.obj' ∧ a.canon' = b.canon')
    (by cases a; cases b; simp)

instance Input_decEq : DecidableEq Input := fun a b =>
  decidable_of_iff (a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧
      a.Node' = b.Node' ∧ a.App' = b.App' ∧ a.HasReject' = b.HasReject' ∧
      a.Reject' = b.Reject' ∧ a.NoOp' = b.NoOp' ∧ a.IgnoreNotFound' = b.IgnoreNotFound' ∧
      a.UID' = b.UID' ∧ a.HasPreUID' = b.HasPreUID' ∧ a.PreUID' = b.PreUID' ∧
      a.HasPreRV' = b.HasPreRV' ∧ a.PreRV' = b.PreRV' ∧ a.UseCached' = b.UseCached' ∧
      a.Cached' = b.Cached' ∧ a.MinRV' = b.MinRV' ∧ a.ListKey' = b.ListKey' ∧
      a.Recursive' = b.Recursive' ∧ a.Match' = b.Match' ∧ a.Field' = b.Field' ∧
      a.SelNS' = b.SelNS' ∧ a.SelName' = b.SelName' ∧ a.SelNode' = b.SelNode' ∧
      a.SelApp' = b.SelApp' ∧ a.Limit' = b.Limit' ∧ a.Client' = b.Client' ∧
      a.WKey' = b.WKey' ∧ a.SendInit' = b.SendInit' ∧ a.Bookmarks' = b.Bookmarks' ∧
      a.Behavior' = b.Behavior' ∧ a.Skip' = b.Skip')
    (by cases a; cases b; simp)

/-- `Raw` (stage 7g: the store's own answer, which the model ignores) holds Go values; its
equality is decided classically. -/
instance Raw_decEq : DecidableEq github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw :=
  fun _ _ => Classical.propDecidable _

instance Output_decEq : DecidableEq Output := fun a b =>
  decidable_of_iff (a.Err' = b.Err' ∧ a.ErrKey' = b.ErrKey' ∧ a.ErrRV' = b.ErrRV' ∧ a.ErrMsg' = b.ErrMsg' ∧
      a.Namespace' = b.Namespace' ∧ a.Name' = b.Name' ∧ a.UID' = b.UID' ∧ a.Value' = b.Value' ∧
      a.Node' = b.Node' ∧ a.App' = b.App' ∧ a.RV' = b.RV' ∧ a.Items' = b.Items' ∧
      a.ListRV' = b.ListRV' ∧ a.Continue' = b.Continue' ∧ a.HasRemaining' = b.HasRemaining' ∧
      a.Remaining' = b.Remaining' ∧ a.WEvents' = b.WEvents' ∧ a.WFailed' = b.WFailed' ∧
      a.Raw' = b.Raw')
    (by cases a; cases b; simp)

/-- **An output's plain value** (stage 7g): the output with its `Raw` (the store's answer itself, which
`outEqual` and the model ignore) zeroed; two outputs `outEqual` compares equal iff their plain values are. -/
@[reducible] def plainOut (y : Output) : Output := { y with Raw' := zeroValDef }

/-- Equal plain values are equal plain fields. -/
theorem plainOut_eq_iff (a b : Output) : plainOut a = plainOut b ↔
    a.Err' = b.Err' ∧ a.ErrKey' = b.ErrKey' ∧ a.ErrRV' = b.ErrRV' ∧ a.ErrMsg' = b.ErrMsg' ∧
    a.Namespace' = b.Namespace' ∧ a.Name' = b.Name' ∧ a.UID' = b.UID' ∧ a.Value' = b.Value' ∧
    a.Node' = b.Node' ∧ a.App' = b.App' ∧ a.RV' = b.RV' ∧ a.Items' = b.Items' ∧
    a.ListRV' = b.ListRV' ∧ a.Continue' = b.Continue' ∧ a.HasRemaining' = b.HasRemaining' ∧
    a.Remaining' = b.Remaining' ∧ a.WEvents' = b.WEvents' ∧ a.WFailed' = b.WFailed' := by
  cases a; cases b; simp [plainOut]

/-- An output with a zero `Raw` is its plain value. -/
theorem plainOut_of_raw (y : Output) (h : y.Raw' = zeroValDef) : plainOut y = y := by
  cases y; simp only [plainOut] at h ⊢; rw [h]

theorem plainOut_idem (y : Output) : plainOut (plainOut y) = plainOut y := rfl

/-! ## The store's helpers -/

/-- The zero `item` (`item{}`). -/
def zItem : item := ⟨[], ⟨[], [], [], [], [], [], W64 0, false⟩, false⟩

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

/-- `storeKey(key)` (`ResourcePrefix + "/" + key`). -/
def storeKeyL (key : GoString) : GoString := go!"/objs/" ++ key

/-- The model's key of a name (`Prefix + storeKey(name)`). -/
def mkeyL (name : GoString) : GoString := go!"/registry" ++ storeKeyL name

/-! ## The answers -/

/-- A store's contents: its items and resource version. -/
structure GSt where
  items : List item
  rv : w64

instance GSt_decEq : DecidableEq GSt := fun a b =>
  decidable_of_iff (a.items = b.items ∧ a.rv = b.rv) (by cases a; cases b; simp)

/-- An output with no object and no list: the error `e`, its key `k` and resource version `r`
(`Output{Err: e, ErrKey: k, ErrRV: r}`). -/
def errOutL (e : w64) (k : GoString) (r : w64) : Output :=
  ⟨e, k, r, [], [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, zeroValDef⟩

/-- A failed precondition's output with the store key `k` and the message `msg`
(`Output{Err: EInvalid, ErrKey: k, ErrMsg: msg}`, stage 7g). -/
def invalidOutL (k msg : GoString) : Output :=
  ⟨W64 5, k, 0, msg, [], [], [], [], [], [], 0, [], 0, [], false, 0, [], false, zeroValDef⟩

/-- `notFound(st, key)` of a store at the resource version `rv`. -/
def notFoundL (rv : w64) (key : GoString) : Output := errOutL (W64 1) (mkeyL key) rv

/-- `invalidObj(key, msg)`: a failed precondition (stage 7b), with its message (stage 7g:
`Output{Err: EInvalid, ErrKey: ..., ErrMsg: msg}`). -/
def invalidObjL (key msg : GoString) : Output := invalidOutL (mkeyL key) msg

/-- `objOut(o)`. -/
def objOutL (o : Obj) : Output :=
  ⟨W64 0, [], 0, [], o.Namespace', o.Name', o.UID', o.Value', o.Node', o.App', o.ResourceVersion',
    [], 0, [], false, 0, [], false, zeroValDef⟩

/-- `objOf(out)`: an answer's object. -/
def objOfL (y : Output) : Obj :=
  ⟨y.Namespace', y.Name', y.UID', y.Value', y.Node', y.App', y.RV', false⟩

/-- "key exists" (`Output{Err: EExists, ...}`). -/
def existsL (key : GoString) : Output := errOutL (W64 2) (mkeyL key) (W64 0)

/-- A callback's rejection (`Output{Err: ERejected}`). -/
def rejectedL : Output := errOutL (W64 3) [] 0

/-- Any other error (`Output{Err: EOther}`): a minimum resource version that does not parse
(stage 7b, T2 (b)). -/
def otherL : Output := errOutL (W64 4) [] 0

/-- A resource version above the store's (`Output{Err: ETooLarge}`, stage 7e). -/
def tooLargeL : Output := errOutL (W64 6) [] 0

/-- The zero object's answer (`Output{Err: ENone}`). -/
def zeroOutL : Output := errOutL (W64 0) [] 0

/-- The zero object (`Obj{}`). -/
def zObj : Obj := ⟨[], [], [], [], [], [], W64 0, false⟩

/-- `preOk(in, o)`: the preconditions, where given, are `o`'s UID and resource version (its
string, `rvString`). -/
def preOkL (x : Input) (o : Obj) : Bool :=
  (if x.HasPreUID' then decide (x.PreUID' = o.UID') else true) &&
    (if x.HasPreRV' then decide (x.PreRV' = rvStr o.ResourceVersion') else true)

/-- `preMsg(in, o)`: `preconditions(in).Check`'s message on `o` when they fail (stage 7g): the
UID's mismatch if there is one, else the resource version's (its string, `rvString`). -/
def preMsgL (x : Input) (o : Obj) : GoString :=
  if x.HasPreUID' && !decide (x.PreUID' = o.UID') then
    go!"Precondition failed: UID in precondition: " ++ x.PreUID' ++
      go!", UID in object meta: " ++ o.UID'
  else
    go!"Precondition failed: ResourceVersion in precondition: " ++ x.PreRV' ++
      go!", ResourceVersion in object meta: " ++ rvStr o.ResourceVersion'

/-- `sameObj(a, b)`: equal but for the resource versions. -/
def sameObjL (a b : Obj) : Bool :=
  decide (a.Namespace' = b.Namespace') && decide (a.Name' = b.Name') &&
    decide (a.UID' = b.UID') && decide (a.Value' = b.Value') && decide (a.Node' = b.Node') &&
    decide (a.App' = b.App')

/-! ## One operation -/

/-- `mcreate(in, st)`. -/
def mcreateL (x : Input) (st : GSt) : GSt × Output :=
  if (lookupL st.items x.Key').2 then (st, existsL x.Key')
  else
    let o : Obj := ⟨(splitKeyL x.Key').1, (splitKeyL x.Key').2, x.UID', x.Val', x.Node', x.App',
      st.rv + W64 1, false⟩
    (⟨setItemL st.items ⟨x.Key', o, true⟩, st.rv + W64 1⟩, objOutL o)

/-- `mdelete(in, st)`. -/
def mdeleteL (x : Input) (st : GSt) : GSt × Output :=
  let it := (lookupL st.items x.Key').1
  if !(lookupL st.items x.Key').2 then (st, notFoundL st.rv x.Key')
  else if !preOkL x it.obj' then (st, invalidObjL x.Key' (preMsgL x it.obj'))
  else if rejects x.HasReject' x.Reject' it.obj'.Node' then (st, rejectedL)
  else
    (⟨delItemL st.items x.Key', st.rv + W64 1⟩,
      objOutL { it.obj' with ResourceVersion' := st.rv + W64 1 })

/-- `updated(in, o)`'s object: `updGo` (`Callbacks.lean`). -/
abbrev updatedL (x : Input) (o : Obj) : Obj := updGo x o

/-- `mupdate(in, st)`: from the stored object, or the zero object for a missing key with
`ignoreNotFound` (stage 7b). -/
def mupdateL (x : Input) (st : GSt) : GSt × Output :=
  let it := (lookupL st.items x.Key').1
  let ok := (lookupL st.items x.Key').2
  if !ok && !x.IgnoreNotFound' then (st, notFoundL st.rv x.Key')
  else
    let cur := if ok then it.obj' else zObj
    if !preOkL x cur then (st, invalidObjL x.Key' (preMsgL x cur))
    else if rejects x.HasReject' x.Reject' cur.Node' then (st, rejectedL)
    else
      let r := updatedL x cur
      if ok = true ∧ sameObjL r it.obj' = true ∧ it.canon' = true then
        (st, objOutL it.obj')
      else
        let o := { r with ResourceVersion' := st.rv + W64 1 }
        (⟨setItemL st.items ⟨x.Key', o, true⟩, st.rv + W64 1⟩, objOutL o)

/-- `mget(in, st)`: an `EOther` for a minimum resource version that does not parse (stage 7b), an
`ETooLarge` for one above the store's (stage 7e), else the stored object, the zero object
(`IgnoreNotFound`) or "not found". -/
def mgetL (x : Input) (st : GSt) : Output :=
  match parseRVD x.MinRV' with
  | none => otherL
  | some req =>
    if uint.nat st.rv < uint.nat req then tooLargeL
    else if !(lookupL st.items x.Key').2 then
      (if x.IgnoreNotFound' then zeroOutL else notFoundL st.rv x.Key')
    else objOutL (lookupL st.items x.Key').1.obj'

/-- `mstep(in, st)`. -/
def mstepL (x : Input) (st : GSt) : GSt × Output :=
  if x.Kind' = W64 0 then mcreateL x st
  else if x.Kind' = W64 1 then mdeleteL x st
  else if x.Kind' = W64 2 then mupdateL x st
  else (st, mgetL x st)

/-- `isWrite(in)`: the write kinds, explicitly (stage 7e: a `List` is no write). -/
def isWriteL (x : Input) : Bool :=
  (decide (x.Kind' = W64 0)).or ((decide (x.Kind' = W64 1)).or (decide (x.Kind' = W64 2)))

/-- `floored(r, floor)` (k8s 7g, D7g-1): a non-zero resource version below `floor` raised to it. -/
def flooredL (r f : w64) : w64 := if r ≠ W64 0 ∧ r < f then f else r

/-- **The floor** (departure D7g-1): a requested resource version is `0` or at least the floor `s0` (the
seeded store's revision). -/
def FloorOk (s0 : w64) (x : Input) : Prop :=
  ∀ q, parseRVD x.MinRV' = some q → q = 0 ∨ uint.nat s0 ≤ uint.nat q

theorem flooredL_floor (r f : w64) : flooredL r f = 0 ∨ uint.nat f ≤ uint.nat (flooredL r f) ∧
    uint.nat (flooredL r f) ≤ max (uint.nat r) (uint.nat f) := by
  unfold flooredL
  by_cases h : r ≠ W64 0 ∧ r < f
  · rw [if_pos h]; right; constructor <;> word
  · rw [if_neg h]
    by_cases h0 : r = W64 0
    · left; exact h0
    · right; have : ¬ r < f := fun h' => h ⟨h0, h'⟩
      constructor <;> word

theorem flooredL_ok (r f : w64) : flooredL r f = 0 ∨ uint.nat f ≤ uint.nat (flooredL r f) := by
  rcases flooredL_floor r f with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem flooredL_lt (r f : w64) (B : Int) (hr : uint.Z r < B) (hf : uint.Z f < B) :
    uint.Z (flooredL r f) < B := by
  unfold flooredL; split <;> assumption

/-- An input with no minimum resource version is floored. -/
theorem floorOk_nil (f : w64) (x : Input) (h : x.MinRV' = []) : FloorOk f x := fun q hq => by
  rw [h] at hq; simp [parseRVD] at hq; exact Or.inl hq.symm

/-- A call's answer: an output whose error is `EOther` is a failed call (its effect unknown). -/
def ansOf (y : Output) : linkv.Ans Output := if y.Err' = W64 4 then .err else .ok y

end go

end k8s_etcd3
end EtcdGrove
end Perennial
