/-
The structured-merge-diff driver's scenario (`examples/k8s/smd/smd.go`) **in the model**
(`Proof/sigs_k8s_io/structured_merge_diff/v7/Model/`): the schema `newSchema` builds, the objects
and managed fields the driver writes out, its `state` and its `state.apply`/`state.check` as
model functions, the nine steps' model results, and the facts `Main`'s proof uses, each decided
by the kernel (`decide +kernel`: no `native_decide`, no axiom).

**The model against the Go run.** The checks below are the driver's own checks, so that the model
computes what SMD computed when the driver ran (`go test ./examples/k8s/smd`, which runs `Main`
without a panic), and they are true of the model: every object, every manager's owned set (the
sets compared structurally, as `ManagedFields.Equals` does), the no-op apply of step 3 returning a
nil object (`ReturnInputOnNoop` false), the conflict of step 4 (`[{A, .replicas}]`, and the
managers then returned: an empty map, `ApplyRes.conflicts` in the model), the list order
`[b1, a2]` after step 7 (A's `a1` replaced by `a2` after B's `b1`).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Merge

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open smd

/-! ## The schema (`newSchema`) -/

def zeroAtom : Atom := .mk none .none .none
def named (n : GoString) : TypeRef := .mk (some n) zeroAtom false
def strRef : TypeRef := named go!"string"
def numRef : TypeRef := named go!"numeric"
def zeroRef : TypeRef := .mk none zeroAtom false
def fld (n : GoString) (t : TypeRef) : StructField := .mk n t

def rootMapT : MapT := .mk (.ofList [
  fld go!"name" strRef, fld go!"image" strRef, fld go!"replicas" numRef,
  fld go!"containers" (named go!"containers"), fld go!"labels" (named go!"labels"),
  fld go!"selector" (named go!"selector")]) zeroRef []
def containerMapT : MapT := .mk (.ofList [
  fld go!"name" strRef, fld go!"image" strRef, fld go!"port" numRef]) zeroRef []
def containersListT : ListT := .mk (named go!"container") go!"associative" [go!"name"]
def labelsMapT : MapT := .mk .nil strRef go!"separable"
def selectorMapT : MapT := .mk .nil strRef go!"atomic"

/-- The schema `newSchema` builds. -/
def sc : Schema := ⟨[
  (go!"root", .ofMap rootMapT),
  (go!"container", .ofMap containerMapT),
  (go!"containers", .ofList containersListT),
  (go!"labels", .ofMap labelsMapT),
  (go!"selector", .ofMap selectorMapT),
  (go!"string", .ofScalar go!"string"),
  (go!"numeric", .ofScalar go!"numeric")]⟩

/-- `schema.TypeRef{NamedType: &rootName}`. -/
def rootRef : TypeRef := named go!"root"
/-- The scenario's API version. -/
def version : GoString := go!"v1"

/-! ## Objects, paths, managed fields -/

/-- A `map[string]interface{}` literal's entries, sorted (a Go map has no order). -/
def mkKVs (kvs : List (GoString × UVal)) : List (GoString × UVal) := kvs.foldl (fun m (k, v) => insertKV k v m) []
/-- A `map[string]interface{}` literal. -/
def mkObj (kvs : List (GoString × UVal)) : UVal := .map (mkKVs kvs)
def str (x : GoString) : UVal := .str x
/-- `container(name, image)`'s entries. -/
def containerKVs (n i : GoString) : List (GoString × UVal) := mkKVs [(go!"name", str n), (go!"image", str i)]
/-- `container(name, image)`. -/
def container (n i : GoString) : UVal := .map (containerKVs n i)

/-- `field(name)`. -/
def field (n : GoString) : Path := [.field n]
/-- `mapKey(name, key)`. -/
def mapKey (n k : GoString) : Path := [.field n, .field k]
/-- `item(key)`. -/
def item (k : GoString) : Path := [.field go!"containers", .key [(go!"name", str k)]]
/-- `itemField(key, name)`. -/
def itemField (k n : GoString) : Path := item k ++ [.field n]
/-- `containerPaths(key)`. -/
def containerPaths (k : GoString) : List Path := [item k, itemField k go!"name", itemField k go!"image"]
/-- `applied(paths...)`. -/
def applied (ps : List Path) : VSet := ⟨PSet.ofPaths ps, version, true⟩
/-- `updated(paths...)`. -/
def updated (ps : List Path) : VSet := ⟨PSet.ofPaths ps, version, false⟩
/-- A `fieldpath.ManagedFields` literal (sorted). -/
def mkMF (ms : List (GoString × VSet)) : MF := ms.foldl (fun m (k, v) => insertKV k v m) []

/-! ## The driver's `state` -/

/-- `state`'s object and managed fields (its schema is `sc`, its updater `ReturnInputOnNoop`-less). -/
structure St where
  live : TV
  mf : MF
  deriving Inhabited

/-- `state.typedObj(obj)`: `AsTyped` of `obj` as a root; `none`: it does not validate (a panic). -/
def stTyped (o : UVal) : Option TV := asTyped sc o rootRef

/-- `state.apply(config, manager, msg)`: the new state and whether the object changed; `none`:
a panic (an error, or a configuration that does not validate). -/
def stApply (st : St) (config : UVal) (m : GoString) : Option (St × Bool) :=
  match stTyped config with
  | none => none
  | some cfg =>
    match apply false sc st.live cfg version st.mf m false with
    | .ok none mf => some ({ st with mf := mf }, false)
    | .ok (some o) mf => some (⟨o, mf⟩, true)
    | _ => none

/-- `state.check(obj, managers, msg)`: whether it returns (no panic). -/
def stCheck (st : St) (o : UVal) (m : MF) : Bool :=
  (match st.live.value with | some v => UVal.equals v o | none => false) && mfEquals st.mf m

/-- What `state.apply` needs of the state (spec premises of `Apply`): every manager's set at the
scenario's version, a named type. -/
def stOk (st : St) : Bool := st.mf.all (fun e => e.2.version == version) && st.live.typeRef.namedType.isSome

/-- A step's state, when the step returns (`Option.getD`). -/
def stOf (r : Option (St × Bool)) : St := (r.getD default).1

theorem eq_some_of_check (r : Option (St × Bool)) (b : Bool)
    (h : (r.isSome && (r.getD default).2 == b) = true) : r = some (stOf r, b) := by
  cases r with
  | none => simp at h
  | some p => obtain ⟨st, b'⟩ := p; simp [stOf] at h ⊢; exact h

/-! ## The steps -/

def obj0 : UVal := mkObj []
def S0 : St := ⟨⟨some obj0, rootRef⟩, []⟩

def selector1 : UVal := mkObj [(go!"k", str go!"v1"), (go!"m", str go!"x")]
def cfg1 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 1), (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", mkObj [(go!"app", str go!"web")]), (go!"selector", selector1)]
def aPaths1 : List Path := [field go!"name", field go!"image", field go!"replicas",
  mapKey go!"labels" go!"app", field go!"selector"] ++ containerPaths go!"a1"
def mf1 : MF := mkMF [(go!"A", applied aPaths1)]

def cfg2 : UVal := mkObj [(go!"labels", mkObj [(go!"team", str go!"t")])]
def labels2 : UVal := mkObj [(go!"app", str go!"web"), (go!"team", str go!"t")]
def obj2 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 1), (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels2), (go!"selector", selector1)]
def mf2 : MF := mkMF [(go!"A", applied aPaths1), (go!"B", applied [mapKey go!"labels" go!"team"])]

def cfg3 : UVal := mkObj [(go!"image", str go!"img1"), (go!"labels", mkObj [(go!"team", str go!"t")])]
def mf3 : MF := mkMF [(go!"A", applied aPaths1),
  (go!"B", applied [field go!"image", mapKey go!"labels" go!"team"])]

def cfg4 : UVal := mkObj [(go!"image", str go!"img1"), (go!"replicas", .int 2),
  (go!"labels", mkObj [(go!"team", str go!"t")])]
def conflicts4 : List Conflict := [⟨go!"A", field go!"replicas"⟩]

def obj5 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 2), (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels2), (go!"selector", selector1)]
def aPaths5 : List Path := [field go!"name", field go!"image", mapKey go!"labels" go!"app",
  field go!"selector"] ++ containerPaths go!"a1"
def bPaths5 : List Path := [field go!"image", field go!"replicas", mapKey go!"labels" go!"team"]
def mf5 : MF := mkMF [(go!"A", applied aPaths5), (go!"B", applied bPaths5)]

def cfg6 : UVal := mkObj [(go!"name", str go!"obj"), (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"selector", selector1)]
def obj6 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 2), (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", mkObj [(go!"team", str go!"t")]), (go!"selector", selector1)]
def aPaths6 : List Path := [field go!"name", field go!"selector"] ++ containerPaths go!"a1"
def mf6 : MF := mkMF [(go!"A", applied aPaths6), (go!"B", applied bPaths5)]

def cfg7a : UVal := mkObj [(go!"image", str go!"img1"), (go!"replicas", .int 2),
  (go!"containers", .list [container go!"b1" go!"y"]), (go!"labels", mkObj [(go!"team", str go!"t")])]
def bPaths7 : List Path := bPaths5 ++ containerPaths go!"b1"
def obj7a : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 2), (go!"containers", .list [container go!"a1" go!"x", container go!"b1" go!"y"]),
  (go!"labels", mkObj [(go!"team", str go!"t")]), (go!"selector", selector1)]
def mf7a : MF := mkMF [(go!"A", applied aPaths6), (go!"B", applied bPaths7)]

def cfg7b : UVal := mkObj [(go!"name", str go!"obj"), (go!"containers", .list [container go!"a2" go!"z"]),
  (go!"selector", selector1)]
def aPaths7 : List Path := [field go!"name", field go!"selector"] ++ containerPaths go!"a2"
def obj7b : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 2), (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", mkObj [(go!"team", str go!"t")]), (go!"selector", selector1)]
def mf7b : MF := mkMF [(go!"A", applied aPaths7), (go!"B", applied bPaths7)]

def obj8 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 3), (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", mkObj [(go!"team", str go!"t"), (go!"env", str go!"prod")]), (go!"selector", selector1)]
def bPaths8 : List Path := [field go!"image", mapKey go!"labels" go!"team"] ++ containerPaths go!"b1"
def mf8 : MF := mkMF [(go!"A", applied aPaths7), (go!"B", applied bPaths8),
  (go!"C", updated [field go!"replicas", mapKey go!"labels" go!"env"])]

def cfg9 : UVal := mkObj [(go!"name", str go!"obj"), (go!"containers", .list [container go!"a2" go!"z"]),
  (go!"selector", mkObj [(go!"k", str go!"v2")])]
def obj9 : UVal := mkObj [(go!"name", str go!"obj"), (go!"image", str go!"img1"),
  (go!"replicas", .int 3), (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", mkObj [(go!"team", str go!"t"), (go!"env", str go!"prod")]),
  (go!"selector", mkObj [(go!"k", str go!"v2")])]

/-- Steps 1-3 (`state.apply`). -/
def r1 : Option (St × Bool) := stApply S0 cfg1 go!"A"
def S1 : St := stOf r1
def r2 : Option (St × Bool) := stApply S1 cfg2 go!"B"
def S2 : St := stOf r2
def r3 : Option (St × Bool) := stApply S2 cfg3 go!"B"
def S3 : St := stOf r3

/-- `cfg4` typed (steps 4 and 5). -/
def tv4 : TV := ⟨some cfg4, rootRef⟩
/-- Step 4: B's apply without force. -/
def res4 : ApplyRes := apply false sc S3.live tv4 version S3.mf go!"B" false
/-- Step 5: with force. -/
def res5 : ApplyRes := apply false sc S3.live tv4 version S3.mf go!"B" true
def S5 : St := match res5 with | .ok (some o) m => ⟨o, m⟩ | _ => default

/-- Steps 6, 7 (`state.apply`). -/
def r6 : Option (St × Bool) := stApply S5 cfg6 go!"A"
def S6 : St := stOf r6
def r7a : Option (St × Bool) := stApply S6 cfg7a go!"B"
def S7a : St := stOf r7a
def r7b : Option (St × Bool) := stApply S7a cfg7b go!"A"
def S7b : St := stOf r7b

/-- Step 8: C's update with `obj8` typed. -/
def tv8 : TV := ⟨some obj8, rootRef⟩
def res8 : UpdateRes := updateObj sc S7b.live tv8 version S7b.mf go!"C"
def S8 : St := match res8 with | .ok m => ⟨tv8, m⟩ | _ => default

/-- Step 9 (`state.apply`). -/
def r9 : Option (St × Bool) := stApply S8 cfg9 go!"A"
def S9 : St := stOf r9

/-! ## The facts, decided by the kernel -/

/-- The states the steps start from are `stOk`, and the schema's lists' keys are distinct. -/
theorem states_ok : stOk S0 && stOk S1 && stOk S2 && stOk S3 && stOk S5 && stOk S6 && stOk S7a &&
    stOk S7b && stOk S8 && sc.keysNodup = true := by decide +kernel

/-- The objects the driver types validate (`typedObj` does not panic). -/
theorem typed_ok : (stTyped obj0).isSome && (stTyped cfg1).isSome && (stTyped cfg2).isSome &&
    (stTyped cfg3).isSome && (stTyped cfg4).isSome && (stTyped cfg6).isSome &&
    (stTyped cfg7a).isSome && (stTyped cfg7b).isSome && (stTyped obj8).isSome &&
    (stTyped cfg9).isSome = true := by decide +kernel

theorem r1_eq : r1 = some (S1, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check1 : stCheck S1 cfg1 mf1 = true := by decide +kernel
theorem r2_eq : r2 = some (S2, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check2 : stCheck S2 obj2 mf2 = true := by decide +kernel
/-- Step 3's apply is a no-op: `Apply` returns a nil object, `state.apply` returns `false`. -/
theorem r3_eq : r3 = some (S3, false) := eq_some_of_check _ _ (by decide +kernel)
theorem check3 : stCheck S3 obj2 mf3 = true := by decide +kernel

/-- Step 4: a conflict, with A on `.replicas` alone. -/
theorem res4_conflicts : (match res4 with
    | .conflicts [c] => conflictsEquals (conflictsOf [c]) conflicts4
    | _ => false) = true := by decide +kernel
/-- The state is unchanged by step 4 (as step 3 left it). -/
theorem check4 : stCheck S3 obj2 mf3 = true := check3

theorem res5_ok : (match res5 with | .ok (some _) _ => true | _ => false) = true := by decide +kernel
theorem check5 : stCheck S5 obj5 mf5 = true := by decide +kernel
theorem r6_eq : r6 = some (S6, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check6 : stCheck S6 obj6 mf6 = true := by decide +kernel
theorem r7a_eq : r7a = some (S7a, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check7a : stCheck S7a obj7a mf7a = true := by decide +kernel
theorem r7b_eq : r7b = some (S7b, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check7b : stCheck S7b obj7b mf7b = true := by decide +kernel
theorem res8_ok : (match res8 with | .ok _ => true | _ => false) = true := by decide +kernel
theorem check8 : stCheck S8 obj8 mf8 = true := by decide +kernel
theorem r9_eq : r9 = some (S9, true) := eq_some_of_check _ _ (by decide +kernel)
theorem check9 : stCheck S9 obj9 mf8 = true := by decide +kernel

/-! ## More of the Go run, checked on the model -/

/-- After step 7, B's `b1` comes before A's `a2` (A's `a1` was replaced in place by `a2`, which
the merge puts after the items of the live list it does not have: `[b1, a2]`). -/
example : (match S7b.live.value with
    | some (.map kvs) => match lookupKV go!"containers" kvs with
      | some (.list [c1, c2]) => UVal.equals c1 (container go!"b1" go!"y") &&
          UVal.equals c2 (container go!"a2" go!"z")
      | _ => false
    | _ => false) = true := by decide +kernel

/-- Step 3's no-op: the model's `Apply` returns no object (`ReturnInputOnNoop` false), and with
`ReturnInputOnNoop` it would return the merged one. -/
example : (match stTyped cfg3 with
    | some c => (match apply false sc S2.live c version S2.mf go!"B" false with
        | .ok none _ => true | _ => false) &&
      (match apply true sc S2.live c version S2.mf go!"B" false with
        | .ok (some _) _ => true | _ => false)
    | none => false) = true := by decide +kernel

/-- Step 4's conflict leaves nothing to the managers (Go: an empty, non-nil `ManagedFields`), and a
forced apply of the same configuration succeeds. -/
example : (match res4, res5 with | .conflicts _, .ok (some _) _ => true | _, _ => false) = true := by
  decide +kernel

end k8s_smd
end EtcdGrove
end Perennial
