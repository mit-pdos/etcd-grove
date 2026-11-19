/-
**The driver's nine steps, computed** (`examples/k8s/smd/smd.go`, `Main`): each `Apply`'s outcome
(`applyResult`) and the `Update`'s managers (`updateResult`) on the driver's literal inputs, proved
equal to the object, managed fields and conflicts the driver checks, by `decide` (the kernel's
evaluation of the API's computable vocabulary; no `native_decide`). With the specs of
`Updater.Apply`/`Updater.Update` (their posts are these functions), these are the facts `Main`'s
proof needs at each `check`; their hand derivation is `notes/smd-plan.md`, "Sanity checks".

The premises the specs take at each step are decided here too: the schema is in scope
(`sc0_wf`), every literal object conforms (`conforms_*`), and the managed fields before each
`Apply` keep list items with their key fields (`kwi_*`, by `keysWithItemsB`; `Main` gets the
`keysWithItems` premise itself from `applyResult_premise`/`updateResult_premise`).

Review round 1 (2026-11-19), P1: the completeness test of the computable vocabulary.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Scenario

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open smd

/-! ## The literals (in the driver's order) -/

def A : GoString := go!"A"
def B : GoString := go!"B"
def C : GoString := go!"C"

def labels (kvs : List (GoString × UVal)) : UVal := UVal.ofMap kvs
def sel (kvs : List (GoString × UVal)) : UVal := UVal.ofMap kvs
def i64 (n : Nat) : UVal := .int (BitVec.ofNat 64 n)

def obj1 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 1),
  (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels [(go!"app", str go!"web")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def aPaths1 : List Path :=
  [field go!"name", field go!"image", field go!"replicas", mapKey go!"labels" go!"app",
    field go!"selector"] ++ containerPaths go!"a1"
def mf1 : MF := MF.ofList [(A, applied aPaths1)]

def cfg2 : UVal := UVal.ofMap [(go!"labels", labels [(go!"team", str go!"t")])]
def obj2 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 1),
  (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels [(go!"app", str go!"web"), (go!"team", str go!"t")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def mf2 : MF := MF.ofList [(A, applied aPaths1), (B, applied [mapKey go!"labels" go!"team"])]

def cfg3 : UVal := UVal.ofMap [(go!"image", str go!"img1"), (go!"labels", labels [(go!"team", str go!"t")])]
def mf3 : MF := MF.ofList [(A, applied aPaths1),
  (B, applied [field go!"image", mapKey go!"labels" go!"team"])]

def cfg4 : UVal := UVal.ofMap [(go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"labels", labels [(go!"team", str go!"t")])]
def conflicts4 : FSet (GoString × Path) := FSet.ofList [(A, field go!"replicas")]

def obj5 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels [(go!"app", str go!"web"), (go!"team", str go!"t")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def aPaths5 : List Path :=
  [field go!"name", field go!"image", mapKey go!"labels" go!"app", field go!"selector"] ++
    containerPaths go!"a1"
def bPaths5 : List Path := [field go!"image", field go!"replicas", mapKey go!"labels" go!"team"]
def mf5 : MF := MF.ofList [(A, applied aPaths5), (B, applied bPaths5)]

def cfg6 : UVal := UVal.ofMap [(go!"name", str go!"obj"),
  (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def obj6 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"containers", .list [container go!"a1" go!"x"]),
  (go!"labels", labels [(go!"team", str go!"t")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def aPaths6 : List Path := [field go!"name", field go!"selector"] ++ containerPaths go!"a1"
def mf6 : MF := MF.ofList [(A, applied aPaths6), (B, applied bPaths5)]

def cfg7a : UVal := UVal.ofMap [(go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"containers", .list [container go!"b1" go!"y"]), (go!"labels", labels [(go!"team", str go!"t")])]
def obj7a : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"containers", .list [container go!"a1" go!"x", container go!"b1" go!"y"]),
  (go!"labels", labels [(go!"team", str go!"t")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def bPaths7 : List Path := bPaths5 ++ containerPaths go!"b1"
def mf7a : MF := MF.ofList [(A, applied aPaths6), (B, applied bPaths7)]

def cfg7b : UVal := UVal.ofMap [(go!"name", str go!"obj"),
  (go!"containers", .list [container go!"a2" go!"z"]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def obj7b : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 2),
  (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", labels [(go!"team", str go!"t")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def aPaths7 : List Path := [field go!"name", field go!"selector"] ++ containerPaths go!"a2"
def mf7b : MF := MF.ofList [(A, applied aPaths7), (B, applied bPaths7)]

def obj8 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 3),
  (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", labels [(go!"team", str go!"t"), (go!"env", str go!"prod")]),
  (go!"selector", sel [(go!"k", str go!"v1"), (go!"m", str go!"x")])]
def bPaths8 : List Path := [field go!"image", mapKey go!"labels" go!"team"] ++ containerPaths go!"b1"
def mf8 : MF := MF.ofList [(A, applied aPaths7), (B, applied bPaths8),
  (C, updated [field go!"replicas", mapKey go!"labels" go!"env"])]

def cfg9 : UVal := UVal.ofMap [(go!"name", str go!"obj"),
  (go!"containers", .list [container go!"a2" go!"z"]), (go!"selector", sel [(go!"k", str go!"v2")])]
def obj9 : UVal := UVal.ofMap [
  (go!"name", str go!"obj"), (go!"image", str go!"img1"), (go!"replicas", i64 3),
  (go!"containers", .list [container go!"b1" go!"y", container go!"a2" go!"z"]),
  (go!"labels", labels [(go!"team", str go!"t"), (go!"env", str go!"prod")]),
  (go!"selector", sel [(go!"k", str go!"v2")])]

/-! ## The steps -/

/-- 1. A creates the object by `Apply`. -/
theorem step1 :
    applyResult sc0 rootRef false (UVal.ofMap []) obj1 version MF.none A false =
      .ok (some obj1) mf1 := by
  decide +kernel

/-- 2. B applies a disjoint field. -/
theorem step2 : applyResult sc0 rootRef false obj1 cfg2 version mf1 B false = .ok (some obj2) mf2 := by
  decide +kernel

/-- 3. B applies the value A has for image: no change (`nil` object), both own it. -/
theorem step3 : applyResult sc0 rootRef false obj2 cfg3 version mf2 B false = .ok none mf3 := by
  decide +kernel

/-- 4. B applies another replicas, not forced: a conflict with A on replicas, nothing else. -/
theorem step4 :
    applyResult sc0 rootRef false obj2 cfg4 version mf3 B false = .conflicts conflicts4 := by
  decide +kernel

/-- 5. The same, forced. -/
theorem step5 : applyResult sc0 rootRef false obj2 cfg4 version mf3 B true = .ok (some obj5) mf5 := by
  decide +kernel

/-- 6. A applies again without labels.app (pruned) and image (kept: B owns it). -/
theorem step6 : applyResult sc0 rootRef false obj5 cfg6 version mf5 A false = .ok (some obj6) mf6 := by
  decide +kernel

/-- 7. B adds a list item. -/
theorem step7a :
    applyResult sc0 rootRef false obj6 cfg7a version mf6 B false = .ok (some obj7a) mf7a := by
  decide +kernel

/-- 7. A replaces its item `a1` by `a2`: only `a1` goes, in the order `[b1, a2]`. -/
theorem step7b :
    applyResult sc0 rootRef false obj7a cfg7b version mf7a A false = .ok (some obj7b) mf7b := by
  decide +kernel

/-- 8. C updates replicas and adds labels.env (`Update` returns `obj8` itself). -/
theorem step8 : updateResult sc0 rootRef obj7b obj8 version mf7b C = mf8 := by
  decide +kernel

/-- 9. A changes the atomic selector: replaced whole, managers unchanged. -/
theorem step9 : applyResult sc0 rootRef false obj8 cfg9 version mf8 A false = .ok (some obj9) mf8 := by
  decide +kernel

/-! ## The specs' premises at each step -/

/-- The scenario's schema is in scope. -/
theorem sc0_wf : sc0.WF := by decide +kernel

/-- Every object the driver types conforms to `root`. -/
theorem conforms_all : ∀ x ∈ [UVal.ofMap [], obj1, cfg2, cfg3, cfg4, cfg6, cfg7a, cfg7b, obj8, cfg9],
    conforms sc0 rootRef x := by
  decide +kernel

/-- Every managed field set before an `Apply` keeps items with their key fields (and nothing below
a key field), decided. -/
theorem kwi_all : ∀ mf ∈ [mf1, mf2, mf3, mf5, mf6, mf7a, mf8],
    ∀ me ∈ mf, keysWithItemsB sc0 rootRef me.2.set = true := by
  decide +kernel

/-- One API version (`Apply`'s premise, `notes/smd-plan.md`, "Scope"): every manager's entry is at
`version` before each `Apply` (the Draft's integration, 2026-11-19). -/
theorem version_all : ∀ mf ∈ [MF.none, mf1, mf2, mf3, mf5, mf6, mf7a, mf8],
    ∀ me ∈ mf, me.2.version = version := by
  decide +kernel

/-- **D9's workload premise** (`inputsSmall`, `merge/Defs.lean`) at every `Apply` (steps 1-7b and
9) and at the `Update` of step 8: the objects' sizes and the managers' trie nodes below
`smdSizeMax` (the Draft's integration, 2026-11-19). -/
theorem small_all :
    inputsSmall [UVal.ofMap [], obj1] MF.none ∧ inputsSmall [obj1, cfg2] mf1 ∧
    inputsSmall [obj2, cfg3] mf2 ∧ inputsSmall [obj2, cfg4] mf3 ∧ inputsSmall [obj5, cfg6] mf5 ∧
    inputsSmall [obj6, cfg7a] mf6 ∧ inputsSmall [obj7a, cfg7b] mf7a ∧
    inputsSmall [obj7b, obj8] mf7b ∧ inputsSmall [obj8, cfg9] mf8 := by
  decide +kernel

end k8s_smd
end EtcdGrove
end Perennial
