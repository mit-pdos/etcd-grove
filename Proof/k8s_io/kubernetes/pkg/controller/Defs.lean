/-
**`pkg/controller`'s vocabulary** (the library's specs; Lean-first, the DaemonSet autoverify run,
track B, 2026-11-04: moved out of `daemon/` so that the library's specs do not import the DaemonSet
controller, review 1's M3).

* `InfLoc`, `infAt γa r I FamN`: an informer's fixed locations and ghost names, and the informer of
  the model API server's resource `r` (track A's `infView`, its index relations by name `FamN`);
* `ctlOf`, `podCtlKey`, `podCtlIndex`, `podCtlIndexed I FamN`: a pod's controller reference
  (`metav1.GetControllerOf`), `PodControllerIndexKey`, and the pod store's controller index
  (`AddPodControllerIndexer`);
* `computeHashD`: `ComputeHash`'s model (uninterpreted);
* `int32PtrD`, `int64PtrD`, `podsAt`, `crsAt`: optional integers behind pointers, lists of cache
  objects (read-only for good).

Still the DaemonSet run's: the claims and the ref managers are stated for a `*DaemonSet` owner,
`FilterPodsByOwner` over the informer's log (review 1's M3, the rest: an owner contract and a
statement over client-go's cache, deferred to the freeze).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs
public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Proof.k8s_io.client_go.tools.cache.InformerInv
public import Proof.k8s_io.client_go.tools.cache.InformerApi

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer cache

section pure
variable [GooseExts]

/-- An informer's fixed locations and ghost names. -/
structure InfLoc where
  ca : Loc
  ts : Loc
  kf : GoFunc
  γf : FifoNames
  γt : TsNames
  γi : InfNames
  res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource

/-- **`metav1.GetControllerOf(pod)`**: the first owner reference with `Controller` set. -/
def ctlOf (p : kd.core.Pod) : Option kd.meta.OwnerReference :=
  p.ObjectMeta'.OwnerReferences'.find? (fun r => decide (r.Controller' = some true))

/-- **`controller.PodControllerIndexKey(ns, ref)`**: the namespace alone for no reference. -/
def podCtlKey (ns : GoString) : Option kd.meta.OwnerReference → GoString
  | none => ns
  | some r => ns ++ go!"/" ++ r.Kind' ++ go!"/" ++ r.Name' ++ go!"/" ++ r.UID'

/-- `controller.PodControllerIndex`. -/
def podCtlIndex : GoString := go!"podController"

/-- A non-empty string (`ComputeHash`'s results: `SafeEncodeString` of a decimal number). -/
abbrev NeStr : Type := {s : GoString // s.length ≠ 0}

instance : Inhabited NeStr := ⟨⟨[(48 : w8)], by simp⟩⟩

/-- **`controller.ComputeHash(template, collisionCount)`**: a function of the template and the
collision count (uninterpreted). -/
opaque computeHashD : kd.core.PodTemplateSpec → Option w32 → NeStr

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An informer's handles as track A's informer API names them (`InfH`). -/
def InfLoc.h (I : InfLoc) : InfH := ⟨I.ca, I.ts, I.kf, I.γf, I.γt, I.γi⟩

/-- **The informer of resource `r`** (persistent): track A's view of it (`infView`: its store
over the informer's registered objects, `infObj`, and the informer invariant), its indices' relations
by name `FamN` (the store's family `famOf FamN`). -/
def infAt (γa : ApiNames) (r : Res) (I : InfLoc) (FamN : GoString → Fn GF) : IProp GF :=
  infView γa r I.h (famOf FamN)

instance infAt_persistent (γa : ApiNames) (r : Res) (I : InfLoc) (FamN : GoString → Fn GF) :
    Persistent (infAt γa r I FamN) := by
  unfold infAt; infer_instance

/-- **The pod store's controller index** (persistent): the index named `podCtlIndex` is registered
(`infIdx`: `AddPodControllerIndexer`, in the constructor), and its relation gives a pod its
`PodControllerIndexKey`. -/
def podCtlIndexed (I : InfLoc) (FamN : GoString → Fn GF) : IProp GF :=
  iprop(infIdx I.h podCtlIndex ∗
    □ (∀ (x : GoInterface) (vs : List GoString) (p : kd.core.Pod),
      apimodel.objAt x DFrac.discard (.pod p) -∗ FamN podCtlIndex x vs -∗
      ⌜vs = [podCtlKey p.ObjectMeta'.Namespace' (ctlOf p)]⌝))

instance podCtlIndexed_persistent (I : InfLoc) (FamN : GoString → Fn GF) :
    Persistent (podCtlIndexed I FamN) := by
  unfold podCtlIndexed; infer_instance

/-- **An `*int64`**: `nil` for `none`, else a pointer to the value (at `dq`). -/
def int64PtrD (p : Loc) (dq : DFrac) (g : Option w64) : IProp GF :=
  ownPtrD (fun (x : w64) (_ : DFrac) (y : w64) => iprop(⌜x = y⌝)) p dq g

/-- **An `*int32`**: `nil` for `none`, else a pointer to the value (at `dq`). -/
def int32PtrD (p : Loc) (dq : DFrac) (g : Option w32) : IProp GF :=
  ownPtrD (fun (x : w32) (_ : DFrac) (y : w32) => iprop(⌜x = y⌝)) p dq g

/-- **A list of pods** (the slice at `dq`, the pods cache objects, read-only for good). -/
def podsAt (pl : GoSlice) (dq : DFrac) (ps : List kd.core.Pod) : IProp GF :=
  iprop(∃ ls : List Loc, pl ↦*{dq} ls ∗ ⌜ls.length = ps.length⌝ ∗
    [∗list] i ↦ p ∈ ls, ∃ d, ⌜ps[i]? = some d⌝ ∗ □ podAt p DFrac.discard d)

/-- **A list of controller revisions** (the slice at `dq`, the revisions read-only for good). -/
def crsAt (hl : GoSlice) (dq : DFrac) (rs : List kd.apps.ControllerRevision) : IProp GF :=
  iprop(∃ ls : List Loc, hl ↦*{dq} ls ∗ ⌜ls.length = rs.length⌝ ∗
    [∗list] i ↦ p ∈ ls, ∃ r, ⌜rs[i]? = some r⌝ ∗ □ crAt p DFrac.discard r)

end defs

end dsctl
end EtcdGrove
end Perennial
