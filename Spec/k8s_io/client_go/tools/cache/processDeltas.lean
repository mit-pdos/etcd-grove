/-
`processDeltas(logger, handler, clientState, deltas, isInInitialList, keyFunc)`
(`controller.go:823`) on the one delta the atomic FIFO's `Pop` hands its processing function: the
delta applied to the store, then the handler's events. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processReplacedAllInfo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`processDeltas(lg, h, ca, Deltas{v}, b, kf')`**, the store `ca` held by its exclusive writer
at `σ`, for one queued delta `d` (the Go delta `v`, `fdAt`) of a kind the atomic FIFO queues, its
objects keyed by the cache's key function `kf` and by `kf'` alike (`KF`) with versions `rvOf`: no
error; the store's next state and the handler's events are `stepFD`'s (each store write one
atomic operation, before the events: the store reflects a change before any handler hears of
it). -/
abbrev processDeltas.spec : Prop :=
  ∀ (lg : github_com.go_logr.logr.Logger) (h : GoInterface) (ca ts : Loc) (γ : TsNames)
    (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (kf kf' : GoFunc)
    (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (SW : St → IProp GF)
    (σ : St) (H : List Ev → IProp GF) (evs : List Ev) (d : FD) (v : Delta) (sl : GoSlice)
    (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ storeWriter γ SW ∗ SW σ ∗ handlerOk OK h H ∗ H evs ∗
      fdAt OK d v ∗ sl ↦* [v] ∗ ⌜d.kindOk⌝ ∗
      keyOk (fun x => iprop(⌜x ∈ d.objs⌝)) kf KF ∗ keyOk (fun x => iprop(⌜x ∈ d.objs⌝)) kf' KF ∗
      rvAcc (fun x => iprop(⌜x ∈ d.objs⌝)) rvOf }}
    (App (App (App (App (App (App (Val (@! processDeltas)) (Val #lg)) (Val #h))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #sl)) (Val #b)) (Val #kf'))
  {{ RET #interface.nil; ∃ (σ' : St) (evs' : List Ev), ⌜stepFD KF rvOf b σ d σ' evs'⌝ ∗
      SW σ' ∗ H (evs ++ evs') ∗ sl ↦* [v] ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
