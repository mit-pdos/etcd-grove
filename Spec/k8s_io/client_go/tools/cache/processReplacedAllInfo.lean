/-
`processReplacedAllInfo(logger, handler, info, clientState, isInInitialList, keyFunc)`
(`controller.go:993`): a relist's `ReplacedAll` delta applied to the store, then its events.
Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.reconcileReplacement

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- A relist's events at the items `it`: a deletion of each key of `dks` (its tombstone), then an
update or add of each new object (`putEvR`). -/
def replacedEvs [FfiSyntax] [GoGlobalContext] (KF : GoInterface → GoString) (b : Bool) (it : Items)
    (dks : List GoString) (objs : List GoInterface) : List Ev :=
  dks.map (fun k => Ev.delete (tombstone k (objAt it k))) ++
    objs.map (fun x => putEvR it (KF x) x b)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`processReplacedAllInfo(lg, h, {rv, isl}, ca, b, kf')`**, the store `ca` held by its
exclusive writer at `σ`, a relist of the objects `objs` (meeting `OK`) at version `rv`, keyed by
the cache's key function `kf` and by `kf'` alike (`KF`): the store becomes
`σ.replace (keyedItems KF objs) rv` (one atomic `Replace`), then the handler gets a deletion for
each store key the relist lacks (`delKeys`, in some order), then an update or add for each listed
object, in order (`replacedEvs`). -/
abbrev processReplacedAllInfo.spec : Prop :=
  ∀ (lg : github_com.go_logr.logr.Logger) (h : GoInterface) (ca ts : Loc) (γ : TsNames)
    (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (kf kf' : GoFunc)
    (KF : GoInterface → GoString) (SW : St → IProp GF) (σ : St) (H : List Ev → IProp GF)
    (evs : List Ev) (rv : GoString) (isl : GoSlice) (objs : List GoInterface) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ storeWriter γ SW ∗ SW σ ∗ handlerOk OK h H ∗ H evs ∗
      isl ↦* objs ∗ □ ([∗list] x ∈ objs, OK x) ∗
      keyOk (fun x => iprop(⌜x ∈ objs⌝)) kf KF ∗ keyOk (fun x => iprop(⌜x ∈ objs⌝)) kf' KF }}
    (App (App (App (App (App (App (Val (@! processReplacedAllInfo)) (Val #lg)) (Val #h))
      (Val #(ReplacedAllInfo.mk rv isl)))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #b)) (Val #kf'))
  {{ RET #interface.nil; ∃ dks : List GoString, ⌜delKeys KF σ.items objs dks⌝ ∗
      SW (σ.replace (keyedItems KF objs) rv) ∗ H (evs ++ replacedEvs KF b σ.items dks objs) ∗
      isl ↦* objs ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
