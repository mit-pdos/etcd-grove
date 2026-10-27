/-
`(*store).GuaranteedUpdate(ctx, key, destination, false, nil, tryUpdate, nil)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

An update, retried on conflicts: with the caller's updates at the members (`k8sAuRW`, D30n:
persistent, firing as a plain read any number of times, and once as the linearization point,
handing the caller's timeless token `W` back), its outcome is `correctness.Model`'s `update` with
the canonical bit (D30g, `updOut`): at the state the update fired at as the linearization point
(`Φ σ`): the write (`destination` the result at the new revision), or a read-like answer (the no-op
of an unchanged canonical object, "not found", `tryUpdate`'s error, nothing changed); or an error
(the client's, or the codec's or transformer's). `tryUpdate` is the
caller's callback, answering `f` (`tryUpdateOk`).

For now the key is valid, `ignoreNotFound` is false, and there are no preconditions and no cached
object; `tryUpdate` sets no TTL (D30d).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps
public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.GuaranteedUpdate.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (dest : GoInterface) (o0 : Obj)
    (rv0 : GoString) (f : Obj → Nat → Except E Obj) (uf : GoFunc) (W : IProp GF)
    [Timeless W] (Φ : KVState → IProp GF) (k : GoString),
  prepareKeyM c.resourcePrefix key false = some k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt dest o0 rv0 ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (updStep (c.pathPrefix ++ k) c.S.zero f) W Φ) ∗
      tryUpdateOk c f uf }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"GuaranteedUpdate"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #dest)) (Val #false)) (Val #null)) (Val #uf))
      (Val #GoInterface.nil))
  {{ (err : GoInterface), RET #err; updOut c (c.pathPrefix ++ k) c.S.zero f Φ err dest }}

end spec

end k8s
end EtcdGrove
end Perennial
