/-
`(*store).Create(ctx, key, obj, out, 0)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

A write, fired at most once (D30h's one-shot part): the store encodes the object (after clearing
its resource version), transforms it for storage and sends `OptimisticPut(key, value, 0)` through
its client, with the caller's relational update at each member (`k8sAu1`: the next state's model
is `correctness.Model`'s `create`). Its answer is the model's at the state `σ` the update fired at
(`Φ σ`), as the error and object it leaves (`respIs`): the object at the new revision, or a
`*StorageError` "key exists". Or an error, the update fired at most once (the client's, or an
encoding or transformation failure before anything was sent).

For now the key is valid, the object has no resource version (`ErrResourceVersionSetOnCreate`
otherwise: a package variable's value), and no lease (`ttl = 0`, D30d).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates
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
abbrev store.Create.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (obj : GoInterface) (o : Obj)
    (rv : GoString) (out : GoInterface) (o0 : Obj) (rv0 : GoString) (k : GoString)
    (Φ : KVState → IProp GF),
  prepareKeyM c.resourcePrefix key false = some k →
  (c.pathPrefix ++ k).length ≤ 2 ^ 27 →
  c.S.storedSizeOk o →
  c.S.parseRV rv = some (W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt obj o rv ∗ c.S.objAt out o0 rv0 ∗
      ([∧list] x ∈ c.ms, k8sAu1 x.γr.kv c
        (fun s => (s.create (E := Empty) (c.pathPrefix ++ k) o 0).1) Φ) }}
    (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Create")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #obj)) (Val #out)) (Val #(W64 0)))
  {{ (err : GoInterface), RET #err; (∃ o' rv', c.S.objAt obj o' rv') ∗
      ((unkErr c err ∗ ∃ o' rv', c.S.objAt out o' rv') ∨
        (∃ σ : KVState, Φ σ ∗
          respIs (E := Empty) c ((c.abs σ).create (c.pathPrefix ++ k) o 0).2 err out)) }}

end spec

end k8s
end EtcdGrove
end Perennial
