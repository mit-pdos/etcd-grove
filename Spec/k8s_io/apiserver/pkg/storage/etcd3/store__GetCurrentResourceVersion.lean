/-
`(*store).GetCurrentResourceVersion(ctx)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`), the
watch cache's `getCurrentRV` (`cacher.go`, `config.Storage.GetCurrentResourceVersion`; KEP-6404,
`notes/kep-6404-plan.md`, step 2). Lean-first (no Rocq counterpart).

A linearizable read of etcd's revision: the store reads its resource prefix through its client
(`kubernetes.Client.Get`, at the latest revision), with the caller's persistent read updates as
`store.Get`'s, and returns the revision of the state `σ` the update for `σ`'s pair fired at
(`□ Q (W64 σ.rev) (modAt k σ) σ`), not `0` (a `0` is an error); or an error (the client's, or
the revision's). The caller's `Q` gives what it needs of `σ`: for the cached GET, that its
revision is at least etcd's at the call's start (the update fires within the call). For now the
resource prefix is a valid key (`PrepareKey` succeeds, as `store.Get`'s premise).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.GetCurrentResourceVersion.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (k : GoString) (Q : w64 → w64 → KVState → IProp GF),
  prepareKeyM c.resourcePrefix c.resourcePrefix false = some k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R m, |==> □ [∧list] x ∈ c.ms, ⌜Q R m = fun _ => iprop(True)⌝ ∨
        kvReadAu x.γr.kv (Q R m)) }}
    (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"GetCurrentResourceVersion"))
      (Val #(GoInterface.ok ci)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState,
        □ Q (W64 (σ.rev : Int)) (kubernetes.modAt (c.pathPrefix ++ k) σ) σ ∗
        ⌜n = W64 (σ.rev : Int) ∧ 0 < σ.rev⌝) }}

end spec

end k8s
end EtcdGrove
end Perennial
