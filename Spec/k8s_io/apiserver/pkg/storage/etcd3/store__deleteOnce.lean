/-
`(*store).deleteOnce(ctx, key, out, origState, v, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

One attempt at deleting the prepared key `key`: `OptimisticDelete(key, origState.rev,
GetOnFailure: true)` through the client, with the caller's updates at the members (`k8sAuRW`, D30h
as carried out: the model's `delete` as the write, `W` the caller's token) and `origState` the
store's reading `s` of the key-value `kv0` at a state `σ0` the caller's read fired at (`rdOk`),
which `validateDeletion` passed (`validate`). A key-value at `s`'s mod revision has `kv0`'s value
(the caller's history, D30j), so the transaction is the model's `delete` when it succeeds. Its
outcomes:

- an error of the client (the update fired at most once);
- success: the update fired as the write at `σ`, `out` the deleted object at the next revision (the
  model's answer, `respIs`);
- a conflict: the update fired as a read at the state `σ` the transaction saw (`W` back), and the
  new state is the store's reading of the key there (`stAt`: "not found", or its key-value).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

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
abbrev store.deleteOnce.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (out : GoInterface) (o0 : Obj)
    (rv0 : GoString) (st : Loc) (s : OState Obj) (σ0 : KVState) (kv0 : EtcdKv)
    (v : _root_.Perennial.reflect.Value) (p : Loc) (validate : Obj → Nat → Option E)
    (W : IProp GF) (Q Φ : KVState → IProp GF),
  c.pfx <+: key →
  mvcc.findKey key σ0.kvs = some kv0 →
  stOfKv c kv0 s →
  validate s.o (uint.nat s.rev) = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ownState c st s ∗ c.S.objAt out o0 rv0 ∗
      ⌜reflectM.reflElem v c.S.objTy p⌝ ∗ rdOk c Q σ0 ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (delStep key validate) W Q Φ) }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"deleteOnce")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #out)) (Val #st)) (Val #v)) (Val #false))
  {{ (st' : Loc) (ok : Bool) (err : GoInterface), RET (PairV (PairV #st' #ok) #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv, c.S.objAt out o rv) ∨
      (⌜ok = true⌝ ∗ ∃ σ, Φ σ ∗
        respIs c ((c.abs σ).delete key (fun _ _ => none) validate).2 err out) ∨
      (⌜ok = false⌝ ∗ W ∗ c.S.objAt out o0 rv0 ∗ ∃ σ, rdOk c Q σ ∗ stAt c key σ st' err) }}

end spec

end k8s
end EtcdGrove
end Perennial
