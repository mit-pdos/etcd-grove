/-
`(*store).updateOnce(ctx, span, key, destination, origState, data, 0, v, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

One attempt at writing `tryUpdate`'s result `o'` (`data`, its encoding) at the prepared key `key`,
as `deleteOnce` (D30l): the transformer's value for `data`, then `OptimisticPut(key, value,
origState.rev, GetOnFailure: true)` through the client with the caller's updates at the members
(`k8sAuRW`, D30n, the model's `update` as the write). `origState` is the store's reading `s` of the
key-value `kv0` at a state `σ0` the caller's read fired at, on which `tryUpdate` gave `o'`, and
the store did not skip the write (`o'` and `s` are not unchanged and canonical). Its outcomes:

- an error (the transformer's, or the client's: the update fired at most once);
- success: the write at `σ`, `destination` the result at the new revision (`respIs`);
- a conflict: a read at the state `σ` the transaction saw (`W` back), and the store's reading of
  the key there (`stAt`).

No TTL (D30d), and `ignoreNotFound` false.
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
abbrev store.updateOnce.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (span : Loc) (key : GoString) (dest : GoInterface)
    (o0 : Obj) (rv0 : GoString) (st : Loc) (s : OState Obj) (x : GoInterface) (dsl : GoSlice)
    (σ0 : KVState) (kv0 : EtcdKv) (v : _root_.Perennial.reflect.Value) (p : Loc) (z : Obj)
    (f : Obj → Nat → Except E Obj) (o' : Obj) (W : IProp GF) (Φ : KVState → IProp GF),
  c.pfx <+: key →
  mvcc.findKey key σ0.kvs = some kv0 →
  stOfKv c kv0 s →
  f s.o (uint.nat s.rev) = .ok o' →
  (!s.stale && decide (c.S.encode o' = s.data)) = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ⌜span ≠ null⌝ ∗ ownStateX c st s x ∗
      dsl ↦*□ c.S.encode o' ∗ c.S.objAt dest o0 rv0 ∗ ⌜reflectM.reflElem v c.S.objTy p⌝ ∗
      rdFacts c σ0 ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (updStep key z f) W Φ) }}
    (App (App (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"updateOnce")) (Val #(GoInterface.ok ci)))
      (Val #span)) (Val #key)) (Val #dest)) (Val #st)) (Val #dsl)) (Val #(W64 0))) (Val #v))
      (Val #false))
  {{ (st' : Loc) (ok : Bool) (err : GoInterface), RET (PairV (PairV #st' #ok) #err);
      (unkErr c err ∗ ∃ o rv, c.S.objAt dest o rv) ∨
      (⌜ok = true ∧ err = GoInterface.nil⌝ ∗ ∃ σ, Φ σ ∗
        respIs c ((c.abs σ).update key false z (fun _ _ => none) f).2 err dest) ∨
      (⌜ok = false⌝ ∗ c.S.objAt dest o0 rv0 ∗ ∃ σ, rdFacts c σ ∗ stAt c key σ st' err ∗
        (if stepHand c (updStep key z f) σ then Φ σ else W)) }}

end spec

end k8s
end EtcdGrove
end Perennial
