/-
`(*store).getCurrentState(ctx, verb, key, v, false, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

A closure (`getStateOk`) that reads the prepared key `key` through the store's client with the
caller's persistent read update at each member (`R`, whose states are the store's), and answers
the store's reading of its key-value (`stateFromEtcdResponse`), at the state the update fired at.
For now `ignoreNotFound` and `expectTransformOrDecodeError` are `false` (`Delete`'s).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.State

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
abbrev store.getCurrentState.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (verb key : GoString)
    (v : _root_.Perennial.reflect.Value) (p : Loc) (R : KVState → IProp GF),
  c.pfx <+: key →
  (∀ σ, R σ ⊢ ⌜kvWf c σ⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ⌜reflectM.reflElem v c.S.objTy p⌝ ∗
      □ ([∧list] x ∈ c.ms, kvReadAu x.γr.kv R) }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"getCurrentState"))
      (Val #(GoInterface.ok ci))) (Val #verb)) (Val #key)) (Val #v)) (Val #false)) (Val #false))
  {{ (f : GoFunc), RET #f; getStateOk c key R f }}

end spec

end k8s
end EtcdGrove
end Perennial
