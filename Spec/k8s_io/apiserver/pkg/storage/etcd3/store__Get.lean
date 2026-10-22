/-
`(*store).Get(ctx, key, opts, out)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

A linearizable read: the store reads the key through its client (`kubernetes.Client.Get`, at the
latest revision), with the caller's persistent read update at each member (D30h: a read may fire
at several). Its answer is `correctness.Model`'s `get` (`KSt.get`) at the state `σ` the update
fired at (`□ Q σ`), as the error and object it leaves (`respIs`): the object at its mod revision,
the zero object (`IgnoreNotFound`), or a `*StorageError` "not found" at the state's revision. Or
an error of the client, the object `out` holding something.

The caller's update gives a state that is the store's (`Q σ ⊢ kvWf c σ`: every value under the
prefix decodes, D30i), so decoding never fails. For now the key is valid (`PrepareKey` succeeds:
the model's `checkKey`), and `opts.ResourceVersion` is `""` (no minimum: a minimum's check builds
its error through apimachinery's names-only `NewTimeoutError`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
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
abbrev store.Get.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : k8s_io.apiserver.pkg.storage.GetOptions) (out : GoInterface) (o0 : Obj) (rv0 : GoString)
    (k : GoString) (Q : KVState → IProp GF),
  prepareKeyM c.resourcePrefix key false = some k →
  opts.ResourceVersion' = [] →
  (∀ σ, Q σ ⊢ ⌜kvWf c σ⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt out o0 rv0 ∗
      □ ([∧list] x ∈ c.ms, kvReadAu x.γr.kv Q) }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Get")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts)) (Val #out))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv, c.S.objAt out o rv) ∨
      (∃ σ : KVState, □ Q σ ∗
        respIs (E := Empty) c ((c.abs σ).get (c.pathPrefix ++ k) 0 opts.IgnoreNotFound') err out) }}

end spec

end k8s
end EtcdGrove
end Perennial
