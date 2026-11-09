/-
`(*store).listReadError(ctx, err, withRev, false, continueKey, keyPrefix)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:922-934`) of a failed read's error (`readErrIs`): a
future revision (`errors.Is(err, rpctypes.ErrFutureRev)`, by the descriptions) gives
`NewTooLargeResourceVersionError` (`tooLargeErrIs`), with the state `Q` fired at below `withRev`;
anything else `interpretListError`'s (`listErr`). The current resource version it reads for the
message is not used (`GetCurrentResourceVersion` with the trivial update). Proved (stage 7e-2,
`notes/k8s-7e-2-draft.md` §3.5; the resource prefix's key is the one `GetCurrentResourceVersion`
needs, a form settled at Prove). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.listReadError.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (withRev : w64) (ck kp : GoString)
    (Q : w64 → KVState → IProp GF),
  (∃ k, prepareKeyM c.resourcePrefix c.resourcePrefix false = some k ∧
    (c.pathPrefix ++ k).length ≤ opKeyMax) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ readErrIs c withRev Q err }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"listReadError")) (Val #(GoInterface.ok ci)))
      (Val #err)) (Val #withRev)) (Val #false)) (Val #ck)) (Val #kp))
  {{ (e : GoInterface), RET #e;
      (apierrors.tooLargeErrIs e ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
        ⌜σ.rev < sint.nat withRev⌝) ∨ listErr c e }}

end spec

end k8s
end EtcdGrove
end Perennial
