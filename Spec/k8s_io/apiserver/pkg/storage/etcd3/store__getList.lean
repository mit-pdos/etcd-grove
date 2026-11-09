/-
`(*store).getList(ctx, keyPrefix, recursive, options)` (`k8s.io/apiserver/pkg/storage/etcd3/
store.go:1081-1115`): recursive, the client's `List` (`Client.List.spec`, a hypothesis until 7e-1);
not, its `Get` at the revision (`Client.GetAt.spec`, until 7c-3), the key-value in a fresh
one-element slice (`Count` 1) or none (`Count` 0); the request metric; the size estimator under
`collectorMux.RLock` (`nil`, so `stats.Update` is not called). The answer is a page of the state
`σ` the read update fired at (`listRespIs`), or a failed read's error (`readErrIs`). Proved (stage
7e-2, `notes/k8s-7e-2-draft.md` §3.5). Lean-first (no Rocq counterpart).
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
abbrev store.getList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (kp : GoString) (recur : Bool)
    (lo : go_etcd_io.etcd.client.v3.kubernetes.ListOptions) (Q : w64 → KVState → IProp GF),
  kp.length ≤ opKeyMax → lo.Continue'.length ≤ opKeyMax → 0 ≤ sint.Z lo.Revision' →
  0 ≤ sint.Z lo.Limit' → (recur = false → lo.Continue' = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"getList")) (Val #(GoInterface.ok ci)))
      (Val #kp)) (Val #recur)) (Val #lo))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface),
      RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
          ⌜σ.readRev lo.Revision' ≤ σ.rev⌝ ∗
          listRespIs resp σ kp recur lo.Revision' lo.Limit'
            (if lo.Continue' = [] then kp else lo.Continue')) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ readErrIs c lo.Revision' Q err)) }}

end spec

end k8s
end EtcdGrove
end Perennial
