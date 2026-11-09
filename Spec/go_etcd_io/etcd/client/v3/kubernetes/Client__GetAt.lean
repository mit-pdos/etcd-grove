/-
`kubernetes.Client.Get(ctx, key, opts)` (`client/v3/kubernetes/client.go:47-57`) at a revision, as
the store's non-recursive list consumes it (`notes/k8s-7e-2-draft.md` §7, #17): the key's key-value
in `σ`'s store at the read revision `σ.readRev opts.Revision` (`kvOut`), the response's revision
`σ`'s, where `σ` is the state the read update fired at; an error is the client's, with the
future-revision soundness (`rangeErrSound`).

**A hypothesis** until 7c-3 (a premise of `store.getList`'s proof only, never an axiom; decided by
etcd-grove-81, B4): 7c-3 restates `Client.Get.spec` without its `opts.Revision' = 0` premise
(`notes/k8s-etcd3-plan.md`), which gives this triple (with `Q` ignoring the prophesied mod
revision). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev Client.GetAt.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ms : List (client.SrvAt GF)) (V : client.WEnv GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.GetOptions) (Q : w64 → KVState → IProp GF),
  key.length ≤ opKeyMax → 0 ≤ sint.Z opts.Revision' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R, |==> □ [∧list] x ∈ ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Get"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
        ⌜resp.Revision' = W64 (σ.rev : Int) ∧ σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev⌝ ∗
        kvOut resp.KV' (mvcc.findKey key (σ.at (σ.readRev opts.Revision')).kvs)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err ∗ rangeErrSound opts.Revision' Q err) }}

end spec

end kubernetes
end EtcdGrove
end Perennial
