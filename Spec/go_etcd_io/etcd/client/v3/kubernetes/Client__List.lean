/-
`kubernetes.Client.List(ctx, prefix, opts)` (`client/v3/kubernetes/client.go:59-73`), as the store's
list path consumes it (`notes/k8s-7e-2-draft.md` §7, #16): a range `[prefix, GetPrefixRangeEnd
prefix)` from the continue key (or the prefix) at `opts.Revision` (`0`: the latest) with limit
`opts.Limit`, through `New`'s client of the members, with a read update or none at each member.
The answer is about the state `σ` the update fired at: its revision is the response's, the page
of `σ`'s store at the read revision (`listRespIs`; the `Kvs` slice owned: `appendChunk` writes it);
an error is the client's, with the future-revision soundness (`rangeErrSound`) for a non-empty
prefix on members that refuse no request (`noRefusalAt`; k8s 7e-1). The continue key is
none or has the prefix (review of 2026-11-10, which refuted the statement without this premise: the
client reads the raw range `[Continue, GetPrefixRangeEnd prefix)`, so a key below the prefix returns
and counts keys outside it; the store's continue keys are `DecodeContinue`'s `keyPrefix ++ ...` and
`pagedChunks`' last key and `"\x00"`).

**A hypothesis** until 7e-1 (a premise of `store.getList`'s proof only, never an axiom; decided by
etcd-grove-81). Requirements on 7e-1 recorded in the Draft §7 (owned `Kvs`, `Count` from the range
start, the error's soundness, `len(Kvs) ≤ 2 ^ 41`). It is stated with the store's vocabulary
(`listRespIs`, `rangeErrSound`, `Proof/k8s_io/apiserver/pkg/storage/etcd3/ListDefs.lean`), which 7e-1
moves down. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import GeneratedProof.go_etcd_io.etcd.client.v3.kubernetes

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
abbrev Client.List.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ms : List (client.SrvAt GF)) (V : client.WEnv GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (pfx : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.ListOptions) (Q : w64 → KVState → IProp GF),
  pfx.length ≤ opKeyMax → opts.Continue'.length ≤ opKeyMax →
  0 ≤ sint.Z opts.Revision' → 0 ≤ sint.Z opts.Limit' → (opts.Continue' = [] ∨ pfx <+: opts.Continue') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R, |==> □ [∧list] x ∈ ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"List"))
      (Val #(GoInterface.ok ci))) (Val #pfx)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
        ⌜σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev⌝ ∗
        listRespIs resp σ pfx true opts.Revision' opts.Limit'
          (if opts.Continue' = [] then pfx else opts.Continue')) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err ∗
        (⌜pfx ≠ [] ∧ ∀ x ∈ ms, noRefusalAt x.addr⌝ → rangeErrSound opts.Revision' Q err)) }}

end spec

end kubernetes
end EtcdGrove
end Perennial
