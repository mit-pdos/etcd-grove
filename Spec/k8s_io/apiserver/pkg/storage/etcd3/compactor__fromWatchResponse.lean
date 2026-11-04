/-
`(*compactor).fromWatchResponse(resp)` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`): a
response of the watch loop's watch of the compactors' key (Q1 (b) of
`notes/k8s-compactor-plan.md`; the shapes in `CompactorDefs.lean`). Lean-first (no Rocq
counterpart).

`resp.Err()` (an error response: its error); no event: `0`; else the last event's value parsed
(`ParseInt`, its error on failure). On success the revision is a compaction revision (`recRevOk`):
the response's events hold `keyValOk` values (`respKeyOk`, from the watch's read update).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

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

/-- See the file header. -/
abbrev compactor.fromWatchResponse.spec : Prop :=
  ∀ (c : Loc) (γk : KVNames) (recorded : w64 → IProp GF)
    (v : go_etcd_io.etcd.client.v3.WatchResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      respKeyOk γk recorded v }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"fromWatchResponse")) (Val #v))
  {{ (cr : w64) (err : GoInterface), RET (PairV #cr #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ recRevOk γk recorded cr) }}

end spec

end k8s
end EtcdGrove
end Perennial
