/-
`(*watchGRPCStream).dispatchEvent(pbresp)`: the client's response (`WireWatchRespM.toResp`, `ensureWatchHeader`), broadcast if a progress of id `-1`, else unicast; the response's facts for its target (`deliverOk`). Users: `run`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `s.dispatchEvent(pbresp)`: delivered (`true`), or no substream took it. -/
def watchGRPCStream.dispatchEvent.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) (p : Loc) (mr : WireWatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r ∗ wireWatchRespOwn p (DFrac.own 1) mr ∗
      deliverOk s γ who
        (if (mr.toResp mr.events).isProgressNotify = true ∧ mr.watchId = -1 then -1 else mr.watchId)
        (mr.toResp mr.events) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"dispatchEvent")) (Val #p))
  {{ (ok : Bool), RET #ok; wgsRun s γ who r ∗
      ⌜(mr.toResp mr.events).isProgressNotify = true ∧ mr.watchId = -1 → ok = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
