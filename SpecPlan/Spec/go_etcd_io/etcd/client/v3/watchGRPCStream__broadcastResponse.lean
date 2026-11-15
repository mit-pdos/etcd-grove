/-
`(*watchGRPCStream).broadcastResponse(wr)`: the same response to every registered substream (or its goroutine stopped: `donec`); shared, as it has no events (`watchRespAt_noEvents_dup`). Users: `dispatchEvent`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `s.broadcastResponse(wr)`: `true`. -/
def watchGRPCStream.broadcastResponse.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) (wr : Loc)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (mw : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r ∗ wr ↦□ v ∗ watchRespAt v mw ∗ deliverOk s γ who none mw ∗
      ⌜mw.events = []⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"broadcastResponse")) (Val #wr))
  {{ (ok : Bool), RET #ok; ⌜ok = true⌝ ∗ wgsRun s γ who r }}

end spec

end ClientV3
end EtcdGrove
end Perennial
