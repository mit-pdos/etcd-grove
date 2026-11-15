/-
`(*watchGRPCStream).unicastResponse(wr, id)`: to the substream registered as `id`, unless none is or its goroutine stopped (`false`). Users: `dispatchEvent`.
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

/-- `s.unicastResponse(wr, id)`. -/
def watchGRPCStream.unicastResponse.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) (wr : Loc)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (mw : WatchRespM) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r ∗ wr ↦□ v ∗ watchRespAt v mw ∗ deliverOk s γ who (some (sint.Z id)) mw }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"unicastResponse")) (Val #wr)) (Val #id))
  {{ (ok : Bool), RET #ok; wgsRun s γ who r ∗
      ⌜ok = true → (sint.Z id) ∈ r.subs.map Prod.fst⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
