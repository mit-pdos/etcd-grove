/-
`(*clientv3.WatchResponse).IsProgressNotify()` (`client/v3/watch.go`).

**Users**: Kubernetes' etcd3 watcher, the cache (`store`, `demux`), grpcproxy's broadcast, the
examples (`progress.go`). **Proof sketch**: `len(Events)`, the fields, `Header.GetRevision()` (3h's
getter: `0` on a `nil` header). **Changes** from `specs-ref/.../WatchResponse__IsProgressNotify.lean`:
over the struct and an optional header (so that the cache's own responses are covered); for a
response of a watch's channel it is `WatchRespM.isProgressNotify` (`watchRespAt_fields`).
**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `wr.IsProgressNotify()`. -/
def WatchResponse.IsProgressNotify.spec : Prop :=
  ∀ (p : Loc) (dq dh : DFrac) (v : go_etcd_io.etcd.client.v3.WatchResponse) (h : Option HeaderM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦{dq} v ∗
      optOwn respHeaderOwn v.Header' dh h }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty @!!
      go!"IsProgressNotify")) (Val #()))
  {{ (b : Bool), RET #b; p ↦{dq} v ∗ optOwn respHeaderOwn v.Header' dh h ∗
      ⌜b = decide (v.Events'.len = W64 0 ∧ v.Canceled' = false ∧ v.Created' = false ∧
        v.CompactRevision' = W64 0 ∧ (h.map (·.revision)).getD (W64 0) ≠ W64 0)⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
