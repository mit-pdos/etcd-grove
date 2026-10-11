/-
`demux.updateStoreLocked(resp)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.updateStoreLocked(resp)`, under the write lock, after `Broadcast`'s checks (initialized,
`validateRevisions`): `minRev`, `maxRev` and the history become `updResp cap c r`'s (a progress
notification sets `maxRev`; events are appended batch by batch, `updCore`). -/
abbrev demux.updateStoreLocked.spec : Prop :=
  ∀ (d : Loc) (cap : Nat) (c : DemuxCore)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxMinRevAddr d ↦ c.minRev ∗ demuxMaxRevAddr d ↦ c.maxRev ∗
      ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history ∗
      respAt resp r ∗
      ⌜DemuxInv cap c ∧ c.minRev ≠ W64 0 ∧ validRevisions r c.maxRev = true ∧
        EvRevSorted r.events ∧ RespRevsBounded r⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"updateStoreLocked")) (Val #resp))
  {{ RET #();
      demuxMinRevAddr d ↦ (updResp cap c r).minRev ∗
      demuxMaxRevAddr d ↦ (updResp cap c r).maxRev ∗
      ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev
        (updResp cap c r).history }}

end spec

end EtcdGrove
end Perennial
