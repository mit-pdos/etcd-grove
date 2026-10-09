/-
`NewDemux(ctx, wg, historyWindowSize, resyncInterval)` (`cache/demux.go`). Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `NewDemux(ctx, wg, historyWindowSize, resyncInterval)`: `newDemux` (`historyWindowSize` in
`(0, 2^61]`), then `wg.Add(1)` and a goroutine running `resyncLoop(ctx)` then `wg.Done()`. The
wait group is the caller's, described by the triples of its `Add(1)` (from a slot `Pslot` to a
running token `Prun`, giving back `Pret`) and of its `Done()` (consuming `Prun`):
`wgSlotProtocol`. Returns `newDemux`'s resources less
what the goroutine keeps: one demux token and one notifier handle. -/
abbrev NewDemux.spec : Prop :=
  ∀ (C : DemuxCert GF) (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (wg : Loc)
    (Pslot Prun Pret : IProp GF) (historyWindowSize : w64) (resyncInterval : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isContext ctx s ∗
      ⌜0 < sint.Z historyWindowSize ∧ sint.Z historyWindowSize ≤ 2 ^ 61⌝ ∗
      wgSlotProtocol wg Pslot Prun Pret ∗ Pslot }}
    (App (App (App (App (Val (@! NewDemux)) (Val #(GoInterface.ok ctx))) (Val #wg))
      (Val #historyWindowSize)) (Val #resyncInterval))
  {{ (d : Loc) (γd : DemuxNames) (γn : NotifierNames), RET #d; Pret ∗
      isDemux d γd (sint.nat historyWindowSize) C ∗
      demuxWriter d γd (sint.nat historyWindowSize) C DemuxCore.init ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
        demuxHandle d γd (sint.nat historyWindowSize) C) ∗
      notifierLb γn 0 ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        demuxResyncHandle d γn }}

end spec

end EtcdGrove
end Perennial
