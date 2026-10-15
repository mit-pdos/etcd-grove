/-
`(*clientv3.watchGRPCStream).dispatchEvent(pbresp)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.dispatchEvent(pbresp)` of a response holding `m` (its fields read; its header `h` not nil,
read only if it has no events; its events `es`): makes the `WatchResponse` `wrOf m h sl` (at a
fresh location, read-only) and broadcasts it (a progress notification of id `-1`,
`isBroadcast`) or sends it to the substream registered under its id (`unicastResponse`), each
target's content of it given (`sendCap`); returns whether it was delivered (unicast). -/
abbrev watchGRPCStream.dispatchEvent.spec : Prop :=
  ∀ (V : WEnv GF) (wgs p : Loc) (dq : DFrac) (mm : v3rpc.WatchRespM) (h : Loc) (sl : GoSlice)
    (es : List EvModel) (m : Loc) (M : GMap w64 Loc) (dq1 dq2 : DFrac),
  let Ψ : Loc → IProp GF := fun wr => iprop(wr ↦□ wrOf mm h sl)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ respFields p dq mm h sl ∗
      eventsAt sl es ∗ ⌜es.length = mm.evs.length⌝ ∗
      (⌜mm.evs = []⌝ -∗ hdrAt h mm.hdr.revision) ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      (if decide (isBroadcast mm) then iprop([∗map] _k ↦ ws ∈ M, sendCap V ws Ψ)
       else match M !! mm.watchId with
         | some ws => sendCap V ws Ψ
         | none => iprop(True)) }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"dispatchEvent")) (Val #p))
  {{ (b : Bool), RET #b; respFields p dq mm h sl ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      (if decide (isBroadcast mm) then
        iprop([∗map] _k ↦ ws ∈ M, (∃ wr : Loc, sendDone V ws wr) ∨ sendCap V ws Ψ)
       else match M !! mm.watchId with
         | some ws => iprop((⌜b = true⌝ ∗ ∃ wr : Loc, sendDone V ws wr) ∨
             (⌜b = false⌝ ∗ sendCap V ws Ψ))
         | none => iprop(⌜b = false⌝)) }}

end spec

end EtcdGrove
end Perennial
