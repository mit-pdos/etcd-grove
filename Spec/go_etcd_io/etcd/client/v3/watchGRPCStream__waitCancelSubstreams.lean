/-
`(*clientv3.watchGRPCStream).waitCancelSubstreams(stopc)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.InvWcJoin

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

/-- **`w.waitCancelSubstreams(stopc)`** (D24; `newWatchClient`'s, while it opens a gRPC stream): for
each substream of `resuming` (`l`, no nil), a goroutine that, unless `stopc` is closed first,
closes the substream once its watch's context is done (`closing` set, `outc` closed and `nil`, the
substream posted on `closingc` from a goroutine added to the stream's wait group, which the
goroutines share, `wgsWgShared`), or closes the `outc` a stopped substream left if its context is
done; returns a channel closed once every goroutine is done, whose close gives each substream back
(`wcOut`) with the shared adder's tokens, through a one-shot update (`£ 1`). -/
abbrev watchGRPCStream.waitCancelSubstreams.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (s : GoSlice) (l : List Loc) (dq : DFrac)
    (Pf : Loc → WsPrm GF) (stopc : GoChan) (γst : ChanNames) (γS : WgsWgNames) (γh : WgsShNames) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      wgsF G.wgs go!"resuming" ↦{dq} s ∗ s ↦* l ∗ ⌜∀ ws ∈ l, (Pf ws).ws = ws⌝ ∗
      ownBroadcastChan stopc γst iprop(True) .Unknown ∗
      wgsWgShared (wgsF G.wgs go!"wg") γS γh n ∗ threadTok ∗
      [∗list] ws ∈ l, wcIn V G (Pf ws) }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"waitCancelSubstreams")) (Val #stopc))
  {{ (donec : GoChan), RET #donec; wgsF G.wgs go!"resuming" ↦{dq} s ∗ s ↦* l ∗ threadTok ∗
      wgsWgShared (wgsF G.wgs go!"wg") γS γh (n + l.length) ∗
      ∃ (γd : ChanNames) (Qd : IProp GF), ownBroadcastChan donec γd Qd .Unknown ∗
        (£ 1 -∗ □ Qd ={⊤}=∗ [∗list] ws ∈ l, wcOut V G (Pf ws) ∗
          wgsShareTok (wgsF G.wgs go!"wg") γS γh) }}

end spec

end EtcdGrove
end Perennial
