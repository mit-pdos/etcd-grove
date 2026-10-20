/-
`(*clientv3.watchGRPCStream).broadcastResponse(wr)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.broadcastResponse(wr)`: sends `wr` to every registered substream that has not stopped;
`true`. The targets' values are `Pf ws`, their `recvc` producers' histories `Sf ws`, their
lifetimes' `donec`s `Df ws` (D24; `run`'s generation authority at `n`). -/
abbrev watchGRPCStream.broadcastResponse.spec : Prop :=
  ∀ (V : WEnv GF) (wgs wr : Loc) (m : Loc) (M : GMap w64 Loc) (dq1 dq2 : DFrac)
    (Pf : Loc → WsPrm GF) (Sf : Loc → List Loc) (Df : Loc → DnInfo GF) (γend : GName) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗ monoNatAuthOwn γend 1 n ∗
      ([∗map] _k ↦ ws ∈ M, ⌜(Pf ws).ws = ws⌝ ∗ sendCap1 V (Pf ws) (Sf ws) wr (Df ws) γend n) }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"broadcastResponse")) (Val #wr))
  {{ RET #true; wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗ monoNatAuthOwn γend 1 n ∗
      ([∗map] _k ↦ ws ∈ M, sendDone (Pf ws) (Sf ws) wr (Df ws) γend n ∨
        sendFail V (Pf ws) (Sf ws) wr (Df ws) γend n) }}

end spec

end EtcdGrove
end Perennial
