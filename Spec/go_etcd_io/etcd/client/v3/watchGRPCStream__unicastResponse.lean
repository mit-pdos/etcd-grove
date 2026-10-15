/-
`(*clientv3.watchGRPCStream).unicastResponse(wr, watchID)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.unicastResponse(wr, watchID)`: `false` if no substream is registered under the id; otherwise
sends `wr` to it (`true`: its content delivered) unless the substream has stopped (`false`: the
content back). -/
abbrev watchGRPCStream.unicastResponse.spec : Prop :=
  ∀ (V : WEnv GF) (wgs wr : Loc) (watchID : w64) (m : Loc) (M : GMap w64 Loc) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      (match M !! watchID with
       | some ws => sendCap1 V ws wr
       | none => iprop(True)) }}
    (App (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"unicastResponse")) (Val #wr)) (Val #watchID))
  {{ (b : Bool), RET #b; wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      (match M !! watchID with
       | some ws => iprop((⌜b = true⌝ ∗ sendDone V ws wr) ∨ (⌜b = false⌝ ∗ sendCap1 V ws wr))
       | none => iprop(⌜b = false⌝)) }}

end spec

end EtcdGrove
end Perennial
