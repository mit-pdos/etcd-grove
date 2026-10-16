/-
`(*clientv3.watchGRPCStream).joinSubstreams()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.joinSubstreams()`: waits for the `donec` of every substream in `substreams` and of every
non-nil one in `resuming`. -/
abbrev watchGRPCStream.joinSubstreams.spec : Prop :=
  ∀ (wgs m : Loc) (M : GMap w64 Loc) (s : GoSlice) (l : List Loc) (dq1 dq2 dq3 dq4 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗ ([∗map] _k ↦ ws ∈ M, donecOf ws) ∗
      wgsF wgs go!"resuming" ↦{dq3} s ∗ s ↦*{dq4} l ∗ ([∗list] ws ∈ l, ⌜ws = null⌝ ∨ donecOf ws) }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"joinSubstreams")) (Val #()))
  {{ RET #(); wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      wgsF wgs go!"resuming" ↦{dq3} s ∗ s ↦*{dq4} l }}

end spec

end EtcdGrove
end Perennial
