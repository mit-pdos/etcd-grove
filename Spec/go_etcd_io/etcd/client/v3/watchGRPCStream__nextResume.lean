/-
`(*clientv3.watchGRPCStream).nextResume()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.nextResume()`: drops the nil substreams at the head of `resuming` and returns its new head
(`nil` if it is empty). -/
abbrev watchGRPCStream.nextResume.spec : Prop :=
  ∀ (wgs : Loc) (s : GoSlice) (l : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"resuming" ↦ s ∗ sliceOwn s l }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"nextResume")) (Val #()))
  {{ (ws : Loc), RET #ws; ∃ s' : GoSlice, wgsF wgs go!"resuming" ↦ s' ∗
      sliceOwn s' (l.dropWhile (fun x => decide (x = null))) ∗
      ⌜ws = ((l.dropWhile (fun x => decide (x = null))).head?).getD null⌝ }}

end spec

end EtcdGrove
end Perennial
