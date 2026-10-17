/-
`(*clientv3.watchRequest).toPB()` (`client/v3/watch.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `wr.toPB()` of a request of a range watch (no filter, no previous key-values, no fragments):
a `*pb.WatchRequest` the client sends (`watchReqSend`, read-only) holding the create request of
its key, range end, start revision (the `rev` field, read at any fraction) and progress flag,
with the automatic watch id (`createOf`). -/
abbrev watchRequest.toPB.spec : Prop :=
  ∀ (wr : Loc) (key ed : GoString) (rv : w64) (pn : Bool) (flt : GoSlice) (dq : DFrac) (sr : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wrF wr go!"key" ↦□ key ∗ wrF wr go!"end" ↦□ ed ∗ wrF wr go!"rev" ↦{dq} rv ∗
      wrF wr go!"progressNotify" ↦□ pn ∗ wrF wr go!"filters" ↦□ flt ∗ flt ↦*□ ([] : List w32) ∗
      wrF wr go!"prevKV" ↦□ false ∗ wrF wr go!"fragment" ↦□ false }}
    (App (Val (wr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty @!! go!"toPB"))
      (Val #()))
  {{ (p : Loc), RET #p; wrF wr go!"rev" ↦{dq} rv ∗
      v3rpc.watchReqSend p (.create (createOf key ed rv pn sr)) }}

end spec

end EtcdGrove
end Perennial
