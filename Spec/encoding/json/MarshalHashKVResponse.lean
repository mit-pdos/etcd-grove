/-
`json.Marshal(resp)` of a `*etcdserverpb.HashKVResponse`: the trust boundary (`encoding/json`
is names-only; PR etcd#22243, the peer hashKV handler). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `json.Marshal(resp)`, `resp` a `HashKVResponse` with only `Header` (a `ResponseHeader` with
only `Revision` set), `Hash`, `CompactRevision` and `HashRevision` set, returns its encoding
`json.hashKVRespJSON`, or an error whose `Error()` returns. -/
abbrev json.MarshalHashKVResponse.spec : Prop :=
  ∀ (resp p : Loc) (hrev crev hashRev : w64) (h : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      resp ↦ hkvResp p h crev hashRev ∗ p ↦ hkvRespHeader hrev }}
    (App (Val (@! _root_.Perennial.encoding.json.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.HashKVResponse.ty) #resp)))
  {{ (sl : GoSlice) (err : GoError), RET (PairV #sl #err);
      (⌜err = interface.nil⌝ → sl ↦* json.hashKVRespJSON hrev h crev hashRev) ∗
      (∀ e, ⌜err = GoInterface.ok e⌝ → errorStringSpec e) }}

end spec

end EtcdGrove
end Perennial
