/-
`json.Unmarshal(bs, req)` into a `*etcdserverpb.HashKVRequest`: the trust boundary
(`encoding/json` is names-only; PR etcd#22243, the peer hashKV handler). Lean-first (no Rocq
counterpart).
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

/-- `json.Unmarshal(sl, req)`, `req` a zero `HashKVRequest`, decodes `json.hashKVReqOf bs`:
on success (`nil`) the request's `Revision` is the revision decoded, else it returns an error. -/
abbrev json.UnmarshalHashKVRequest.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (bs : List w8) (req : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ sl ↦*{dq} bs ∗
      req ↦ (zero_val etcdserverpb.HashKVRequest) }}
    (App (App (Val (@! _root_.Perennial.encoding.json.Unmarshal)) (Val #sl))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.HashKVRequest.ty) #req)))
  {{ (err : GoError), RET #err; sl ↦*{dq} bs ∗ ∃ v : etcdserverpb.HashKVRequest, req ↦ v ∗
      ⌜match json.hashKVReqOf bs with
        | none => err ≠ interface.nil
        | some rev => err = interface.nil ∧ v.Revision' = rev⌝ }}

end spec

end EtcdGrove
end Perennial
