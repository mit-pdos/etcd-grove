/-
`v3rpc.headerFillingRangeStream.Send` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`s.Send(resp)`** of the stream wrapper: the chunk's header (if any: `RangeResponse` is not
nil) filled but for its revision, then the wrapped stream's `Send` (`streamSendOk st Ψ Ξ`: a
contract whose precondition `Ψ` gets the chunk with its header filled). -/
abbrev v3rpc.headerFillingRangeStream.Send.spec : Prop :=
  ∀ (p st hp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (stv : GoInterface)
    (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF) (resp rr h : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      structFieldRef v3rpc.headerFillingRangeStream go!"KV_RangeStreamServer" p ↦□ stv ∗
      structFieldRef v3rpc.headerFillingRangeStream go!"hdr" p ↦□ hp ∗
      v3rpc.hdrIs hp s A cid mid ∗ v3rpc.streamSendOk stv Ψ Ξ ∗
      structFieldRef etcdserverpb.RangeStreamResponse go!"RangeResponse" resp ↦□ rr ∗
      ⌜rr ≠ null⌝ ∗ structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ h ∗
      ((⌜h = null⌝ ∗ Ψ resp) ∨ (v3rpc.hdrW h ∗ (v3rpc.hdrFilled h cid mid -∗ Ψ resp))) }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.headerFillingRangeStream.ty @!! go!"Send"))
      (Val #resp))
  {{ (err : GoInterface), RET #err; Ξ resp err }}

end spec

end EtcdGrove
end Perennial
