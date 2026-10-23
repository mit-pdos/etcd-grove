/-
`(*pipeline).post(data)` (`pipeline.go`; rafthttp stage 4d, D33b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`p.post(data)`** of an encoding of the message `st` for the peer `to` (not a snapshot, without
responses), with its bundle: it posts it to one of the peer's URLs (the request's deposit holding
the one-shot part, `pipeDeposit`), and returns an error whose `Error()` returns; it reports nothing on `errorc` (the
member's response is never a `403`, `raftProto`). -/
abbrev rafthttp.pipeline.post.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (p : Loc) (to : w64) (d : GoSlice) (bs : List w8) (st : MsgSt),
  MsgWireOk st bs → st.msg.To' = to → st.msg.Type' ≠ MsgSnap → st.resps = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pipeSenderOk Rh p to ∗ d ↦* bs ∗ □ Rh.γn.N.P st ∗ Rh.γn.N.O st }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.pipeline.ty @!! go!"post")) (Val #d))
  {{ (err : GoInterface), RET #err; http.errStrOk err }}

end spec

end EtcdGrove
end Perennial
