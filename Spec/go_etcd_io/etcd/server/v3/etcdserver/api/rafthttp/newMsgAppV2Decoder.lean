/-
`newMsgAppV2Decoder(r, local, remote)` (`msgappv2_codec.go`; rafthttp stage 5b). Lean-first; the model: `rafthttp/MsgAppV2.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`newMsgAppV2Decoder(r, local, remote)`**: a decoder of the connection from `remote` to
`local`, at the zero state. -/
abbrev rafthttp.newMsgAppV2Decoder.spec : Prop :=
  ∀ (r : GoInterface) (lcl rmt : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Decoder))
      (Val #r)) (Val #lcl)) (Val #rmt))
  {{ (dec : Loc), RET #dec; v2DecOwn dec r rmt lcl ⟨W64 0, W64 0⟩ }}

end spec

end EtcdGrove
end Perennial
