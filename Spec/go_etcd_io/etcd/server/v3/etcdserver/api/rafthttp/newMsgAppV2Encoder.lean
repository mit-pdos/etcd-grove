/-
`newMsgAppV2Encoder(w, fs)` (`msgappv2_codec.go`; rafthttp stage 5b). Lean-first; the model: `rafthttp/MsgAppV2.lean`.
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

/-- **`newMsgAppV2Encoder(w, fs)`** of a writer and non-`nil` follower stats: an encoder at the zero
state (`v2Codec`'s initial state). -/
abbrev rafthttp.newMsgAppV2Encoder.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (fs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      ⌜fs ≠ null⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Encoder))
      (Val #(GoInterface.ok wi))) (Val #fs))
  {{ (enc : Loc), RET #enc; v2EncOwn enc wi fs ⟨W64 0, W64 0⟩ }}

end spec

end EtcdGrove
end Perennial
