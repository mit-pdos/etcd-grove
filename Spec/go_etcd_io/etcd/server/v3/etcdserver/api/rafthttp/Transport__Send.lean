/-
`(*Transport).Send(msgs)` (`transport.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv

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

/-- **`t.Send(msgs)`** on a started transport of the member `lid`, with a reader's token of its
mutex, of messages the member sends (`sendMsg`): it returns, each message handed to the peer or
remote of its `To` (`peer.send`, `remote.send`), or dropped (none such, or `To` zero); the token
back. -/
abbrev rafthttp.Transport.Send.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs : GName)
    (sl : GoSlice) (msL : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trFixed Rh t lid γd R ∗ trReadTok Rh t lid γd R γs ∗ sl ↦* msL ∗
      [∗list] m ∈ msL, sendMsg Rh lid m }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Send")) (Val #sl))
  {{ RET #(); trReadTok Rh t lid γd R γs }}

end spec

end EtcdGrove
end Perennial
