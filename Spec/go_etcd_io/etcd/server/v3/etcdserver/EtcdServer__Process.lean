/-
`(*EtcdServer).Process` (`server.go`): rejects a message from a removed member or to another member with a `403`, counts a `MsgApp` in the server's stats, and steps the message into raft (`s.r.Step`). Lean-first (no Rocq counterpart); D21 stage M2
(2026-10-19): the inbound path from the transport (`rafthttp.Raft`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Process(ctx, m)`** on the server `s`, member `id` of the network `γn` (`srvProcOk`), a
message the network delivers to it (`netRecv`) and a context the node API takes, with one of
`lgMu`'s reader slots (`Logger()`): returns some error, the slot back. The two `403` branches are
dead: the cluster removes no member (`IsIDRemoved` is `false`) and the message is addressed to
`id` (the network's promise); the message is stepped into raft's node (`stepP`, `stepP_of_recv`). -/
abbrev EtcdServer.Process.spec : Prop :=
  ∀ (γn : NetNames GF) (s : Loc) (id : w64) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ml : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvProcOk γn s id ∗ nodeCtx ctx cd ∗ srvLgReader s ∗ netRecv γn id ml }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Process"))
      (Val #(GoInterface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; srvLgReader s }}

end spec

end EtcdGrove
end Perennial
