/-
`(*EtcdServer).RaftHandler()` (`server.go`): names-only (its body, `s.r.transport.Handler()`, calls
rafthttp's names-only `Transport.Handler`). Lean-first (no Rocq counterpart); D21 stage M5
(2026-10-19, the user's (A)), an axiom at the trust boundary, why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.RaftHandler()`** on member `id`'s server in the network `γn` (`srvNetMember`, which
`NewServer` gives): a handler `h` of the transport holding `id`'s slot (`raftHandlerOf γn id h`).

Why it is true of the Go code (`server.go`, `rafthttp/transport.go` at the etcd pin):
`RaftHandler` returns `s.r.transport.Handler()`; `s.r.transport` is the `*rafthttp.Transport` `t`
that `NewServer` started for member `id` with `id`'s slot (`srvNetMember`'s
`rnTransportAddr ↦□ t`, `transportStarted γn t`). `Handler()` builds a fresh `http.ServeMux` (no
panic, no side effect on `t`) routing `/raft` to a pipeline handler, `/raft/stream/` to a stream
handler and `/raft/snapshot` to a snapshot handler over `t`, `t.Raft` (the server), `t.ID` and
`t.ClusterID`, and the prober's path to `probing.NewHandler()`: every message it receives goes to
`t.Raft`'s `Process` (directly, or through `t`'s peer for the sender), as `Transport.Start`'s
axiom describes. It reads only fields `NewServer` set before the transport started. -/
abbrev EtcdServer.RaftHandler.spec : Prop :=
  ∀ (s : Loc) (γn : NetNames GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNetMember γn s id }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RaftHandler")) (Val #()))
  {{ (h : GoInterface), RET #h; raftHandlerOf γn id h }}

end spec

end EtcdGrove
end Perennial
