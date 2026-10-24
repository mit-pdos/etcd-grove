/-
`(*EtcdServer).RaftHandler()` (`server.go`): its body, `s.r.transport.Handler()`. Lean-first (no
Rocq counterpart); D21 stage M5 (2026-10-19, the user's (A)), an axiom over the names-only
transport until rafthttp stage 6d (2026-10-24), which translated it and proved it over rafthttp's
`Transport.Handler`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

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
`NewServer` gives, with its transport `τ`), for an address `a` the member owns (one of its peer
URLs' hosts): a handler of `a` for the raft protocol (`raftProto`, `http.handlerOk`), each request
it serves borrowing `srvServeRes γn τ` (an `R` of the transport's and one of its reader tokens).
`s.r.transport` is `τ.t`, frozen with every other member added as a peer: its `Handler()`
(`rafthttp.Transport.Handler`). -/
abbrev EtcdServer.RaftHandler.spec : Prop :=
  ∀ (s : Loc) (γn : NetNames GF) (id : w64) (τ : SrvTr GF) (a : GoString),
  (netRh γn).owner a = id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNetMember γn s id τ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RaftHandler")) (Val #()))
  {{ (h : GoInterface), RET #h; http.handlerOk (raftHttpNet (netRh γn)) a (srvServeRes γn τ) h }}

end spec

end EtcdGrove
end Perennial
