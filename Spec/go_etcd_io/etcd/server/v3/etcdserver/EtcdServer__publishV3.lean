/-
`(*EtcdServer).publishV3(timeout)` (`server.go`): one of the goroutines `Start` attaches, with its body
(prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42; until then names-only, a trust-boundary axiom).
Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MonitorsOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.publishV3(timeout)` returns (names-only: it publishes the member's attributes through raft
until it succeeds or `stopping` is closed). It proposes, through `s.raftRequest`, only
`ClusterMemberAttrSet` requests (`server.go`: `req := pb.InternalRaftRequest{ClusterMemberAttrSet:
…}`), with the permission `srvMonitorPermitM` gives (in either auth mode, `MonitorsOn.lean`, E3zb) (D19c, 2026-10-18, `InvMonitors.lean`; until
then the contract took only the package's initialization, and its proposals were outside the
model). On success it closes `s.readych` (`close(s.readych)`), with the right to (`srvReadyCloser`,
2026-10-23: until then the contract closed a channel it did not own). (2026-11-02, the cluster-rows
stage: its requests name the server's own id, `s.MemberID()`, `monitorReq lid`.) (srvloops2, 2026-11-21, bounds B2 for `lgMu`) With
`GoAttach`'s pool of `s.lgMu` reader slots (`raftPool (srvLgReader s)`, `srvGoAttachOk`'s, persistent) and a
level-1 token (`levelTok 1`, given back), with which `Logger()` borrows a slot for its read lock (until then
`Logger()` read-locked without one: what the spec now rules out). (prove-ps2-srvgoroutines, 2026-11-24, the body
proved) `srvReadyCloser` holds, besides the channel, the server's attributes read-only and the reader slots
its proposals take (`raftRequest`'s: one of `leadTimeMu` with one of the transport, and the auth store's
reader resource, each given back), from `NewServer`; and it takes the server's view in the mode `on`, which
is the environment's (`isServerReadM`: `s.stopping`'s stop channel, `s.ctx` a child of `Background()`, the
store's log lower bound), and the request names' credential. Until then the contract was a names-only
axiom. -/
abbrev EtcdServer.publishV3.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (d : _root_.Perennial.time.Duration) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authOn = on⌝ ∗
      srvMonitorPermitM on s E ρ ∗ srvReadyCloser s E ∗ raftPool (srvLgReader s) ∗ levelTok 1 ∗
      isServerReadM on s E γr ∗ □ (|==> idCred ρ.ids 1) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"publishV3")) (Val #d))
  {{ RET #(); levelTok 1 }}

end spec

end EtcdGrove
end Perennial
