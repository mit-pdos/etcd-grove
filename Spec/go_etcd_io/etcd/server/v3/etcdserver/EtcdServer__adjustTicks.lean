/-
`(*EtcdServer).adjustTicks()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

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

/-- `s.adjustTicks()` returns (names-only: it advances the raft ticks of a fresh or rejoining member, then returns). It reads `s.Logger()` and logs through it (`lg.Info`), and reads the cluster, the raft
node and `s.Cfg`: its premise is the server's request-side fields (`isServerReqM`) and its logger
(`srvLoggerOk`; premise fixes 6, family axiom #22: until then nothing on `s`). (srvloops2, 2026-11-21, bounds B2 for `lgMu`) With
`GoAttach`'s pool of `s.lgMu` reader slots (`raftPool (srvLgReader s)`, `srvGoAttachOk`'s, persistent) and a
level-1 token (`levelTok 1`, given back), with which `Logger()` borrows a slot for its read lock (until then
`Logger()` read-locked without one: what the spec now rules out). (prove-ps2-srv, 2026-11-22: proved
over the real code) With the raft wrapper's contract (`isRaftNode`, for `advanceTicks`): a single member
fast-forwards its ticks (`advanceTicks(ElectionTicks - 1)`). (rdslot, 2026-11-22) In a cluster of
several members, for either value of `InitialElectionTickAdvance` (its field read-only): off, it logs
and returns; on, it waits up to `ConnReadTimeout / 50ms` rounds, each a `select` on `time.After(50ms)`
and `s.stopping` (`srvGoAttachOk`'s, returning once closed), for the transport's `ActivePeers()` to
exceed one (read with a reader slot of the transport, `srvTrReader`, given back), and then
fast-forwards (`advanceTicks(ElectionTicks - 2)`). Until rdslot the premise
`InitialElectionTickAdvance = false` (`srvMonitorsOff`'s), and before prove-ps2-srv an axiom. -/
abbrev EtcdServer.adjustTicks.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (Er : RNEnv GF) (γn : RNNames GF)
    (γg : GoNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLoggerOk s ∗ raftPool (srvLgReader s) ∗ levelTok 1 ∗
      srvGoAttachOk s γg ∗ srvTrReader s ∗
      (∃ b : Bool, srvCfgFieldAddr s go!"InitialElectionTickAdvance" ↦□ b) ∗
      isRaftNode Er γn (srvRAddr s) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"adjustTicks")) (Val #()))
  {{ RET #(); levelTok 1 ∗ srvTrReader s }}

end spec

end EtcdGrove
end Perennial
