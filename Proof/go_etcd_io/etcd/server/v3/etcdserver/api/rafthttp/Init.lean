/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`rafthttpInit`, `etcdserver/BaseApply.lean`): `ErrExceedSizeLimit` holds a non-nil
error, `linkHeartbeatMessage` a heartbeat message without unknown fields, read-only for good. Its
initializer runs its variables' initializers: (prove-errinits, 2026-11-19) its errors' are translated,
`errors.New` calls and verb-less `fmt.Errorf` calls (`msg_codec.go`, `http.go`, `peer.go`,
`stream.go`; `fmt.Errorf`'s trusted model is `errors.New(format)`), until then the trust-boundary axiom
`errorsNewVarsInit`; (prove-misc, 2026-11-20) `linkHeartbeatSize = proto.Size(&linkHeartbeatMessage)`
(`stream.go`) is translated, over `proto.SizePb`'s spec at the registered `raftpb.Message` (until then
the trust-boundary axiom `linkHeartbeatSize_init`).
(const-inits, 2026-11-19) The timeouts and intervals (`snapResponseReadTimeout`, `ConnWriteTimeout`,
`proberInterval`, `statusMonitoringInterval`, `statusErrorInterval`), `errMemberNotFound`
(`fmt.Errorf`, its proof) and `supportedStream` (a map literal of slice literals) are translated
and set (until then the trust-boundary axioms `<X>_init` and `opaqueInitsOk`).
`RaftPrefix` (`"/raft"`), its subpaths `ProbingPrefix`, `RaftStreamPrefix` and `RaftSnapshotPrefix`
(`path.Join`, proved), `ConnReadTimeout` (`DefaultConnReadTimeout`, five seconds), `readBytesLimit`
(512 MiB) and (raft-entsize, route H1, 2026-11-10) `linkHeartbeatMessage`
(`raftpb.Message{Type: raftpb.MsgHeartbeat.Enum()}`, `stream.go`: `Enum`'s proof inlined, the
literal frozen by `hbMsg_init`) are translated and set. (metric-vecs, 2026-11-19) So are its metric
vectors (`metrics.go`: `sentBytes`, `activePeers`, `rttSec`, the snapshot metrics, ...), over
prometheus's `New<Kind>Vec` specs, each with its label names (`vecLabels`; until then the
trust-boundary axioms `<X>_init`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.github_com.xiang90.probing.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.httputil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.time.rate.Init
public import Proof.net.Init
public import Proof.net.http.Init
public import Proof.net.url.Init
public import Proof.path.Init
public import Proof.runtime.Init
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVarCell
public import Proof.fmt.OutLemmas
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.runtime.PkgInitRes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- A lookup in `<[k := v]> m` finds `v` or one of `m`'s values. -/
theorem EtcdGrove.lookup_insert_some {K V : Type} [DecidableEq K] (m : GMap K V) (k k' : K) (v w : V)
    (h : (<[k := v]> m) !! k' = some w) : w = v ∨ m !! k' = some w := by
  rw [GMap.lookup_insert_eq_iff] at h
  by_cases hk : k = k' <;> simp [hk] at h <;> simp [h]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"active_peers",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"disconnected_peers_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"peer_sent_bytes_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"peer_received_bytes_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"peer_sent_failures_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"peer_received_failures_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_send_success",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_send_inflights_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_send_failures",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_send_total_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_receive_success",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_receive_inflights_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_receive_failures",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"snapshot_receive_total_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"peer_round_trip_time_seconds"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

end Perennial
