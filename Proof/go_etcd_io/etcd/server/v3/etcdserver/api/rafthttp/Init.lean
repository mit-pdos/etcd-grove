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
`errorsNewVarsInit`; `linkHeartbeatSize_init` states `linkHeartbeatSize`'s (`stream.go`).
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
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVarCell

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

section opaqueInits
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `linkHeartbeatSize = proto.Size(&linkHeartbeatMessage)` (`stream.go`): the heartbeat's encoding's size (two bytes), an `int` from `0` to below `2^50`; nothing writes it (the stream writer adds it to its metrics). -/
axiom linkHeartbeatSize_init :
    {{ (True : IProp GF) }} (App (Val linkHeartbeatSize.init) (Val #()))
    {{ RET #(); ∃ n : w64, globalAddr linkHeartbeatSize ↦ n ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 50⌝ }}

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
end opaqueInits

/-- A lookup in `<[k := v]> m` finds `v` or one of `m`'s values. -/
theorem EtcdGrove.lookup_insert_some {K V : Type} [DecidableEq K] (m : GMap K V) (k k' : K) (v w : V)
    (h : (<[k := v]> m) !! k' = some w) : w = v ∨ m !! k' = some w := by
  rw [GMap.lookup_insert_eq_iff] at h
  by_cases hk : k = k' <;> simp [hk] at h <;> simp [h]

end Perennial
