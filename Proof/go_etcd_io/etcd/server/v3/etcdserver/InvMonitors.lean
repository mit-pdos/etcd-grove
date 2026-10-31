/-
**What the names-only proposers propose** (D19c, option (a), 2026-10-18; `notes/decisions.md`,
D19c). Lean-first (no Rocq counterpart).

Besides the request path (`EtcdServer.Put`/`DeleteRange`/`Txn`, whose proposals carry their
shapes, `reqPropOk`), two goroutines `Start` attaches propose through `s.raftRequest`, and their
specs are trust-boundary contracts (names-only, `server.go`):

* `publishV3(timeout)` proposes `InternalRaftRequest{ClusterMemberAttrSet: …}` (the member's name
  and client URLs), retrying until it succeeds or the server stops;
* `monitorClusterVersions()` (on the leader) proposes, through `updateClusterVersionV3`,
  `InternalRaftRequest{ClusterVersionSet: {Ver: v.String()}}` with `v` a `semver.Version` the
  monitor decided (`decideClusterVersion`), whose `String()` parses back (`semverValid`).

Their contracts take `srvMonitorPermit s E ρ`: the server's request path and the proposals'
permission (`reqPropOk`, with a trivial result) for exactly those requests, a plain non-write
request of one of the two kinds with no range end `[0]` (no range, delete or transaction field
set) and, for a version, a valid one. So the committed entries they produce have the shapes the KV
invariant keeps (`rqShape`: `rqOk` asks nothing of a member's attributes, and a valid version of
`ClusterVersionSet`). Until D19c their contracts took only the package's initialization (their
proposals were not in the model).

**The monitors that are off** (audit B4a, 2026-10-18; `notes/decisions.md`, D19m): three more
goroutines `Start` attaches would read the backend and propose alarms (`Alarm{CORRUPT}`, which the
KV model does not admit, as the NOSPACE alarm) or a downgrade's cancellation once configured:
`monitorKVHash` (`CorruptCheckTime ≠ 0`), `monitorCompactHash` (the `CompactHashCheck` feature on)
and `monitorDowngrade` (`DowngradeCheckTime ≠ 0`). Their contracts are restricted to the
configuration under which each returns at once (putget's: the zero durations, the feature off by
default): `srvMonitorsOff s`, the two fields at `0` and the feature gate answering `false` for
`CompactHashCheck` (`featureIs`). `NewServer` leaves the fields at the configuration's values
(`srvMonitorCfg s cfg`, with the `lgMu` reader slot `monitorDowngrade`'s `Logger()` needs), and
`srvMonitorsOff_of` turns them into `srvMonitorsOff` for a configuration that leaves them off.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **The requests the monitors propose** (pure): a member's attributes, or a valid cluster
version, with no range end `[0]` and no auth request field set (`needAdminPermission`: D19k,
2026-10-18, the KV model's `plainReq` asks it), and (D22, 2026-10-23) no side-effect-free field
set (`noSideEffect`: the monitors' requests set only their own field). Their kinds are plain
(`putgetKind_cluster`). -/
def monitorReq (rq : apply.IRRModel) : Prop :=
  irrNoZeroEnd rq ∧ apply.needAdminPermission rq = false ∧ apply.noSideEffect rq = false ∧
    (apply.dispatchKind rq = .clusterMemberAttrSet ∨
      (apply.dispatchKind rq = .clusterVersionSet ∧
        ∀ v, rq.clusterVersionSet = some v → apply.semverValid v))

/-- A monitor's request has a good shape. -/
theorem rqShape_of_monitorReq (rq : apply.IRRModel) (h : monitorReq rq) : rqShape rq := by
  obtain ⟨-, -, -, hk⟩ := h
  refine ⟨fun on => ?_, fun log _ => ?_⟩
  · unfold apply.dispatchOk
    rcases hk with hk | ⟨hk, -⟩ <;> rw [hk] <;> exact ⟨by decide, fun h => by cases h⟩
  · unfold apply.rqOk
    rcases hk with hk | ⟨hk, hv⟩ <;> rw [hk]
    · trivial
    · exact hv

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the monitors may propose** (persistent; see the file header): the server's request
path, and the proposal's permission for a monitor's request. -/
def srvMonitorPermit (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerReq s E ρ ∗
    □ ∀ rq : apply.IRRModel, ⌜monitorReq rq⌝ -∗ reqPropOk ρ.kv rq (fun _ => iprop(True)))

/-- The monitors' permission, from the server's request path. -/
theorem srvMonitorPermit_of (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ srvMonitorPermit s E ρ := by
  iintro #H
  iunfold srvMonitorPermit
  iframe H
  iintro !> %rq %hrq
  iunfold reqPropOk
  ileft
  ipureintro
  have hs := rqShape_of_monitorReq rq hrq
  obtain ⟨hz, hna, hns, hk⟩ := hrq
  have hk' : apply.dispatchKind rq = .clusterMemberAttrSet ∨
      apply.dispatchKind rq = .clusterVersionSet := by
    rcases hk with hk | ⟨hk, -⟩
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨?_, ?_, hz, hs, rfl⟩
  · refine ⟨?_, putgetKind_cluster rq hk'⟩
    unfold plainCover; rcases hk' with hk' | hk' <;> rw [hk'] <;> exact ⟨hns, hna⟩
  · unfold writeKind; rcases hk' with hk' | hk' <;> rw [hk'] <;> decide

/-- **The monitors' configuration, as `NewServer` leaves it** (audit B4a; see the file header):
the corruption check's and the downgrade check's intervals and the feature gate at `cfg`'s values
(read-only), and an `lgMu` reader slot (`monitorDowngrade`'s `Logger()`). -/
def srvMonitorCfg (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(srvCfgFieldAddr s go!"CorruptCheckTime" ↦□ cfg.CorruptCheckTime' ∗
    srvCfgFieldAddr s go!"DowngradeCheckTime" ↦□ cfg.DowngradeCheckTime' ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ cfg.ServerFeatureGate' ∗
    srvLgReader s)

/-- **The hash and downgrade monitors are off** (persistent; audit B4a, see the file header): no
corruption check (`CorruptCheckTime = 0`), no downgrade check (`DowngradeCheckTime = 0`), and the
feature gate answering `false` for `CompactHashCheck`. -/
def srvMonitorsOff (s : Loc) : IProp GF :=
  iprop(srvCfgFieldAddr s go!"CorruptCheckTime" ↦□ (W64 0) ∗
    srvCfgFieldAddr s go!"DowngradeCheckTime" ↦□ (W64 0) ∗
    ∃ fg : GoInterface, srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗
      featureIs fg go!"CompactHashCheck" false)

instance srvMonitorsOff_persistent (s : Loc) : Persistent (srvMonitorsOff (GF := GF) s) := by
  unfold srvMonitorsOff; infer_instance

/-- **The right to close `s.readych`** (2026-10-23): the channel `NewServer` makes
(`readych: make(chan struct{})`, read-only in its field), allocated as a broadcast channel
(Perennial's `Broadcast` idiom, nothing promised to receivers: `True`) not yet closed. Only
`publishV3` closes it (`close(s.readych)`, once the member's attributes are published), so
`NewServer` hands this to `Start`, which hands it to `publishV3`'s goroutine; a receiver
(`ReadyNotify()`) would take the idiom's persistent part. Until then the axiom `publishV3.spec`
closed the channel without owning it. -/
def srvReadyCloser (s : Loc) : IProp GF :=
  iprop(∃ (rdc : GoChan) (γ : ChanNames), structFieldRef EtcdServer go!"readych" s ↦□ rdc ∗
    ownBroadcastChan rdc γ iprop(True) .Pending)

end defs

end EtcdGrove
end Perennial
