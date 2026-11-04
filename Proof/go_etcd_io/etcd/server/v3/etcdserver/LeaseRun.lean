/-
**The lease subsystem's premise on the running server** (2026-11-04; the lease-expiry plan's Part C,
option (a), `notes/lease-expiry-plan.md`, "Plumbing: Part C"). Lean-first.

The server's inner predicates (`srvBuilt`, `srvBuiltG`, `isServerBuilt(On)`, `isServerRun(On)`, and
the examples' `memberBoot`) carried the lease subsystem's premise inline, `lg = true →
lease.leasesNoExpiry ∧ srvGrantOpen`. They now carry `∃ m, lease.runCfg lg m`: the sealed
`lease.runCfg` at the KV names' grant flag `lg` and the lease mode `m`, introduced from the boot
slot (`lease.bootCfg_run`, `LeaseApi.lean`) or, before `NewServer`, by the mode's intro law. A later
change of what the running server takes of the lease subsystem (the expiry stage's Part X: the
revocable mode) changes `lease.runCfg`'s body and laws, not the inner predicates' text.

Below `InvRun.lean` (which `isServerRun` needs) and `LeaseApi.lean` (whose `lease.bootCfg` names
`srvGrantOpen`), with the open cases of a granting cluster (`srvGrantOpen`, `runSnapLgOkBody`, moved
from `InvRun.lean`). Sealed (`etc/import-all.txt`; `LeaseApi.lean` alone imports it with `import
all`, for the laws relating the two slots).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRunRes
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__revokeExpiredLeases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (open, the lease-grant plan's D2, 2026-11-02) **A snapshot payload's job in a cluster that
grants leases** (`KVNames.lg = true`; `run_job_snap`'s statement there): the obligation `run` takes
as `isServerRun`'s `%Hslg` (from `NewServer`'s precondition) instead of proving it. `applyAll.specSnap`
takes a cluster that grants none: its lessor is monotone, and `Recover` (the snapshot's restore)
takes a revocable one; besides, the snapshot's image then has leases (`specSnap`'s `hlease` is
false). It quantifies over every apply context, so it covers a member of a multi-member cluster,
which a leader may send a snapshot (a lagging follower, `raft.go`'s `maybeSendSnapshot`): it is not
vacuous outside the single-member examples, and restoring a snapshot with leases is a stage of its
own. Sealed (`srvGrantOpen`); `run` opens it with `srvGrantOpen_snap`. -/
def runSnapLgOkBody : Prop :=
  ∀ (C : ApplyCtx GF) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64),
  uint.nat C.ai₀ = 0 → uint.Z C.c₀ ≤ uint.Z C.ai₀ → γn.pre = [] →
  γn.node = C.γr.raft.raft → C.ρ.raft = C.γr.raft →
  C.γr.raft.pre = γn.pre → C.γs = γn.γs → C.γw = C.ρ.wait →
  A.length < A'.length →
  (γn.pre ++ A').length = uint.nat sv.Metadata'.Index' →
  uint.Z sv.Metadata'.Index' < 2 ^ 61 →
  (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index' →
  C.γr.kv.lg = true →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length ∗
            rnWalHanded γn (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyRes C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C A' }}

/-- (review S4, 2026-11-02; the lease-grant plan's B1/B2 commit 1, 2026-11-02: the bundle, until then
`runSnapLgOk`, the snapshot case alone) **The open cases of a lease-granting cluster, by name**: what
`NewServer`'s precondition names (`%Hslg`, gated on `lg = true`), sealed so that the statement a
client reads is a name, not the triples. Each case is a named field, opened by its law: the
snapshot job's triple (`runSnapLgOkBody`; `srvGrantOpen_snap` is how `run` uses it); the later
commits of the lease-grant plan add the grant's open cases as further fields. A cluster that
grants none discharges the gated premise by its `lg = false`; the open cases are in the trust base
of the lease-granting results only (`srvGrantOpen_open`, `EtcdServer__run.lean`). -/
@[no_expose] def srvGrantOpen : Prop := runSnapLgOkBody (GF := GF)

/-- The bundle's snapshot field (`run_job_snap`'s premise at `lg = true`). -/
theorem srvGrantOpen_snap : srvGrantOpen (GF := GF) → runSnapLgOkBody (GF := GF) := id

/-- (the lease-expiry plan's X5, revision 4, 2026-11-04; Part X-a) **The open case of a
revocable-lease cluster, by name**: `run`'s expiry arm calls `revokeExpiredLeases`
(`EtcdServer.revokeExpiredLeases.spec`), whose proof waits on thread tokens by level (the plan's
P1). `run` takes it as `lease.runCfg`'s revocable conjunct instead of a callee spec, so that its
proof (a marked `sorry` once written) is in the trust base of the revocable cluster's results only,
as `srvGrantOpen` is of the granting ones'. Sealed; `run` opens it with `srvRevokeOpen_spec`. -/
@[no_expose] def srvRevokeOpen : Prop := EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG)

/-- The open case's triple (`run`'s expiry arm in the revocable mode). -/
theorem srvRevokeOpen_spec :
    srvRevokeOpen (GF := GF) → EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG) := id
end defs

-- `lease.Mode`: `Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean` (2026-11-04, X2: `srvSnapRO`
-- and the rest model name it, below this module).

section runCfg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the running server takes of the lease subsystem** (sealed), at the KV names' lease mode
`lm` and the lease mode `m`: `lm` is `m` (the lease-expiry plan's X7 option (iii), 2026-11-04: until
then the grant flag `lg` with `lg = decide (m ≠ none)`); in the monotone mode, no lease expires
during the run; in a granting mode, the open cases of a granting cluster (`srvGrantOpen`, until the
plan's S4); in the revocable mode, the open case of the expiry arm (`srvRevokeOpen`; the expiry
stage's Part X-a, 2026-11-04: until then `m = revocable → False`, and `srvGrantOpen` only at
`mono`). The server's inner predicates carry `∃ m, lease.runCfg lm m` (`lease.runCfg_none`,
`lease.runCfg_mono` and `lease.runCfg_revocable` give it; `lease.runCfg_open`, `_noExpiry`,
`_revoke`, `_lm` and `LeaseApi.lean`'s `lease.bootCfg_of_run` use it). -/
@[no_expose] def lease.runCfg (lm : lease.Mode) (m : lease.Mode) : Prop :=
  lm = m ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m ≠ .none → srvGrantOpen (GF := GF)) ∧ (m = .revocable → srvRevokeOpen (GF := GF) (hG := hG))

/-- `lease.runCfg` for a cluster that grants no lease. -/
theorem lease.runCfg_none : lease.runCfg (GF := GF) .none .none := by
  unfold lease.runCfg
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> intro h <;> first | cases h | exact absurd rfl h

/-- `lease.runCfg` for a cluster that grants monotone leases: no lease expiring during the run, the
open cases. -/
theorem lease.runCfg_mono (hne : lease.leasesNoExpiry) (hopen : srvGrantOpen (GF := GF)) :
    lease.runCfg (GF := GF) .mono .mono := by
  unfold lease.runCfg
  refine ⟨rfl, fun _ => hne, fun _ => hopen, ?_⟩
  intro h; cases h

/-- `lease.runCfg` for a cluster that grants revocable leases: the open cases of a granting cluster
and of the expiry arm. -/
theorem lease.runCfg_revocable (hopen : srvGrantOpen (GF := GF))
    (hrev : srvRevokeOpen (GF := GF) (hG := hG)) : lease.runCfg (GF := GF) .revocable .revocable := by
  unfold lease.runCfg
  refine ⟨rfl, ?_, fun _ => hopen, fun _ => hrev⟩
  intro h; cases h

/-- **The KV names' mode is the mode** (X7 option (iii); until then `lease.runCfg_lg`). -/
theorem lease.runCfg_lm {lm : lease.Mode} {m : lease.Mode} (h : lease.runCfg (GF := GF) lm m) :
    lm = m := h.1

/-- **What `run`'s snapshot job takes from `lease.runCfg`** in a granting cluster: the open cases
(`srvGrantOpen`). -/
theorem lease.runCfg_open {lm m : lease.Mode} (hlm : lm ≠ .none) (h : lease.runCfg (GF := GF) lm m) :
    srvGrantOpen (GF := GF) := by
  obtain ⟨hlg, -, hopen, -⟩ := h
  exact hopen (hlg ▸ hlm)

/-- **What `run`'s expiry arm takes from `lease.runCfg` in the monotone mode**: no lease expires
during the run (against the expired slice's `¬ leasesNoExpiry`: the arm is dead). -/
theorem lease.runCfg_noExpiry {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .mono) :
    lease.leasesNoExpiry := h.2.1 rfl

/-- **What `run`'s expiry arm takes from `lease.runCfg` in the revocable mode**: the open case
(`srvRevokeOpen`, opened by `srvRevokeOpen_spec`). -/
theorem lease.runCfg_revoke {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .revocable) :
    srvRevokeOpen (GF := GF) (hG := hG) := h.2.2.2 rfl

end runCfg

end EtcdGrove
end Perennial
