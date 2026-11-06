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

/-- (the lease-expiry plan's X5, revision 4, 2026-11-04; Part X-a) **The open case of a
revocable-lease cluster, by name**: `run`'s expiry arm calls `revokeExpiredLeases`
(`EtcdServer.revokeExpiredLeases.spec`), whose proof waits on thread tokens by level (the plan's
P1). `run` takes it as `lease.runCfg`'s revocable conjunct instead of a callee spec, so that its
proof (a marked `sorry` once written) is in the trust base of the revocable cluster's results only
(as `srvGrantOpen`, the granting cluster's snapshot job, was of the granting ones' until the plan's
S2–S4 removed it, 2026-11-05). Sealed; `run` opens it with `srvRevokeOpen_spec`. -/
@[no_expose] def srvRevokeOpen : Prop := EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG)

/-- The open case's triple (`run`'s expiry arm in the revocable mode). -/
theorem srvRevokeOpen_spec :
    srvRevokeOpen (GF := GF) → EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG) := id

/-- (revoke-open, 2026-11-06) The open case, from a proof of the spec (`leaseexpiry`'s
`MainLinked`). -/
theorem srvRevokeOpen_intro (h : EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG)) :
    srvRevokeOpen (GF := GF) (hG := hG) := h
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
during the run; in the revocable mode, the open case of the expiry arm (`srvRevokeOpen`; the expiry
stage's Part X-a, 2026-11-04: until then `m = revocable → False`), with the level bound its goroutines
need (`srvRevokeLevels`, revoke-open Q1 (a2), 2026-11-06). (Until the plan's S2–S4,
2026-11-05, also in a granting mode the open case of a granting cluster's snapshot job,
`srvGrantOpen`: `run`'s snapshot job now restores a snapshot with leases, `applyAll.specSnap` at
every lease mode.) The server's inner predicates carry `∃ m, lease.runCfg lm m`
(`lease.runCfg_none`, `lease.runCfg_mono` and `lease.runCfg_revocable` give it; `_noExpiry`,
`_revoke`, `_lm` and `LeaseApi.lean`'s `lease.bootCfg_of_run` use it). -/
@[no_expose] def lease.runCfg (lm : lease.Mode) (m : lease.Mode) : Prop :=
  lm = m ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG))

/-- `lease.runCfg` for a cluster that grants no lease. -/
theorem lease.runCfg_none : lease.runCfg (GF := GF) .none .none := by
  unfold lease.runCfg
  refine ⟨rfl, ?_, ?_⟩ <;> intro h <;> cases h

/-- `lease.runCfg` for a cluster that grants monotone leases: no lease expiring during the run. -/
theorem lease.runCfg_mono (hne : lease.leasesNoExpiry) : lease.runCfg (GF := GF) .mono .mono := by
  unfold lease.runCfg
  refine ⟨rfl, fun _ => hne, ?_⟩
  intro h; cases h

/-- `lease.runCfg` for a cluster that grants revocable leases: the level bound and the open case of
the expiry arm. -/
theorem lease.runCfg_revocable (hlev : srvRevokeLevels (GF := GF))
    (hrev : srvRevokeOpen (GF := GF) (hG := hG)) :
    lease.runCfg (GF := GF) .revocable .revocable := by
  unfold lease.runCfg
  refine ⟨rfl, ?_, fun _ => ⟨hlev, hrev⟩⟩
  intro h; cases h

/-- **The KV names' mode is the mode** (X7 option (iii); until then `lease.runCfg_lg`). -/
theorem lease.runCfg_lm {lm : lease.Mode} {m : lease.Mode} (h : lease.runCfg (GF := GF) lm m) :
    lm = m := h.1

/-- **What `run`'s expiry arm takes from `lease.runCfg` in the monotone mode**: no lease expires
during the run (against the expired slice's `¬ leasesNoExpiry`: the arm is dead). -/
theorem lease.runCfg_noExpiry {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .mono) :
    lease.leasesNoExpiry := h.2.1 rfl

/-- **What `run`'s expiry arm takes from `lease.runCfg` in the revocable mode**: the level bound
(`srvRevokeLevels`) and the open case (`srvRevokeOpen`, opened by `srvRevokeOpen_spec`). -/
theorem lease.runCfg_revoke {lm : lease.Mode} (h : lease.runCfg (GF := GF) lm .revocable) :
    srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG) := h.2.2 rfl

end runCfg

end EtcdGrove
end Perennial
