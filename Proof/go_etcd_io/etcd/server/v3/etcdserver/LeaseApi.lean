/-
**The lease subsystem's slots in the boot hub** (2026-11-04; the lease-expiry plan's Part C,
`notes/lease-expiry-plan.md`, revision 4's C1; the slot convention, `notes/spec-first-plan.md`, "The
slot convention"). Lean-first.

`NewServer.specG` named the lease subsystem's premises and facts inline: the auth/lease coupling
(`on = true → lg = false`), the open cases of a cluster that grants leases (`lg = true →
leasesNoExpiry ∧ srvGrantOpen`, the latter gone since S2–S4), the lessor's checkpointer (`ckptEffectsOk`, deleted 2026-11-12), and four conjuncts of
its postcondition (the lessor finding no lease with auth on, deleted by auth-lease S3c, 2026-11-15;
the peers' round tripper, the lessor's reader side and its reader pool). They are now two sealed slots (`etc/import-all.txt`):

- `lease.bootCfg lm m on`, the subsystem's pure boot premise, at the lease mode `m` the caller
  chooses (`lease.Mode`: no grants, monotone grants, or revocable grants);
- `lease.srvInv on s E m`, the subsystem's part of the built server (a first start's: the
  lessor's history from the empty snapshot; `lease.srvInvAt on s E m σ₀`, from `σ₀`, a restart's).

A later change inside the lease subsystem (the expiry stage's Part X: admitting the revocable mode)
changes their bodies and laws, not the hub's text. No `lease.Names` yet: the mode is the only datum
the caller chooses (the lessor's ghost name is `NewLessor`'s, in the post's `(mvcc.api.mvccLeases E.γ)`), and
`lg` stays `KVNames.lg` (the plan's C2).

Couplings: `bootCfg`'s `on` is the auth mode; the coupling (with auth on, in a granting mode no lease
expires; auth-lease S3c, 2026-11-15: until then "auth on grants no lease") is owned by lease, with
auth's mode as its parameter; `lg` is the KV names' grant flag, tied to the mode by
`lg = decide (m ≠ none)`; since X7 option (iii) (2026-11-04) the KV names' mode `lm`, tied by
`lm = m` (`lease.bootCfg_lm`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
import all Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

-- `lease.Mode`: `LeaseRun.lean` (2026-11-04, for `lease.runCfg`).

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The lease subsystem's boot premise** (sealed), at the KV names' lease mode `lm`, the lease mode
`m` and the auth mode `on`: `lm` is `m` (the lease-expiry plan's X7 option (iii), 2026-11-04: until
then the KV names' grant flag `lg` with `lg = decide (m ≠ none)`, which `lm = m` gives,
`KVNames.lg`); with auth on, in the revocable mode, no lease expires during the run (the
auth/lease coupling, owned by lease with auth's mode as its parameter; auth-lease S3c, 2026-11-15,
the hub change: until then, from the lease-grant stage's 2.13, "with auth on, no lease granted",
`m = none`); in the monotone mode, no lease expires during the run; in the revocable mode the open
case of `run`'s expiry arm (`srvRevokeOpen`; the expiry stage's Part X-a, 2026-11-04: until then
`m = revocable → False`). (Until 2026-11-12 also the lessor's checkpointer's effects, the opaque
`ckptEffectsOk`, `NewLessor`'s premise, deleted: no checkpointer is installed, `lessorInv` records
`cp = nil`, so it covered no call. Until the plan's S2–S4, 2026-11-05, also in a granting mode the open case of a granting
cluster's snapshot job, `srvGrantOpen`.) At `m = none` exactly the premises `NewServer.specG`
stated inline until 2026-11-04. -/
@[no_expose] def lease.bootCfg (lm : lease.Mode) (m : lease.Mode) (on : Bool) : Prop :=
  lm = m ∧ (on = true → m = .revocable → lease.leasesNoExpiry) ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG))

/-- `lease.bootCfg` for a cluster that grants no lease (every non-granting example), in either auth
mode. -/
theorem lease.bootCfg_none (lm : lease.Mode) (on : Bool) (hlm : lm = .none) :
    lease.bootCfg (GF := GF) lm .none on := by
  unfold lease.bootCfg
  subst hlm
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro _ h; cases h
  · intro h; cases h
  · intro h; cases h

/-- `lease.bootCfg` for a cluster that grants monotone leases (`examples/etcd/leasegrant`), in either
auth mode (auth-lease S3c: until then auth off), no lease expiring during the run. -/
theorem lease.bootCfg_mono (lm : lease.Mode) (on : Bool) (hlm : lm = .mono)
    (hne : lease.leasesNoExpiry) :
    lease.bootCfg (GF := GF) lm .mono on := by
  unfold lease.bootCfg
  subst hlm
  refine ⟨rfl, ?_, fun _ => hne, ?_⟩
  · intro _ h; cases h
  · intro h; cases h

/-- **The KV names' mode is the mode** (X7 option (iii); until then `lease.bootCfg_lg`, the grant
flag `lg = decide (m ≠ none)`, which follows). -/
theorem lease.bootCfg_lm {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : lm = m := h.1

/-- **What the auth mode takes from `lease.bootCfg`** (`NewServer`'s grant guard, `srvGrantGuard`;
auth-lease S3c, 2026-11-15, in place of `bootCfg_auth`'s "auth on grants no lease"): in a granting
cluster with auth on, no lease expires. -/
theorem lease.bootCfg_noExpiry {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) (hon : on = true) (hg : lm ≠ .none) :
    lease.leasesNoExpiry := by
  obtain ⟨hlm, hr, hmono, -⟩ := h
  subst hlm
  cases hc : lm with
  | none => exact absurd hc hg
  | mono => exact hmono hc
  | revocable => exact hr hon hc

/-- **The running server's lease premise from the boot slot** (`NewServer`'s construction premise
for `start` and `run`, `srvBuilt`'s `%Hslg`): `lease.runCfg` at the same KV mode and mode. -/
theorem lease.bootCfg_run {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : lease.runCfg (GF := GF) lm m := by
  unfold lease.bootCfg at h
  unfold lease.runCfg
  obtain ⟨hlg, -, hmono, hrev⟩ := h
  exact ⟨hlg, hmono, hrev⟩

/-- **The boot slot from the running server's lease premise** (`etcdstart`'s `newServerMode`, from
`memberBoot`'s `lease.runCfg`): with the auth/lease coupling at the auth mode `on` (auth-lease S3c:
with auth on, in the revocable mode no lease expires; until then `on = true → m = none`) (until
2026-11-12 also the lessor's checkpointer's `ckptEffectsOk`). -/
theorem lease.bootCfg_of_run {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.runCfg (GF := GF) lm m) (hon : on = true → m = .revocable → lease.leasesNoExpiry) :
    lease.bootCfg (GF := GF) lm m on := by
  unfold lease.runCfg at h
  unfold lease.bootCfg
  obtain ⟨hlg, hmono, hrev⟩ := h
  exact ⟨hlg, hon, hmono, hrev⟩

/-- **The lease subsystem's part of the built server, its lessor's history starting at `σ₀`**
(sealed, persistent), of the server `s` at the apply environment `E` (whose
`(mvcc.api.mvccLeases E.γ)` is the lessor's name), the auth mode `on` (unused since auth-lease S3c,
decision C2′, 2026-11-15: until then "with auth on, its lessor finds no lease", `srvLessorNil`, which no
apply-thread proof reads since S2) and the lease mode `m`: the
peers' round tripper (`srvPeerRt`, `LeaseRenew`'s forwarding); the lessor's reader side
(`srvLessorRd`) and its reader pool (`lease.lessorRdPool`, the lease checks' `Lookup`s); (the
lease-expiry plan's X2, 2026-11-04) the lessor's mode, monotone exactly in the mode `mono`
(`NewLessor`'s `decide (m = mono)`), which turns a grant's mode-free fact into `leaseGrantedAt`
(`lease.srvInvAt_grantedAt`); the lessor's history's first snapshot `σ₀` (`lease.lessorAt … 0 σ₀`,
`lease.srvInvAt_first`). (Restart S6, CP2 review finding 2, 2026-11-13: the first snapshot a
parameter, so that a restart, whose `NewLessor` recovers the leases of the image's `lease` bucket,
states the recovered one, `NewServer.specR`; a first start's is the empty one, `lease.srvInv`.) -/
@[no_expose] def lease.srvInvAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) : IProp GF :=
  iprop(srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool (mvcc.api.mvccLeases E.γ) ∗ lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗
    lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 σ₀)

instance lease.srvInvAt_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) : Persistent (lease.srvInvAt on s E m σ₀) := by
  unfold lease.srvInvAt; infer_instance

/-- **The lease subsystem's part of a first start's built server** (sealed, persistent): its
lessor's history starts empty (`lease.lessorAt … 0 (∅, ∅, ∅)`, `lease.srvInv_first`; the lease-expiry
plan's E3 (c), 2026-11-05), `lease.srvInvAt` at the empty snapshot (restart S6, CP2: until then the
body itself). -/
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    IProp GF :=
  lease.srvInvAt on s E m (∅, ∅, ∅)

instance lease.srvInv_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    Persistent (lease.srvInv on s E m) := by
  unfold lease.srvInv; infer_instance

/-- **`lease.srvInvAt` from `NewServer`'s construction**: its five facts. -/
theorem lease.srvInvAt_intro (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) :
    srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
      lease.lessorRdPool (mvcc.api.mvccLeases E.γ) ∗ lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗
      lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 σ₀ ⊢
      lease.srvInvAt on s E m σ₀ := by
  unfold lease.srvInvAt; exact .rfl

/-- **`lease.srvInv` from `NewServer`'s construction**: its five facts. -/
theorem lease.srvInv_intro (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
      lease.lessorRdPool (mvcc.api.mvccLeases E.γ) ∗ lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗
      lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 (∅, ∅, ∅) ⊢
      lease.srvInv on s E m := by
  unfold lease.srvInv; exact lease.srvInvAt_intro on s E m _

/-- **The lessor's history starts at `σ₀`**. -/
theorem lease.srvInvAt_first (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) :
    lease.srvInvAt on s E m σ₀ ⊢ lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 σ₀ := by
  unfold lease.srvInvAt
  iintro ⟨-, -, -, -, #H⟩
  iexact H

/-- **The lessor's history starts empty** (the lease-expiry plan's E3 (c), 2026-11-05): its first
snapshot has no lease, no item, no TTL. -/
theorem lease.srvInv_first (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 (∅, ∅, ∅) := by
  unfold lease.srvInv; exact lease.srvInvAt_first on s E m _

/-- **What `LeaseRenew`'s forwarding takes from `lease.srvInvAt`**: the peers' round tripper. -/
theorem lease.srvInvAt_peerRt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) : lease.srvInvAt on s E m σ₀ ⊢ srvPeerRt s := by
  unfold lease.srvInvAt
  iintro ⟨#H, -⟩
  iexact H

/-- **What `LeaseRenew`'s forwarding takes from `lease.srvInv`**. -/
theorem lease.srvInv_peerRt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ srvPeerRt s := by
  unfold lease.srvInv; exact lease.srvInvAt_peerRt on s E m _

/-- **What the served lease reads take from `lease.srvInvAt`** (`raftLeaseRead_server`, through
`etcdstart.srvLeaseRd`): the lessor's reader side and its reader pool. -/
theorem lease.srvInvAt_lessorRd (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (σ₀ : lease.LSnap) :
    lease.srvInvAt on s E m σ₀ ⊢
      srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗ lease.lessorRdPool (mvcc.api.mvccLeases E.γ) := by
  unfold lease.srvInvAt
  iintro ⟨-, #H1, #H2, -⟩
  iframe H1 H2

/-- **What the served lease reads take from `lease.srvInv`**. -/
theorem lease.srvInv_lessorRd (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗ lease.lessorRdPool (mvcc.api.mvccLeases E.γ) := by
  unfold lease.srvInv; exact lease.srvInvAt_lessorRd on s E m _

/-- (the lease-expiry plan's X2, 2026-11-04) **A grant's mode-free fact in the monotone mode**: a
lease live in the lessor's history from `i` (what the grant's reply carries, `leaseLiveFrom`) was
granted at an index `j ≥ i` of the monotone history (`leaseGrantedAt`, which every later listing
lists). What v3rpc's `lessorGrantOkLM_of_server` takes. Whatever the first snapshot. -/
theorem lease.srvInvAt_grantedAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (σ₀ : lease.LSnap)
    (i : Nat) (id : w64) (l : Loc) :
    lease.srvInvAt on s E .mono σ₀ ∗ lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i id l ⊢
      ∃ j : Nat, ⌜i ≤ j⌝ ∗ lease.leaseGrantedAt (mvcc.api.mvccLeases E.γ) j id := by
  unfold lease.srvInvAt
  rw [show decide (lease.Mode.mono = lease.Mode.mono) = true from rfl]
  iintro ⟨⟨-, -, -, #Hm, -⟩, #Hl⟩
  iapply lease.leaseGrantedAt_of_live (mvcc.api.mvccLeases E.γ) i id l
  isplitl
  · iexact Hm
  · iexact Hl

/-- `lease.srvInvAt_grantedAt` at a first start. -/
theorem lease.srvInv_grantedAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (i : Nat) (id : w64)
    (l : Loc) :
    lease.srvInv on s E .mono ∗ lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i id l ⊢
      ∃ j : Nat, ⌜i ≤ j⌝ ∗ lease.leaseGrantedAt (mvcc.api.mvccLeases E.γ) j id := by
  unfold lease.srvInv; exact lease.srvInvAt_grantedAt on s E _ i id l

end slots

end EtcdGrove
end Perennial
