/-
**The lease subsystem's slots in the boot hub** (2026-11-04; the lease-expiry plan's Part C,
`notes/lease-expiry-plan.md`, revision 4's C1; the slot convention, `notes/spec-first-plan.md`, "The
slot convention"). Lean-first.

`NewServer.specG` named the lease subsystem's premises and facts inline: the auth/lease coupling
(`on = true → lg = false`), the open cases of a cluster that grants leases (`lg = true →
leasesNoExpiry ∧ srvGrantOpen`), the lessor's checkpointer (`ckptEffectsOk`), and four conjuncts of
its postcondition (the lessor finding no lease with auth on, the peers' round tripper, the lessor's
reader side and its reader pool). They are now two sealed slots (`etc/import-all.txt`):

- `lease.bootCfg lg m on`, the subsystem's pure boot premise, at the lease mode `m` the caller
  chooses (`lease.Mode`: no grants, monotone grants, or revocable grants);
- `lease.srvInv on s E m`, the subsystem's part of the built server.

A later change inside the lease subsystem (the expiry stage's Part X: admitting the revocable mode)
changes their bodies and laws, not the hub's text. No `lease.Names` yet: the mode is the only datum
the caller chooses (the lessor's ghost name is `NewLessor`'s, in the post's `E.γ.leases`), and
`lg` stays `KVNames.lg` (the plan's C2).

Couplings: `bootCfg`'s `on` is the auth mode; the coupling (auth on grants no lease) is owned by
lease, with auth's mode as its parameter; `lg` is the KV names' grant flag, tied to the mode by
`lg = decide (m ≠ none)` (`lease.bootCfg_lg`).
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

/-- **The lease subsystem's boot premise** (sealed), at the KV names' grant flag `lg`, the lease mode
`m` and the auth mode `on`: `lg` is whether `m` grants; with auth on, no lease granted (the
auth/lease coupling, the lease-grant stage's 2.13, owned by lease with auth's mode as its
parameter); in the monotone mode, no lease expires during the run and the open cases of a granting
cluster (`srvGrantOpen`); the revocable mode not admitted (`False`: the placeholder until the expiry
stage's Part X admits it); and the lessor's checkpointer's effects (`ckptEffectsOk`, `NewLessor`'s
premise). At `m = none` (`lg = false`) and `m = mono` (`lg = true`) exactly the premises
`NewServer.specG` stated inline until 2026-11-04. -/
@[no_expose] def lease.bootCfg (lg : Bool) (m : lease.Mode) (on : Bool) : Prop :=
  lg = decide (m ≠ .none) ∧ (on = true → m = .none) ∧
    (m = .mono → lease.leasesNoExpiry ∧ srvGrantOpen (GF := GF)) ∧
    (m = .revocable → False) ∧ ckptEffectsOk

/-- `lease.bootCfg` for a cluster that grants no lease (every non-granting example), in either auth
mode. -/
theorem lease.bootCfg_none (lg on : Bool) (hlg : lg = false) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lg .none on := by
  unfold lease.bootCfg
  subst hlg
  refine ⟨by decide, fun _ => rfl, ?_, ?_, hck⟩ <;> intro h <;> cases h

/-- `lease.bootCfg` for a cluster that grants monotone leases (`examples/etcd/leasegrant`): auth
off, no lease expiring during the run, the open cases. -/
theorem lease.bootCfg_mono (lg on : Bool) (hlg : lg = true) (hon : on = false)
    (hne : lease.leasesNoExpiry) (hopen : srvGrantOpen (GF := GF)) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lg .mono on := by
  unfold lease.bootCfg
  subst hlg hon
  refine ⟨by decide, ?_, fun _ => ⟨hne, hopen⟩, ?_, hck⟩ <;> intro h <;> cases h

/-- **The grant flag is the mode's**: `lg` is whether the mode grants leases. -/
theorem lease.bootCfg_lg {lg : Bool} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lg m on) : lg = decide (m ≠ .none) := h.1

/-- **What the auth mode takes from `lease.bootCfg`** (`NewServer`'s auth-on construction): with
auth on, the cluster grants no lease. -/
theorem lease.bootCfg_auth {lg : Bool} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lg m on) : on = true → lg = false := by
  intro hon
  rw [h.1, h.2.1 hon]
  decide

/-- **What `NewLessor` takes from `lease.bootCfg`**: the checkpointer's effects. -/
theorem lease.bootCfg_ckpt {lg : Bool} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lg m on) : ckptEffectsOk := h.2.2.2.2

/-- **What `run`'s snapshot job takes from `lease.bootCfg`** in a granting cluster: the open cases
(`srvGrantOpen`, `isServerRun`'s `%Hslg`). -/
theorem lease.bootCfg_open {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) true m on) : srvGrantOpen (GF := GF) := by
  obtain ⟨hlg, -, hmono, hrev, -⟩ := h
  cases m with
  | none => exact absurd hlg (by decide)
  | mono => exact (hmono rfl).2
  | revocable => exact (hrev rfl).elim

/-- **What the server's grant guard takes from `lease.bootCfg`** in a granting cluster: no lease
expires during the run (`leasesNoExpiry`, `isServerRun`'s `%Hslg`). -/
theorem lease.bootCfg_noExpiry {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) true m on) : lease.leasesNoExpiry := by
  obtain ⟨hlg, -, hmono, hrev, -⟩ := h
  cases m with
  | none => exact absurd hlg (by decide)
  | mono => exact (hmono rfl).1
  | revocable => exact (hrev rfl).elim

/-- **The running server's lease premise from the boot slot** (`NewServer`'s construction premise
for `start` and `run`, `srvBuilt`'s `%Hslg`): `lease.runCfg` at the same flag and mode. -/
theorem lease.bootCfg_run {lg : Bool} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lg m on) : lease.runCfg (GF := GF) lg m := by
  unfold lease.bootCfg at h
  unfold lease.runCfg
  obtain ⟨hlg, -, hmono, hrev, -⟩ := h
  exact ⟨hlg, hmono, hrev⟩

/-- **The boot slot from the running server's lease premise** (`etcdstart`'s `newServerMode`, from
`memberBoot`'s `lease.runCfg`): with the auth/lease coupling at the auth mode `on` and the lessor's
checkpointer. -/
theorem lease.bootCfg_of_run {lg : Bool} {m : lease.Mode} {on : Bool}
    (h : lease.runCfg (GF := GF) lg m) (hon : on = true → m = .none) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lg m on := by
  unfold lease.runCfg at h
  unfold lease.bootCfg
  obtain ⟨hlg, hmono, hrev⟩ := h
  exact ⟨hlg, hon, hmono, hrev, hck⟩

-- `m` is not read yet (Part X)
set_option linter.unusedVariables false in
/-- **The lease subsystem's part of the built server** (sealed, persistent), of the server `s` at
the apply environment `E` (whose `E.γ.leases` is the lessor's name), the auth mode `on` and the lease
mode `m` (not read yet: the expiry stage's Part X adds the lessor's mode here): with auth on, its
lessor finds no lease (`srvLessorNil`, what `start.specOn`'s apply thread takes); the peers' round
tripper (`srvPeerRt`, `LeaseRenew`'s forwarding); the lessor's reader side (`srvLessorRd`) and its
reader pool (`lease.lessorRdPool`, the lease checks' `Lookup`s). -/
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    IProp GF :=
  iprop(□ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s E.γ.leases ∗
    lease.lessorRdPool E.γ.leases)

instance lease.srvInv_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    Persistent (lease.srvInv on s E m) := by
  unfold lease.srvInv; infer_instance

/-- **`lease.srvInv` from `NewServer`'s construction**: its four facts. -/
theorem lease.srvInv_intro (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    □ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s E.γ.leases ∗
      lease.lessorRdPool E.γ.leases ⊢ lease.srvInv on s E m := by
  unfold lease.srvInv; exact .rfl

/-- **What the auth-on start takes from `lease.srvInv`** (`start.specOn`'s apply thread): with auth
on, the lessor finds no lease. -/
theorem lease.srvInv_lessorNil (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode)
    (hon : on = true) : lease.srvInv on s E m ⊢ srvLessorNil s := by
  unfold lease.srvInv
  iintro ⟨#Hn, -⟩
  iapply Hn
  ipureintro; exact hon

/-- **What `LeaseRenew`'s forwarding takes from `lease.srvInv`**: the peers' round tripper. -/
theorem lease.srvInv_peerRt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ srvPeerRt s := by
  unfold lease.srvInv
  iintro ⟨-, #H, -⟩
  iexact H

/-- **What the served lease reads take from `lease.srvInv`** (`raftLeaseRead_server`, through
`etcdstart.srvLeaseRd`): the lessor's reader side and its reader pool. -/
theorem lease.srvInv_lessorRd (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ srvLessorRd s E.γ.leases ∗ lease.lessorRdPool E.γ.leases := by
  unfold lease.srvInv
  iintro ⟨-, -, #H1, #H2⟩
  iframe H1 H2

end slots

end EtcdGrove
end Perennial
