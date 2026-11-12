/-
**The lease subsystem's slots in the boot hub** (2026-11-04; the lease-expiry plan's Part C,
`notes/lease-expiry-plan.md`, revision 4's C1; the slot convention, `notes/spec-first-plan.md`, "The
slot convention"). Lean-first.

`NewServer.specG` named the lease subsystem's premises and facts inline: the auth/lease coupling
(`on = true → lg = false`), the open cases of a cluster that grants leases (`lg = true →
leasesNoExpiry ∧ srvGrantOpen`, the latter gone since S2–S4), the lessor's checkpointer (`ckptEffectsOk`), and four conjuncts of
its postcondition (the lessor finding no lease with auth on, the peers' round tripper, the lessor's
reader side and its reader pool). They are now two sealed slots (`etc/import-all.txt`):

- `lease.bootCfg lm m on`, the subsystem's pure boot premise, at the lease mode `m` the caller
  chooses (`lease.Mode`: no grants, monotone grants, or revocable grants);
- `lease.srvInv on s E m`, the subsystem's part of the built server.

A later change inside the lease subsystem (the expiry stage's Part X: admitting the revocable mode)
changes their bodies and laws, not the hub's text. No `lease.Names` yet: the mode is the only datum
the caller chooses (the lessor's ghost name is `NewLessor`'s, in the post's `(mvcc.api.mvccLeases E.γ)`), and
`lg` stays `KVNames.lg` (the plan's C2).

Couplings: `bootCfg`'s `on` is the auth mode; the coupling (auth on grants no lease) is owned by
lease, with auth's mode as its parameter; `lg` is the KV names' grant flag, tied to the mode by
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
`KVNames.lg`); with auth on, no lease granted (the
auth/lease coupling, the lease-grant stage's 2.13, owned by lease with auth's mode as its
parameter); in the monotone mode, no lease expires during the run; in the revocable mode the open
case of `run`'s expiry arm (`srvRevokeOpen`; the expiry stage's Part X-a, 2026-11-04: until then
`m = revocable → False`); and the lessor's checkpointer's effects (`ckptEffectsOk`, `NewLessor`'s
premise). (Until the plan's S2–S4, 2026-11-05, also in a granting mode the open case of a granting
cluster's snapshot job, `srvGrantOpen`.) At `m = none` exactly the premises `NewServer.specG`
stated inline until 2026-11-04. -/
@[no_expose] def lease.bootCfg (lm : lease.Mode) (m : lease.Mode) (on : Bool) : Prop :=
  lm = m ∧ (on = true → m = .none) ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG)) ∧
    ckptEffectsOk

/-- `lease.bootCfg` for a cluster that grants no lease (every non-granting example), in either auth
mode. -/
theorem lease.bootCfg_none (lm : lease.Mode) (on : Bool) (hlm : lm = .none) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lm .none on := by
  unfold lease.bootCfg
  subst hlm
  refine ⟨rfl, fun _ => rfl, ?_, ?_, hck⟩ <;> intro h <;> cases h

/-- `lease.bootCfg` for a cluster that grants monotone leases (`examples/etcd/leasegrant`): auth
off, no lease expiring during the run. -/
theorem lease.bootCfg_mono (lm : lease.Mode) (on : Bool) (hlm : lm = .mono) (hon : on = false)
    (hne : lease.leasesNoExpiry) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lm .mono on := by
  unfold lease.bootCfg
  subst hlm hon
  refine ⟨rfl, ?_, fun _ => hne, ?_, hck⟩ <;> intro h <;> cases h

/-- **The KV names' mode is the mode** (X7 option (iii); until then `lease.bootCfg_lg`, the grant
flag `lg = decide (m ≠ none)`, which follows). -/
theorem lease.bootCfg_lm {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : lm = m := h.1

/-- **What the auth mode takes from `lease.bootCfg`** (`NewServer`'s auth-on construction): with
auth on, the cluster grants no lease. -/
theorem lease.bootCfg_auth {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : on = true → lm = .none := by
  intro hon
  rw [h.1, h.2.1 hon]

/-- **What `NewLessor` takes from `lease.bootCfg`**: the checkpointer's effects. -/
theorem lease.bootCfg_ckpt {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : ckptEffectsOk := h.2.2.2.2

/-- **The running server's lease premise from the boot slot** (`NewServer`'s construction premise
for `start` and `run`, `srvBuilt`'s `%Hslg`): `lease.runCfg` at the same KV mode and mode. -/
theorem lease.bootCfg_run {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.bootCfg (GF := GF) lm m on) : lease.runCfg (GF := GF) lm m := by
  unfold lease.bootCfg at h
  unfold lease.runCfg
  obtain ⟨hlg, -, hmono, hrev, -⟩ := h
  exact ⟨hlg, hmono, hrev⟩

/-- **The boot slot from the running server's lease premise** (`etcdstart`'s `newServerMode`, from
`memberBoot`'s `lease.runCfg`): with the auth/lease coupling at the auth mode `on` and the lessor's
checkpointer. -/
theorem lease.bootCfg_of_run {lm : lease.Mode} {m : lease.Mode} {on : Bool}
    (h : lease.runCfg (GF := GF) lm m) (hon : on = true → m = .none) (hck : ckptEffectsOk) :
    lease.bootCfg (GF := GF) lm m on := by
  unfold lease.runCfg at h
  unfold lease.bootCfg
  obtain ⟨hlg, hmono, hrev⟩ := h
  exact ⟨hlg, hon, hmono, hrev, hck⟩

/-- **The lease subsystem's part of the built server** (sealed, persistent), of the server `s` at
the apply environment `E` (whose `(mvcc.api.mvccLeases E.γ)` is the lessor's name), the auth mode `on` and the lease
mode `m`: with auth on, its lessor finds no lease (`srvLessorNil`, what `start.specOn`'s apply thread
takes); the peers' round tripper (`srvPeerRt`, `LeaseRenew`'s forwarding); the lessor's reader side
(`srvLessorRd`) and its reader pool (`lease.lessorRdPool`, the lease checks' `Lookup`s); (the
lease-expiry plan's X2, 2026-11-04) the lessor's mode, monotone exactly in the mode `mono`
(`NewLessor`'s `decide (m = mono)`), which turns a grant's mode-free fact into `leaseGrantedAt`
(`lease.srvInv_grantedAt`); (the lease-expiry plan's E3 (c), 2026-11-05) the lessor's history
starts empty (`lease.lessorAt … 0 (∅, ∅, ∅)`, `lease.srvInv_first`). -/
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    IProp GF :=
  iprop(□ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool (mvcc.api.mvccLeases E.γ) ∗ lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗
    lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 (∅, ∅, ∅))

instance lease.srvInv_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    Persistent (lease.srvInv on s E m) := by
  unfold lease.srvInv; infer_instance

/-- **`lease.srvInv` from `NewServer`'s construction**: its six facts. -/
theorem lease.srvInv_intro (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    □ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
      lease.lessorRdPool (mvcc.api.mvccLeases E.γ) ∗ lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (m = .mono)) ∗
      lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 (∅, ∅, ∅) ⊢
      lease.srvInv on s E m := by
  unfold lease.srvInv; exact .rfl

/-- **The lessor's history starts empty** (the lease-expiry plan's E3 (c), 2026-11-05): its first
snapshot has no lease, no item, no TTL. -/
theorem lease.srvInv_first (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) :
    lease.srvInv on s E m ⊢ lease.lessorAt (mvcc.api.mvccLeases E.γ) 0 (∅, ∅, ∅) := by
  unfold lease.srvInv
  iintro ⟨-, -, -, -, -, #H⟩
  iexact H

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
    lease.srvInv on s E m ⊢ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗ lease.lessorRdPool (mvcc.api.mvccLeases E.γ) := by
  unfold lease.srvInv
  iintro ⟨-, -, #H1, #H2, -⟩
  iframe H1 H2

/-- (the lease-expiry plan's X2, 2026-11-04) **A grant's mode-free fact in the monotone mode**: a
lease live in the lessor's history from `i` (what the grant's reply carries, `leaseLiveFrom`) was
granted at an index `j ≥ i` of the monotone history (`leaseGrantedAt`, which every later listing
lists). What v3rpc's `lessorGrantOkL_of_server` takes. -/
theorem lease.srvInv_grantedAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (i : Nat) (id : w64)
    (l : Loc) :
    lease.srvInv on s E .mono ∗ lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i id l ⊢
      ∃ j : Nat, ⌜i ≤ j⌝ ∗ lease.leaseGrantedAt (mvcc.api.mvccLeases E.γ) j id := by
  unfold lease.srvInv
  rw [show decide (lease.Mode.mono = lease.Mode.mono) = true from rfl]
  iintro ⟨⟨-, -, -, -, #Hm, -⟩, #Hl⟩
  iapply lease.leaseGrantedAt_of_live (mvcc.api.mvccLeases E.γ) i id l
  isplitl
  · iexact Hm
  · iexact Hl

end slots

end EtcdGrove
end Perennial
