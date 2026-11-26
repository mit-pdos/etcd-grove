/-
**`foreign`'s two lessor-read refutations at the view, as a hypothesis** (F7 stage S5, 2026-11-26; the
lead, #50 07:01Z; `notes/etcd-dist-f7.md`, "Handoff S5-3" and "Handoff S5-4").

`foreign(ucli, "u", lz)` and `foreign(vcli, "v", lu)` (`examples/etcd/dist/client/authlease.go`) end with a
`TimeToLive(id, WithAttachedKeys())` and a `Leases()` that must be refused. `foreign.spec` takes the caller's
refutations of both successes. Refuting them needs member `mid`'s lessor (`Γ.ls mid`, another member than the
granting one) to hold the lease with its key from some index on; in one process that was `cell_holds` over
`lessor_keys_of_read`, which is stated false outside raft's no-snapshot mode, and the dist cluster is not in
that mode (`ClusterOk`'s `¬ clusterNoSnap`). So at the view this is **not provable** from the published
facts, and may be false of this deployment (`nonissues/etcd-lease-keys-mid-apply.md`, "A second window: after a
snapshot").

It is therefore a separate, named hypothesis of `RunAuthLease.wp_proof`: neither proved nor axiomatized, and
`RunAuthLease` is linked into no `Results` root while it stands. Upamanyu decides `foreign`'s form; whichever
form is adopted replaces this law (if the two calls go, the law and its two uses go with them).

The statement is the dist form of the single-process `cell_holds` + `foreign_reads_refuted`, at what
`RunAuthLease` holds at `foreign`'s calls: the frozen set-up (`authHistFrozen` at `Lset`, its state `setupSt
r`), member `mid`'s barrier floor above it, the cell (allocated at `Γ.kv`) seen past the three attachments with
`Lz`, `Lu` fixed, and the principal: `u` against `Lz` (holding `z/lease`) or `v` against `Lu` (holding
`a/lease`). It gives the published lower bounds `n₀`, `m₀` and the two refutations at `R` the main thread's
unpermitted revocation (`monoNatAuthOwn γc.a ½ 0`), exactly `foreign.spec`'s two premises.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthCell
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd etcd_authlease

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev foreignReads.law : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (γc : CellNames) (γz : GName)
    (hs : List auth.AuthState) (Lset L₀ : List EntryModel) (r : Nat) (mid : w64) (m : Nat)
    (ps1 : List Nat) (d1 : Nat) (σ : KVState) (Lz Lu id : w64) (k : GoString) (P : Option GoString),
  Γ.auth = true → Lset <+: L₀ → admStates Γ.kv srvAuthSt0 Lset = hs →
  srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r → 3 ≤ ps1.length →
  ((P = some go!"u" ∧ id = Lz ∧ k = zK) ∨ (P = some go!"v" ∧ id = Lu ∧ k = aK)) →
  ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗ authFloorD Γ γR mid L₀ m -∗
    cellInv Γ.kv γc -∗ cellSeen γc ps1 d1 σ -∗ monoListLbOwn γc.ids [Lz, Lu] -∗ |={⊤}=>
    ∃ n₀ m₀ : Nat, auth.authPubLbM (.on (Γ.au mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ ∗
      □ (∀ (n j : Nat), ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ -∗
          leaseCheckD (Γ.au mid) P n
            (fun info => leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id .read) -∗
          monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False) ∗
      □ (∀ (n j : Nat) (ids : List w64), ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ -∗ lease.leaseIdsAt (Γ.ls mid) j ids -∗
          leaseCheckD (Γ.au mid) P n
            (fun info => iprop([∗list] id' ∈ ids,
              leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id' .read)) -∗
          monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False)

end law

end etcd_dist_client
end EtcdGrove
end Perennial
