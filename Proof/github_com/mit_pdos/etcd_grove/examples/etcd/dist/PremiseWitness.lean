/- Lean-first (no Rocq counterpart).

# `etcd/dist`: per-premise satisfiability lemmas for the dist statements

These are the premises of `etcd_robust_nocrash.spec` (and of its scoped variants, M1's
`etcd_kv_safe_nocrash.spec`) at concrete values. A statement's `TopLevelWitness.lean` composes them
into its `premise_sat%` theorem (`Robustness/PremiseSat.lean`). The module is shared with P12 (#50), which
adds the remaining premises' lemmas here under these names.

The member is `putget_safe`'s witness member (`putget/TopLevelWitness.lean`): `putgetd`, peer address
`10.77.1.1:2380`, client address `10.77.1.1:2379`, in the cluster with token `putgetd`.

- `witnessMember`, `witnessToken`: that member and token.
- `witnessMember_id`: its id is the one Go computes, `memberId "http://10.77.1.1:2380" "putgetd" =
  pgId`, evaluated by the kernel.
- `bootFacts_witness`: `BootFacts` of any deployment whose members are `[witnessMember]` and whose token
  is `witnessToken`, at the peers `[pgId]`, the contexts `[pgCtx]` and the log `pgBoot` (`pgBootCore`).
- `serverStart_witness`: `ServerStart` of the member at `witnessMemberσ`, a fresh machine whose files are
  its two empty roots (data directory, WAL area).
- `clientStart_witness`: `ClientStart` at `witnessClientσ`, a fresh machine with the empty root `/tmp`.

Not here, because no Lean proof can establish them: `EtcdEnv`'s fields (`authRecordsFit`,
`apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`, `leasePeersOk`), `EtcdVerifyOff` and
`GodebugFips140Off`, all stated over opaque values. A witness leaves them out (class `opaque` of
`etc/premise-witness-baseline.txt`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelWitness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver Robustness Fs

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- The witness member: `putget_safe`'s witness member `putgetd`. -/
def witnessMember : Member :=
  ⟨etcd_putget_dist.name, etcd_putget_dist.peerA, etcd_putget_dist.clientA⟩

/-- The witness cluster's token, `putgetd` (the token `etcd_putget_dist.pgId` is computed in). -/
def witnessToken : GoString := etcd_putget_dist.name

/-- **The witness member's id is SHA-1's**, as `etcd_putget_dist.pgId_eq` (`crypto.sha1.sha1` evaluated by
the kernel, its message schedule's loops as folds). -/
theorem witnessMember_id :
    memberId (go!"http://" ++ witnessMember.peer) witnessToken = etcd_putget_dist.pgId := by
  unfold witnessMember witnessToken memberId membership.memberIdOf crypto.sha1.sha1 crypto.sha1.compress
  rw [show crypto.sha1.schedule = _ from funext crypto.sha1.schedule_eq]
  decide +kernel

/-- **`bootstrap`'s results** at a deployment of the witness member alone. -/
theorem bootFacts_witness (d : Deployment) (hm : d.members = [witnessMember])
    (ht : d.token = witnessToken) :
    BootFacts d [etcd_putget_dist.pgId] [etcd_putget_dist.pgCtx] etcd_putget_dist.pgBoot := by
  have hids : d.ids = [etcd_putget_dist.pgId] := by
    simp only [Deployment.ids, hm, ht, List.map_cons, List.map_nil, witnessMember_id]
  exact ⟨etcd_putget_dist.pgBootCore, by rw [hids]; try exact List.Perm.refl _⟩

/-- The witness member machine's start state: a fresh machine whose files are the member's two roots. -/
def witnessMemberσ [GoLocalContext] : state :=
  freshState ((∅ : IdIssueState), fsRoots etcd_putget_dist.memberRoots, (default : Net.NetLocal), ())

/-- A witness client machine's start state: a fresh machine with the root `/tmp`. -/
def witnessClientσ [GoLocalContext] : state :=
  freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"tmp"), (default : Net.NetLocal), ())

theorem serverStart_witness [GoLocalContext] : ServerStart witnessMember witnessMemberσ :=
  ⟨etcd_putget_dist.memberRoots_init, etcd_putget_dist.memberRoots_walAreas⟩

theorem clientStart_witness [GoLocalContext] : ClientStart witnessClientσ :=
  fsInit_fsOneRoot _ etcd_putget_dist.tmp_rootForm

end etcd_dist
end EtcdGrove
end Perennial

end
