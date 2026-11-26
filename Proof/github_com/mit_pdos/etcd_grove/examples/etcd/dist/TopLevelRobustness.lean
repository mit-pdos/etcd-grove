/- Lean-first (no Rocq counterpart).

# `etcd/dist`: `etcd_safe_nocrash` (`notes/etcd-dist-plan.md` §27, §30)

The full no-crash theorem over every workload kind, from the skeleton (`BootSkel.lean`:
`etcd_safe_nocrash_of_boot`; `BootBad.lean`: the malformed case) and the well-formed deployments' boot
`EtcdBootNC`, split by the token provider (`auth_class`, Q1 of §27.7: auth is on exactly when the one
workload is `auth` or `authLease`):
- auth off (`EtcdBootNCAt (·.cfg.auth = false)`): every class but A and AL, by the general start
  (`Start.lean`) and the machines' boots (`server.member_boot_dist` at `lmOf d`, `AdequacyClient.lean`'s
  `orchBoot`/`nodeBoot` over the full dispatch);
- `[auth]` (F7 S14): `etcdAuthBootNC_holds`, by the auth class's start `etcd_startAuth` and the same machines' boots
  (the orchestrator's arm `MainReadyAuth`, the principal machines' `NodeMainAuth`);
- `[authLease]`: the named hypothesis `EtcdAuthLeaseBootNC` (F7 S4 closes it: its start; `RunAuthLease` is proved
  over `foreignReads.law`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentClass
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.Start
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.StartAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AdequacyClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.AdequacyMember

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **`EtcdBootNC` at the well-formed deployments of a class `P`**: the same start update and boot WPs,
with `P d` one more hypothesis. -/
def EtcdBootNCAt (P : Deployment → Prop) : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : d.WellFormed) (_HP : P d) (σs σc σn : List state)
    (_Hp : BootPremises d σs σc σn)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp etcdDistGF,
          ⌜∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
            Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ machines d σs σc σn, Ps i

/-- **Named hypothesis (F7 S3): the `auth` workload's deployments boot** — `EtcdBootNC` at the deployments whose
one workload is `auth` (kind 5; with auth on, by `auth_class`). -/
abbrev EtcdAuthBootNC : Prop :=
  EtcdBootNCAt (fun d => d.workloads.map (·.kind) = [W64 5])

/-- **Named hypothesis (F7 S4): the `authLease` workload's deployments boot** — `EtcdBootNC` at the deployments
whose one workload is `authLease` (kind 6). -/
abbrev EtcdAuthLeaseBootNC : Prop :=
  EtcdBootNCAt (fun d => d.workloads.map (·.kind) = [W64 6])

/-- **`EtcdBootNC` by the token provider**: auth off from `Hoff`; auth on, the deployment's one workload is
`auth` or `authLease` (`auth_class`), from `Ha` or `Hal`. -/
theorem etcdBootNC_of_split (Hoff : EtcdBootNCAt (fun d => d.cfg.auth = false))
    (Ha : EtcdAuthBootNC) (Hal : EtcdAuthLeaseBootNC) : EtcdBootNC := by
  intro gctx lctx sem errA fmtA srvA clA rpcA cacheA logA fieldA d Hd σs σc σn Hp Hfips G hb
  cases h : d.cfg.auth
  · exact Hoff d Hd h σs σc σn Hp Hfips hb
  · rcases auth_class Hd h with h5 | h6
    · exact Ha d Hd h5 σs σc σn Hp Hfips hb
    · exact Hal d Hd h6 σs σc σn Hp Hfips hb

/-- **The well-formed deployments with auth off or of the `auth` class boot** (every class but AL; §27.2-27.4): the
net extension's registry (`netProto_alloc`), then the full start (`etcd_start` with auth off, `etcd_startAuth` for
`[auth]`, F7 S14: the remote names `ρ` and every machine's share `startShares`), then each machine's boot WP from its
share: a member's by `server.member_boot_dist` at the lease mode `lmOf d` (its premises from `EtcdEnv`'s `noExpiry`,
`lmOf_mono_noExpiry`, and `lmOf_auth_revocable`), an orchestrator's by `orchBoot` and a client machine's by
`nodeBoot` (the dispatch's shares at the Go index, `orchShareF_at`/`nodeShareF_at`; the indices below `2 ^ 63` by
`workloads_length_le`/`nodeList_length_lt`). No hypothesis. -/
theorem etcdBootNCOffAuth_holds :
    EtcdBootNCAt (fun d => d.cfg.auth = false ∨ d.workloads.map (·.kind) = [W64 5]) := by
  intro gctx lctx sem errA fmtA srvA clA rpcA cacheA logA fieldA d Hd HP σs σc σn Hp Hfips G hb
  obtain ⟨boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ := Hp
  have hrb : receiptBound etcdDistGF ≤ 2 ^ 60 := by unfold etcdSteps at hb; omega
  have hsl : (servers d σs).length = d.members.length := by simp [servers, Hσs.1]
  have hcl : (clients d σc).length = d.workloads.length := by simp [clients, Hσc.1]
  have hnl : (nodeMachines d σn).length = d.nodeList.length := by simp [nodeMachines, Hσn.1]
  have hW := workloads_length_le Hd
  have hN := nodeList_length_lt Hd
  have hV := etcd_putget_dist.wenv_nonempty (GF := etcdDistGF) mvcc.api.mvccApi_names_nonempty_law_holds
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  imod (Or.elim HP
      (fun ha => etcd_start (GF := etcdDistGF) d Hd ha boot Hbf hrb hV EtcdGrove.rpctypesEtcdError_asTarget)
      (fun h5 => etcd_startAuth (GF := etcdDistGF) d Hd h5 boot Hbf hrb)) $$ Hreg Hs
    with ⟨%ρ, HM, HO, HN⟩
  imodintro
  iexists startShares (GF := etcdDistGF) (ρ := ρ) d boot
  isplitr
  · ipureintro
    intro i m hm
    unfold machines at hm
    rcases Nat.lt_or_ge i d.members.length with hi | hi
    · rw [List.getElem?_append_left (by simp [List.length_append]; omega),
        List.getElem?_append_left (by omega)] at hm
      unfold servers at hm
      rw [List.getElem?_mapIdx] at hm
      obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
      rw [startShares_member hi]
      obtain ⟨hiσ, rfl⟩ := List.getElem?_eq_some_iff.1 hσ
      have Hst := Hσs.2 (d.members[i], σs[i]) (List.mem_iff_getElem.mpr
        ⟨i, by simp [List.length_zip]; omega, by simp [List.getElem_zip]⟩)
      exact server.member_boot_dist d Hd boot Hbf Henv HEnv Hfips (lmOf d) (lmOf_mono_noExpiry Henv.noExpiry)
        (lmOf_auth_revocable Hd) i d.members[i] (List.getElem?_eq_getElem hi) σs[i] Hst
    · rcases Nat.lt_or_ge i (d.members.length + d.workloads.length) with hi2 | hi2
      · obtain ⟨j, rfl⟩ : ∃ j, i = d.members.length + j := ⟨i - d.members.length, by omega⟩
        rw [List.getElem?_append_left (by simp [List.length_append]; omega),
          List.getElem?_append_right (by omega), hsl, Nat.add_sub_cancel_left] at hm
        unfold clients at hm
        rw [List.getElem?_mapIdx] at hm
        obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
        rw [startShares_orch (by omega), ← orchShareF_at d j (by omega)]
        exact orchBoot d Hfips j σ ρ
      · obtain ⟨n, rfl⟩ : ∃ n, i = d.members.length + d.workloads.length + n :=
          ⟨i - (d.members.length + d.workloads.length), by omega⟩
        rw [List.getElem?_append_right (by simp [List.length_append]; omega), List.length_append, hsl, hcl,
          Nat.add_sub_cancel_left] at hm
        unfold nodeMachines at hm
        rw [List.getElem?_mapIdx] at hm
        obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
        have hn : n < d.nodeList.length := by
          have := (List.getElem?_eq_some_iff.1 hσ).1
          omega
        rw [startShares_node, ← nodeShareF_at d n (by omega)]
        exact nodeBoot d Hfips n σ ρ
  · unfold machines
    iapply BigSepL.bigSepL_append.2
    isplitl [HM HO]
    · iapply BigSepL.bigSepL_append.2
      isplitl [HM]
      · iapply (cls_bigSepL_idx (startShares (GF := etcdDistGF) (ρ := ρ) d boot) d.members (servers d σs)
          hsl.symm) $$ HM
      · rw [hsl]
        iapply (cls_bigSepL_idx (fun j => startShares (GF := etcdDistGF) (ρ := ρ) d boot (j + d.members.length))
          d.workloads (clients d σc) hcl.symm)
        iapply (BigSepL.bigSepL_mono
          (Φ := fun j _ => startShares (GF := etcdDistGF) (ρ := ρ) d boot (d.members.length + j))
          (fun {j x} _ => by rw [Nat.add_comm])) $$ HO
    · rw [List.length_append, hsl, hcl]
      iapply (cls_bigSepL_idx
        (fun n => startShares (GF := etcdDistGF) (ρ := ρ) d boot (n + (d.members.length + d.workloads.length)))
        d.nodeList (nodeMachines d σn) hnl.symm)
      iapply (BigSepL.bigSepL_mono
        (Φ := fun n _ => startShares (GF := etcdDistGF) (ρ := ρ) d boot (d.members.length + d.workloads.length + n))
        (fun {n x} _ => by rw [Nat.add_comm])) $$ HN

/-- **The well-formed auth-off deployments boot** (every class but A and AL): `etcdBootNCOffAuth_holds`'s left
case. -/
theorem etcdBootNCOff_holds : EtcdBootNCAt (fun d => d.cfg.auth = false) := by
  intro gctx lctx sem errA fmtA srvA clA rpcA cacheA logA fieldA d Hd ha σs σc σn Hp Hfips G hb
  exact etcdBootNCOffAuth_holds d Hd (Or.inl ha) σs σc σn Hp Hfips hb

/-- **`EtcdAuthBootNC` holds** (F7 S14): the `auth` class's deployments boot, `etcdBootNCOffAuth_holds`'s right
case (the start `etcd_startAuth`; the orchestrator's arm `MainReadyAuth`, the principal machines' `NodeMainAuth`). -/
theorem etcdAuthBootNC_holds : EtcdAuthBootNC := by
  intro gctx lctx sem errA fmtA srvA clA rpcA cacheA logA fieldA d Hd h5 σs σc σn Hp Hfips G hb
  exact etcdBootNCOffAuth_holds d Hd (Or.inr h5) σs σc σn Hp Hfips hb

/-- **`etcd_safe_nocrash` from the auth-off boot and the two auth classes' boots** (`etcdBootNC_of_split`, the
skeleton's bridge and malformed case). -/
theorem etcd_safe_nocrash_of_split (Hoff : EtcdBootNCAt (fun d => d.cfg.auth = false))
    (Ha : EtcdAuthBootNC) (Hal : EtcdAuthLeaseBootNC) : etcd_robust_nocrash.spec :=
  etcd_safe_nocrash_of_bootWF (etcdBootNC_of_split Hoff Ha Hal)

/-- **`etcd_safe_nocrash`** (`notes/etcd-dist-plan.md` §27, §30): every workload kind of the single-process
`etcd_robust_single_process` (but its restarts, `etcd_safe`'s), plus `leaseExpiry` and partitions, on any
deployment, from the boot of every class but AL (`etcdBootNCOff_holds`, `etcdAuthBootNC_holds`: proved) and one
**named hypothesis**, the boot of the `authLease` class:
* `HauthLease : EtcdAuthLeaseBootNC` — deployments whose one workload is `authLease` (F7 S4 closes it: the auth-on
  start at the revocable lease mode, and `RunAuthLease`, proved over `foreignReads.law`).
When it is a theorem the hypothesis goes, and `etcd_kv_safe_nocrash` becomes `etcd_kv_safe_nocrash_of_full
etcd_safe_nocrash` (§27.4 Q4). -/
theorem etcd_safe_nocrash (HauthLease : EtcdAuthLeaseBootNC) :
    etcd_robust_nocrash.spec :=
  etcd_safe_nocrash_of_split etcdBootNCOff_holds etcdAuthBootNC_holds HauthLease

#print axioms etcd_safe_nocrash

end etcd_dist
end EtcdGrove
end Perennial

end
