/- Lean-first (no Rocq counterpart).

# `etcd/dist`: `etcd_safe_nocrash` (`notes/etcd-dist-plan.md` §27, §30)

The full no-crash theorem over every workload kind, from the skeleton (`BootSkel.lean`:
`etcd_safe_nocrash_of_boot`; `BootBad.lean`: the malformed case) and the well-formed deployments' boot
`EtcdBootNC`, split by the token provider (`auth_class`, Q1 of §27.7: auth is on exactly when the one
workload is `auth` or `authLease`):
- auth off (`EtcdBootNCAt (·.cfg.auth = false)`): every class but A and AL, by the general start
  (`Start.lean`) and the machines' boots (`server.member_boot_dist` at `lmOf d`, `AdequacyClient.lean`'s
  `orchBoot`/`nodeBoot` over the full dispatch);
- `[auth]` and `[authLease]`: the named hypotheses `EtcdAuthBootNC` and `EtcdAuthLeaseBootNC` (F7 S3/S4 close
  them: their starts, `RunAuth`, the principal arm; `RunAuthLease` is proved over `foreignReads.law`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentClass

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

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

/-- **`etcd_safe_nocrash` from the auth-off boot and the two auth classes' boots** (`etcdBootNC_of_split`, the
skeleton's bridge and malformed case). -/
theorem etcd_safe_nocrash_of_split (Hoff : EtcdBootNCAt (fun d => d.cfg.auth = false))
    (Ha : EtcdAuthBootNC) (Hal : EtcdAuthLeaseBootNC) : etcd_robust_nocrash.spec :=
  etcd_safe_nocrash_of_bootWF (etcdBootNC_of_split Hoff Ha Hal)

end etcd_dist
end EtcdGrove
end Perennial

end
