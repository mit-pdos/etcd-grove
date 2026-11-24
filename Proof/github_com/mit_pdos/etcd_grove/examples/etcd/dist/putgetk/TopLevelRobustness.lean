/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the proof skeleton of `putgetK_safe` at `k = 3` (`notes/putget-dist-plan.md` §13)

Not closed: `putgetK_safe_of_boot` proves `putgetK_safe.spec` from one named hypothesis, `PutgetKBoot`, by
the all-stable bridge over `etcdNetExts` (`Net.robust_of_distBootIL`, as `putget_safe_of_boot`), with each
machine's `FsInit` from the statement (`etcdNetExts_initP`). No axiom and no `sorry`.

`PutgetKBoot`: at the statement's premises (and the addresses valid, from `DistDeploy`), the start update
from the deployment's six addresses unset to a share per machine, each machine's boot program safe from its
share and its whole start (`DistBootWpSL srvLevelK`, as `PutgetBoot`). What discharges it, in later steps:
the start `etcd_dist.etcdClusterStart` (`dist/ClusterStart.lean`, proved over `clusterAllocN`, the interim
`etcdAddr_set` and `S5Draft.http_addr_set`), member `i`'s boot from its `memberStartShare`
(`memberBoot_of_slice`, then `StartMember`, `Serve_dist`, `holdForever`; its peer half waits for S5), and
the client's boot (putget's `client_boot`, through `putgetk.Client`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.TopLevelRobustness
public import Net.Statement.DistBridgeExts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeLevels

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net etcd_putget_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **The four machines' boot WPs** (see the file header): at `putgetK_safe.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe. -/
def PutgetKBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (_Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (_Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (_Hids : ids.length = 3)
    (_Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (_Haf : authRecordsFit) (_Hbuq : apply.backendUnderQuota) (_Hrf : grpcRepliesFit)
    (_Hdbo : storage.diskOk)
    (_Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) n ids ps ctxs boot)
    (σs : List state) (σc : state) (_Hσs : σs.length = 3)
    (_Hm : ∀ (i : Nat) (σ : state), σs[i]? = some σ → MemberFiles i σ) (_Hc : ClientFiles σc)
    (_Hok : ∀ a ∈ addrs, Net.addrOk a = true)
    (_HEnv : ∀ m ∈ system σs σc, verifyEnvOff m.1)
    (_HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    ∀ [GooseGlobalGS .hasLC putgetGF], srvLevelK ≤ receiptBound putgetGF →
      receiptBound putgetGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system σs σc)[i]? = some m →
            Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system σs σc, Ps i

/-- Every machine of the system starts with its files as on disk (`MemberFiles`, `ClientFiles`). -/
theorem system_fsInit [GoGlobalContext] {σs : List state} {σc : state}
    (Hm : ∀ (i : Nat) (σ : state), σs[i]? = some σ → MemberFiles i σ) (Hc : ClientFiles σc)
    (m : Expr × state) (hm : m ∈ system σs σc) : Fs.FsInit (extLocal Fs.fsExt m.2.world) := by
  simp only [system, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    rw [List.getElem_mapIdx] at he
    rw [← he]
    exact (Hm i _ (List.getElem?_eq_getElem (by simpa using hi))).1
  · exact Hc

/-- **`putgetK_safe` from the four machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootIL`), with each machine's `FsInit` from the statement. -/
theorem putgetK_safe_of_boot (HS : PutgetKBoot) : putgetK_safe.spec := by
  intro _ _ _ _ _ _ _ _ Hctx Hcec ids ps ctxs boot Hids Hbf Haf Hbuq Hrf Hdbo Hprem σs σc g Hσs Hm Hc
    Hd HEnv HEnvTok
  refine Net.robust_of_distBootIL (GF := putgetGF) addrs (system σs σc) g
    (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) ?_
    (fun hlo hb => HS Hctx Hcec ids ps ctxs boot Hids Hbf Haf Hbuq Hrf Hdbo Hprem σs σc Hσs Hm Hc
      Hd.2.1 HEnv HEnvTok hlo hb) Hd
  exact etcdNetExts_initP g _ (system_fsInit Hm Hc)

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
