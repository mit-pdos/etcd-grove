/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the proof skeleton of `putget_safe` (`notes/putget-dist-plan.md`, section 5)

Not closed yet: `putget_safe_of_boot` proves `putget_safe.spec` from one named hypothesis, `PutgetBoot`, and
`putget_safe` (the plain name, `theorem putget_safe : putget_safe.spec`) is declared once it is discharged.
No axiom and no `sorry`. The bridge from one WP per machine to `Robust []` is proved
(`Net.robust_of_distBootI`, `Net/Statement/DistBridgeExts.lean`, over any list of extensions with the net
extension), with the interpretations' initial-state conditions from the statement's `FsInit` premises
(`etcdNetExts_initP`).

`PutgetBoot`: at the statement's premises, the start update from the two addresses unset (the net library's
start) to a share per machine, each machine's boot program safe from its share and its whole start
(`DistBootWpS`: its files' and listeners' start resources, its main thread's token, the logic's bounds). Its
split (the plan's section 7):
* the start: the client address's service right and the one-shot name `γE` of the member's apply
  environment (upamanyus's S2 names, #24; not defined here until his signatures are posted);
* the member's boot (`putget.Member`): the in-process `Main.wp_proof` up to `Serve`, given its start
  resources: `threadTok` and the address's listen token from the bridge, its files from `MemberFiles`;
  `addrClaim` (until S2), `dataDirFresh` (until the WAL link), the metric names' rights (until
  `prom-registry`) and `env.ClearProxy`'s spec (until an `os.Unsetenv` model) as hypotheses;
* the client's boot (`putget.Client`): the in-process `Main.wp_proof`'s second half over S2's `Invoke`
  (**blocked on S2**: today's `isGrpcRpcMd` holds a WP of the member's handler at the holder's heap and cannot
  cross machines; S2 redefines it as `grpcSvcAt` with `envAt γE E`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelRobustness
public import Net.Statement.DistBridgeExts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProgramLogic Robustness go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **The two machines' boot WPs** (see the file header): at `putget_safe.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe.
The member's and the client's proofs; the client's is blocked on phase 7 S2. -/
def PutgetBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (_Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (_Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (peer client : GoString)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (_Hbf : etcdstart.BootFacts id ctxs boot)
    (_Haf : authRecordsFit) (_Hbuq : apply.backendUnderQuota) (_Hrf : grpcRepliesFit)
    (_Hdbo : storage.diskOk)
    (_Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    (_HNs : prometheus.namesUnclaimed (bootMember peer client)
        github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.initNames ∧
      prometheus.namesUnclaimed (bootClient client)
        github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.initNames)
    (σm σc : state) (_Hm : MemberFiles σm) (_Hc : ClientFiles σc),
    ∀ [GooseGlobalGS .hasLC putgetGF], receiptBound putgetGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ addrs peer client, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system peer client σm σc)[i]? = some m →
            Net.DistBootWpS (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system peer client σm σc, Ps i

/-- **`putget_safe` from the two machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootI`), with each machine's `FsInit` from the statement. -/
theorem putget_safe_of_boot (HS : PutgetBoot) : putget_safe.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem HNs σm σc g
    Hm Hc Hd
  refine Net.robust_of_distBootI (GF := putgetGF) (addrs peer client) (system peer client σm σc) g
    (2 ^ 28) (2 ^ 28 - 1) ?_
    (fun hb => HS Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem HNs σm σc Hm Hc hb) Hd
  refine etcdNetExts_initP g _ ?_
  intro m hm
  simp only [system, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Hm.1
  · exact Hc

end etcd_putget_dist
end EtcdGrove
end Perennial

end
