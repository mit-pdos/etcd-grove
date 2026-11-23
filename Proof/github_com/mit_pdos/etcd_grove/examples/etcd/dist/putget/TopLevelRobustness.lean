/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the proof skeleton of `putget_safe` (`notes/putget-dist-plan.md`, section 5)

Not closed yet: `putget_safe_of_boot` proves `putget_safe.spec` from two named hypotheses, and
`putget_safe` (the plain name, `theorem putget_safe : putget_safe.spec`) is declared once both are
discharged. No axiom and no `sorry`.

- `PutgetBridge`: the bridge from one WP per machine to `Robust []` for the extensions `etcdNetExts` at the
  ghost-state bundle `putgetGF` (`Net.robust_of_distBootRB`'s statement, which is proved for `netExts` only).
  **Provable now**: `robust_of_distBootRB`'s proof with `putgetGF`'s `GooseGpreS` instance, the three
  extensions' init predicates and the net extension's part of the global start resources (the plan's
  section 3). No axiom needed.
- `PutgetBoot`: at the statement's premises, the start update from the two addresses unset (the net library's
  start) to a share per machine, each machine's boot program safe from its share (`BootWp`). This is the
  two machines' proofs:
  * the member's (`putget.Member`): the in-process `putget`'s `Main.wp_proof` up to `Serve`, given its start
    resources (`dataDirFresh`, `addrClaim` of its client address, the metric names' registration rights,
    `envVerifyOff` through `env.ClearProxy`'s spec, a thread token), which only the single-process start
    axiom hands out today (the plan's section 3: a question for the distributed start, S4);
  * the client's (`putget.Client`): the in-process `Main.wp_proof`'s second half, given the member's KV
    registrations at the client machine's own ghost-state instance; across machines this needs phase 7 S2's
    heap-independent registration (the plan's section 4: **blocked on S2**; the in-process `isGrpcRpcMd` holds
    a WP of the member's handler at the holder's heap and cannot cross machines).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelRobustness
public import Net.Statement.DistBridge

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

/-- **A machine's boot program `e` is safe from `P`** (`Net.DistBootWpG` for `etcdNetExts`, which is
stated for `netExts`): under every ghost state over the global one `G` whose Go context is `lctx`, from
no package initialized, it returns `#()` and is not stuck. -/
def BootWp [GoGlobalContext] [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC putgetGF] (e : Expr)
    (P : IProp putgetGF) : Prop :=
  ∀ hG : HeapGS .hasLC putgetGF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- **The bridge for `etcdNetExts` at `putgetGF`** (`Net.robust_of_distBootRB`'s statement for this bundle):
under a deployment's start, an update from the extension's start resources (every address unset) to a share
`Ps i` for each machine `i`, each machine's boot program safe from its share, gives `Robust` with no crashing
machine. Provable (see the file header); a hypothesis of `putget_safe_of_boot` until it is proved. -/
def PutgetBridge : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] (as₀ : List GoString) (nodes : List (Expr × state))
    (g : GlobalState) (threads bound : Nat),
    (∀ [GooseGlobalGS .hasLC putgetGF], receiptBound putgetGF ≤ bound →
      ⊢ ([∗list] a ∈ as₀, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → BootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) →
    Net.DistDeploy as₀ nodes g → Robust [] nodes g threads bound

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
    (σm σc : state) (_Hm : MemberFiles σm),
    ∀ [GooseGlobalGS .hasLC putgetGF], receiptBound putgetGF ≤ 2 ^ 40 - 11 →
      ⊢ ([∗list] a ∈ addrs peer client, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system peer client σm σc)[i]? = some m →
            BootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system peer client σm σc, Ps i

/-- **`putget_safe` from the bridge and the two machines' boot WPs** (see the file header). -/
theorem putget_safe_of_boot (HB : PutgetBridge) (HS : PutgetBoot) : putget_safe.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem HNs σm σc g
    Hm Hd
  exact HB (addrs peer client) (system peer client σm σc) g (2 ^ 28) (2 ^ 40 - 11)
    (fun hb => HS Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem HNs σm σc Hm hb) Hd

end etcd_putget_dist
end EtcdGrove
end Perennial

end
