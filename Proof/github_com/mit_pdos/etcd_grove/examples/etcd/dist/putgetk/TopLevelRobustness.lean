/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the proof skeleton of `putgetK_safe` (n members; `notes/putget-dist-plan.md` §13)

Not closed: `putgetK_safe_of_boot` proves `putgetK_safe.spec` from one named hypothesis, `PutgetKBoot`, by
the all-stable bridge over `etcdNetExts` (`Net.robust_of_distBootIL`, as `putget_safe_of_boot`), with each
machine's `FsInit` from the statement (`etcdNetExts_initP`). No axiom and no `sorry`.

`PutgetKBoot`: at the statement's premises (and the addresses distinct and valid, from `DistDeploy`), the start update
from the configuration's addresses unset to a share per machine, each machine's boot program safe from its
share and its whole start (`DistBootWpSL srvLevelK`, as `PutgetBoot`). What discharges it, in later steps:
the start `etcd_dist.etcdClusterStart` (`dist/ClusterStart.lean`, proved over `clusterAllocN`, the interim
`etcdAddr_set` and `S5Draft.http_addr_set`), member `i`'s boot from its `memberStartShare`
(`memberBoot_of_slice`, then `StartMember`, `Serve_dist`, `holdForever`; its peer half waits for S5), and
the client's boot (putget's `client_boot`, through `putgetk.Client`). The start splits on the program's
check (`idsOk (idsOf peers)` and the lists' shape, decidable): when it fails, every member's `Valid`
fails too and the member returns at once (its share empty), and the client's `Put` finds no listener.
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

/-- **The machines' boot WPs** (see the file header): at `putgetK_safe.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe. -/
def PutgetKBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (peers clients : List GoString)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (_Hbl : BootLogFacts (idsOf peers) ps ctxs boot)
    (_Haf : authRecordsFit) (_Hbuq : apply.backendUnderQuota) (_Hrf : grpcRepliesFit)
    (_Hdbo : storage.diskOk)
    (_Hbgo : BootGoK peers clients ps ctxs)
    (σs : Nat → state) (σc : state)
    (_Hm : ∀ i < peers.length, MemberFiles i (σs i)) (_Hc : ClientFiles σc)
    (_Hfips : crypto.fips140.GodebugFips140Off)
    (_Hnd : (addrs peers clients).Nodup) (_Hok : ∀ a ∈ addrs peers clients, Net.addrOk a = true)
    (_HEnv : EtcdVerifyOff),
    ∀ [GooseGlobalGS .hasLC putgetGF], srvLevelK ≤ receiptBound putgetGF →
      receiptBound putgetGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ addrs peers clients, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system peers clients σs σc)[i]? = some m →
            Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system peers clients σs σc, Ps i

/-- Every machine of the system starts with its files as on disk (`MemberFiles`, `ClientFiles`). -/
theorem system_fsInit [GoGlobalContext] [GoSemanticsFunctions] {peers clients : List GoString}
    {σs : Nat → state} {σc : state}
    (Hm : ∀ i < peers.length, MemberFiles i (σs i)) (Hc : ClientFiles σc)
    (m : Expr × state) (hm : m ∈ system peers clients σs σc) :
    Fs.FsInit (extLocal Fs.fsExt m.2.world) := by
  simp only [system, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    rw [List.getElem_mapIdx] at he
    rw [← he]
    exact (Hm i (by simpa using hi)).1
  · exact Hc

/-- **`putgetK_safe` from the machines' boot WPs** (see the file header), by the all-stable bridge over
`etcdNetExts` (`Net.robust_of_distBootIL`), with each machine's `FsInit` from the statement. -/
theorem putgetK_safe_of_boot (HS : PutgetKBoot) : putgetK_safe.spec := by
  intro _ _ _ _ _ _ _ _ peers clients ps ctxs boot Hbl Haf Hbuq Hrf Hdbo Hbgo σs σc g Hm Hc
    Hd HEnv Hfips
  refine Net.robust_of_distBootIL (GF := putgetGF) (addrs peers clients) (system peers clients σs σc) g
    (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) ?_
    (fun hlo hb => HS peers clients ps ctxs boot Hbl Haf Hbuq Hrf Hdbo Hbgo σs σc Hm Hc Hfips
      Hd.1 Hd.2.1 HEnv hlo hb) Hd
  exact etcdNetExts_initP g _ (system_fsInit Hm Hc)

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
