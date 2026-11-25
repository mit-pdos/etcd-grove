/- Lean-first (no Rocq counterpart).

# `dist/kvremote`: the members' boot law of the kv start, proved (`notes/etcd-dist-plan.md` §21.1, step 2)

`kvremote/Start.lean`'s `kv_start_deployment` takes the members' part of the start as a law,
`member_boot_dist.law d MS`, for any members' shares `MS`. Here it is proved at N5's shares:
- `membersShareKv d boot Γ`: some cluster names `c` whose view is `Γ`, with every member's `memberShareD c …`
  (what `member_boot_dist` takes, `server/AdequacyMember.lean`, one member at a time);
- `kvSys_boot`: the cluster's `etcdKV` at the boot state is the kv store's state at the model's start
  (`(kvR γk).sysState (kvR γk).B.init`): the boot log changes no KV state (`linkv.kvRaftOf_boot`), so the state
  has no key, at revision `1` (`GoodKV`, `absSt` the model's start, `kvGood`);
- `member_boot_dist_law`: the law, from `server/ClusterStartD.lean`'s `clusterStartD` (the cluster's allocation,
  the peer addresses at the cluster's raft names, the client addresses at its view) and `kvSys_boot`.

No axiom, no `sorry`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Start
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.ClusterStartD
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProofMode Net
open EtcdGrove EtcdGrove.etcd_txnlin EtcdGrove.etcd_dist
open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- The start's members of `kvremote/Start.lean` are N5's (`cmsD`). -/
theorem clusterMembersOf_eq [GooseExts] (d : Deployment) : clusterMembersOf d = cmsD d := by
  rw [cmsD_eq]
  rfl

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [server_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The members' shares at the view `Γ`** (`member_boot_dist.law`'s `MS`): some cluster names whose view is
`Γ`, with every member's share `memberShareD` at `bootstrap`'s peers and contexts and the bootstrap log `boot`. -/
def membersShareKv (d : Deployment) (boot : List LogEntry) (Γ : DistView) : IProp GF :=
  iprop(∃ c : ClusterNames, ⌜c.view = Γ⌝ ∗
    [∗list] i ↦ _m ∈ d.members,
      memberShareD (GF := GF) (G := Gg) c d (distPs d) (distCtxs d) boot i)

/-- **The cluster's KV at the boot state is the kv store's state at the model's start** (see the file header). -/
theorem kvSys_boot (γk : KVNames) (hlog : γk.log0 = [[], []]) (ps : List w64) (bl : List EntryM)
    (hb : srvBootLogOk ps bl) :
    etcdKV (Gg := Gg) γk (kvModelSt γk (bootEntries bl)) ⊢
      (kvR (GF := GF) γk).sysState (kvR (GF := GF) γk).B.init := by
  have h : kvModel γk (bootEntries bl) = [[], []] := by
    unfold kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) ps bl hb, hlog]
  show _ ⊢ kvSys γk TSo.init
  unfold kvSys
  iintro H
  iexists kvModelSt γk (bootEntries bl)
  isplitl [H]
  · iexact H
  · ipureintro
    unfold kvModelSt
    refine ⟨goodKV_empty _ (by rw [h, kvStateOf_kvs]; rfl),
      linkv.absSt_init _ (by rw [h, kvStateOf_kvs]; rfl) (by rw [h, kvStateOf_rev]; rfl), ?_⟩
    unfold kvGood
    refine ⟨?_, ?_⟩
    · first | decide | (show (1 : Nat) < 2 ^ 63; omega) | simp [TSo, linkv.txnSpec, linkv.mInit]
    · intro k r hr
      first | cases hr | simp [TSo, linkv.txnSpec, linkv.mInit] at hr

/-- **`member_boot_dist.law`, proved at N5's shares** (see the file header): for a well-formed deployment at the
bootstrap log `boot` (`BootFacts`) and a receipt budget of at most `2 ^ 60`. -/
theorem member_boot_dist_law (d : Deployment) (Hd : d.WellFormed) (boot : List LogEntry)
    (Hbf : BootFacts d boot) (Hrb : receiptBound GF ≤ 2 ^ 60) :
    member_boot_dist.law (Gg := Gg) d (membersShareKv d boot) := by
  have Hbc : BootCore (distPs d) (distCtxs d) boot := Hbf
  unfold member_boot_dist.law
  iintro #Hreg Hs
  imod (clusterStartD (G := Gg) d Hd boot Hbf Hrb) $$ Hreg Hs with ⟨%c, %Hlog, Hkv, #Hcs, Hms⟩
  imodintro
  iexists c.view
  isplitr
  · ipureintro
    rfl
  isplitl [Hkv]
  · iapply (kvSys_boot c.γk Hlog (distPs d) _ (srvBootLogOk_of_BootLog _ _ _ Hbc.boot)) $$ Hkv
  isplitr
  · rw [clusterMembersOf_eq]
    iexact Hcs
  · iunfold membersShareKv
    iexists c
    isplitr
    · ipureintro
      rfl
    · iexact Hms

end start

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
