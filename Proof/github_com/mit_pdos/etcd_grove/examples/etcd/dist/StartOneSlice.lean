/-
**The one member of a new cluster started from its slice of the deployment's start** (O1 option B,
`notes/etcd-dist-plan.md` §18.3). Lean-first (no Rocq counterpart).

`wp_StartServer1_slice`: `etcdstart.wp_StartServer1` (`StartServer.spec` at the one-member cluster of member
`id`, from its named premises, its start bundle, the logger, the main thread's token) with the ghost state
`NewServer` takes from the deployment's start (`etcdClusterStart`'s pieces for one member: the cluster's
facts `clusterFactsOf c` and the member's slice, `clusterAllocN`'s, `ClusterOk`) in place of the member's own
allocation (`alloc1`): its `memberBoot` from the slice (`memberBoot_of_slice`, with `proto.Marshal`'s
contract), the raft network of the one-member directory of `http://peer`. The result: an error with the
token, or the member started (`memberUp`) at request names whose KV names are `kvCongr` to the cluster's,
`c.γk`, what `Serve_dist` takes at the cluster's view. putget's `Member` starts its member this way, so that
the start fixes the view before the member runs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartOne

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 1600000 in
/-- See the file header. -/
theorem wp_StartServer1_slice (wp_StartServer : StartServer.spec (GF := GF) (hG := hG))
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat) (name peer client : GoString) (lg : Loc) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hbf : BootFacts id ctxs boot)
    (hpl : types.plainPeerURL (go!"http://" ++ peer)) (hu : utf8Valid name) (hn : name.length ≤ 200)
    (hpf : addrFits peer) (hcf : addrFits client)
    (Htb : threadBound GF ≤ 2 ^ 28) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (HrbN : receiptBound GF ≤ N + 1) (HwbN : N + 7 + bootWB ≤ backend.wbInit)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk)
    (c : ClusterNames) (Hcok : ClusterOk c [id] boot .none false 0 [id]) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        zapLoggerOk lg ∗ threadTok ∗ premises (GF := GF) name peer client N id ctxs boot ∗
        context.isClosedchanInit ∗ memberStartRes (GF := GF) name {} ∗
        clusterFactsOf (G := hG.goose_globalGS) c ∗
        memberSliceOf (G := hG.goose_globalGS) c [id] [id] ctxs (LogEntry.toEntries boot 0) id }}
      (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer))
        (Val #name)) (Val #peer)) (Val #client)) (Val #lg))
    {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
        (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF),
          memberUp s ρ E₀ lg γn id ∗ ⌜kvCongr ρ.rd.kv c.γk⌝) }} := by
  iintro %Φ ⟨#Hpkg, #Hlgz, Htok, #Hprem, #Hcci, Hstart, #Hcf, Hsl⟩ HΦ
  obtain ⟨hvs, hrule, hboot, hc0, hch, hlog, hiss, hwn, hfs, hgen, hkc, -, hklg, hpo, hns, -⟩ := Hcok
  iunfold premises at Hprem
  icases Hprem with #Hboot
  -- `proto.Marshal`'s bytes at the bootstrap log's conf changes (as `wp_StartServer1`)
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  ihave #Hb := bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (dir1 peer id) name name
      (urls1 name peer client) id (cfgOk name name) (urls1 name peer client)
      (fun _ h => h) (fun _ h => h) $$ Hboot
  -- the member's `memberBoot`, from its slice
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  have Hx : xsOf [id] c.idx (idPfxOf (W16 (uint.Z id))) = (c.idx id).slog :=
    xsOf_at [id] c.idx (by simp [idPfxsOf]) id (List.mem_singleton_self id)
  imod (memberBoot_of_slice c.γ [id] ctxs (LogEntry.toEntries boot 0) (c.reg id)
      c.issued c.cnt c.wn c.fs c.gen c.γk (fun _ => srvFloorFacts (GF := GF) (c.idx id).slog)
      id γm (c.idx id) (c.cok id) (c.rev id) (xsOf [id] c.idx (idPfxOf (W16 (uint.Z id))))
      Hx hiss hwn hfs hgen hc0 hch hlog hvs false hkc .none lease.runCfg_none hklg (fun h => nomatch h)
      hpo rfl hns) $$ Hmarsh Hcf Hsl with ⟨%ρ, %Hρ, Hmb⟩
  -- the raft network of the one-member directory (as `alloc1`)
  imod (netNames_alloc (srvNet { c.γ with reg := c.reg id }) (dir1 peer id) (∅ : GMap w64 Unit) ⊤)
    with ⟨%γn, %Hγn, -, #HregN⟩
  ihave #Hnet := netHttpOk_single γn id
    (fun f hf => dirOne_member id _ f (by rw [Hγn.2] at hf; exact hf)) $$ HregN
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  have Hdirok : netDirOk (dir1 peer id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) hpl
  ihave Hfresh := memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N name peer client lg (LogEntry.toEntries boot 0) ctxs (dir1 peer id) id
      { c.γ with reg := c.reg id } ρ (env₀ γm (c.idx id) (c.rev id) (srvApi.kvNx ρ.rd false) false)
      (fun _ => srvFloorFacts (GF := GF) (c.idx id).slog) γn .none Htb Hrb48 HrbN HwbN hvs hrule hboot
      hblen Hγn.1 Hγn.2 Hdirok (by simp [dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) hu hn hpf hcf Haf
      Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %srv %err Hr
  · iframe; iframe #
  iapply HΦ
  icases Hr with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup, -⟩)
  · ileft; iframe Htok; ipureintro; exact Herr
  · iright
    isplitr
    · ipureintro; exact Herr
    iexists ρ, _, γn
    iframe Hup
    ipureintro; exact Hρ.2.2.2.2.2

end proof

end etcd_dist
end EtcdGrove
end Perennial
