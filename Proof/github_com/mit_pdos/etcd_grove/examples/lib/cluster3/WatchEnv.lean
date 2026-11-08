/-
**The clients' watch environment at the cluster** (W4c of `notes/watch-cut-plan.md`,
2026-10-22; until 2026-11-05 the partition example's, at its configuration). Lean-first, no Rocq
counterpart.

`watchEnv cfg R₁ R₂ R₃ γr pfx` (`Defs.lean`): the three members at their bridges, the watch contract
at the cluster's history, the KV state variable `γr`'s. A member's watch facts (`memberWatch`: its
read view, its watch server, its names the history's and its KV state variable the cluster's, its
store's fact for watches (`mvcc.watchNoDup`);
until 2026-10-26 also no key written twice in a revision of its logs, from watchkv's server
workload, which D47's watch spec no longer needs) give its `watchMemberFacts` (`memberWatch_facts`:
the laws by `watchLaws_hist`, the KV facts `srvKVFacts` from the read view and the store's start
log, `cert0_of_server`), and the three with their
`Watch` streams at the bridges give the watcher's facts at every connection to the bridges
(`watchEnv_conn`, by `watchConnFacts_of_members`, for a configuration meeting `cfgOk`: its bridges
distinct), what `isNewClient_watcher_of` takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.go_etcd_io.etcd.client.v3.WatchLawsHist
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section watch
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member's watch facts** (persistent): its read view at its apply environment, its watch
server there, its names the history's (`memberOf`), its KV state variable the cluster's; and
(R9, the `lean` merge) the laws of the server's watch facts (`srvWOf`, from `srvWOk`) and its watch
condition (`srvOnce`: the store does not compact, `client.srvOnce_noCmp`, or no revision writes a
key twice, a compacting cluster's workload's; until then mvcc's `watchNoDup`). -/
def memberWatch (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(isServerRead s E ρ.rd ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗
    ⌜R.E = E ∧ v3rpc.memberOf γr.raft γr.kv ρ.rd ∧ kvSame ρ.rd.kv γr.kv⌝ ∗
    client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗ v3rpc.srvOnce (etcdstart.srvWOf E ρ.rd false))

instance memberWatch_persistent (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : Persistent (memberWatch γr s E ρ R) := by
  unfold memberWatch v3rpc.srvOnce; infer_instance

/-- **A member's watch facts are its `watchMemberFacts`** at the history's model, at the member's
server's watch facts. -/
theorem memberWatch_facts (V : client.WEnv GF) (γr : ReadNames) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (hWM : V.WM = v3rpc.etcdModelOfHistory γr.raft γr.kv)
    (hWL : V.WL = v3rpc.histWL γr.raft γr.kv) (hK : kvSame γr.kv V.kv)
    (hW : V.W = etcdstart.srvWOf V.R.E ρ.rd false)
    (hlog0 : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62) :
    memberWatch γr s E ρ V.R ⊢ client.watchMemberFacts V := by
  iintro #H
  iunfold memberWatch at H
  icases H with ⟨#Hrd, -, %h, #Hwl, #Hon⟩
  obtain ⟨hE, hm, hst⟩ := h
  subst hE
  ihave #Hwl' : client.srvWLaws V.W $$ []
  · rw [hW]; iexact Hwl
  ihave #Hon' : v3rpc.srvOnce V.W $$ []
  · rw [hW]; iexact Hon
  ihave #Hinvs := srvKVInvs_of_read s V.R.E ρ.rd $$ Hrd
  have hH : V.W.histLb = srvApi.histLb ρ.rd false V.R.E.γs := by rw [hW]; rfl
  have hC : V.W.crevOk = srvApi.crevOk ρ.rd := by rw [hW]; rfl
  ihave #Hlaws := client.watchLaws_hist V γr.raft γr.kv ρ.rd hWM hWL hm hH $$ Hwl'
  iunfold client.watchMemberFacts
  iframe #
  iapply client.srvKVFacts_of_off V ρ.rd (kvSame_trans hst hK) (by rw [hm.2.2.2, hlog0]) hrb hH hC
  iframe #

theorem watchEnv_addrs (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames) (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).addrs = bridges cfg := rfl

theorem watchEnv_memOf₁ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memOf cfg.Bridge1' = R₁ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ,
    eq_comm]
theorem watchEnv_memOf₂ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memOf cfg.Bridge2' = R₂ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ,
    eq_comm]
theorem watchEnv_memOf₃ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memOf cfg.Bridge3' = R₃ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ,
    eq_comm]

theorem watchEnv_memWOf₁ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memWOf cfg.Bridge1' = W₁ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memWOf, client.WEnv.idxOf, watchEnv, memWAt3, memAt3, List.range_succ,
    eq_comm]

theorem watchEnv_memWOf₂ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memWOf cfg.Bridge2' = W₂ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memWOf, client.WEnv.idxOf, watchEnv, memWAt3, memAt3, List.range_succ,
    eq_comm]

theorem watchEnv_memWOf₃ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (hcfg : cfgOk cfg) (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames)
    (pfx : GoString) :
    (watchEnv cfg R₁ R₂ R₃ W₁ W₂ W₃ γr pfx).memWOf cfg.Bridge3' = W₃ := by
  have := hcfg.b12; have := hcfg.b13; have := hcfg.b23
  simp_all [client.WEnv.memWOf, client.WEnv.idxOf, watchEnv, memWAt3, memAt3, List.range_succ,
    eq_comm]

/-- **The watcher's facts at every connection to the bridges** (see the file header). -/
theorem watchEnv_conn [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (hcfg : cfgOk cfg)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) (hp : pfx ≠ [])
    (hlog0 : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62) (s₁ s₂ s₃ : Loc) (E₁ E₂ E₃ : apply.AEnv GF)
    (ρ₁ ρ₂ ρ₃ : ReqNames) (hR₁ : R₁.E = E₁) (hR₂ : R₂.E = E₂) (hR₃ : R₃.E = E₃) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ client.eofOk ∗
      memberWatch γr s₁ E₁ ρ₁ R₁ ∗ memberWatch γr s₂ E₂ ρ₂ R₂ ∗ memberWatch γr s₃ E₃ ρ₃ R₃ ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) cfg.Bridge1'
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₁)
        (fun md => v3rpc.watchSpec R₁ (etcdstart.srvWOf E₁ ρ₁.rd false) (auth.mdTokenOf md)) ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) cfg.Bridge2'
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₂)
        (fun md => v3rpc.watchSpec R₂ (etcdstart.srvWOf E₂ ρ₂.rd false) (auth.mdTokenOf md)) ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) cfg.Bridge3'
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₃)
        (fun md => v3rpc.watchSpec R₃ (etcdstart.srvWOf E₃ ρ₃.rd false) (auth.mdTokenOf md)) ⊢
      □ ∀ (conn : Loc) (ics : List GoFunc),
        grpcConn (GF := GF) conn (bridges cfg) ics [] -∗
          client.watchConnFacts { watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx with conn := conn, ics := ics } := by
  iintro ⟨#P1, #P2, #P3, #Heof, #Hm₁, #Hm₂, #Hm₃, #Hs₁, #Hs₂, #Hs₃⟩
  iintro !> %conn %ics #Hc
  iapply watchConnFacts_of_members wp_ErrAny hAs (watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx) conn ics
  rw [watchEnv_addrs]
  simp only [bridges, isGrpcStreamsMd, watchEnv_memOf₁ cfg hcfg, watchEnv_memOf₂ cfg hcfg,
    watchEnv_memOf₃ cfg hcfg, watchEnv_memWOf₁ cfg hcfg, watchEnv_memWOf₂ cfg hcfg,
    watchEnv_memWOf₃ cfg hcfg]
  iframe #
  isplitr
  · iintro !> %i %hi
    have hn : (watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).nm = 3 := rfl
    rcases i with _ | _ | _ | i
    · iapply memberWatch_facts ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 0) γr s₁ E₁ ρ₁ rfl rfl (kvSame_refl _) (by simp [client.WEnv.atIdx, watchEnv, memWAt3, memAt3, hR₁]) hlog0 hrb
      rw [show ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 0).R = R₁ from rfl]
      iexact Hm₁
    · iapply memberWatch_facts ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 1) γr s₂ E₂ ρ₂ rfl rfl (kvSame_refl _) (by simp [client.WEnv.atIdx, watchEnv, memWAt3, memAt3, hR₂]) hlog0 hrb
      rw [show ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 1).R = R₂ from rfl]
      iexact Hm₂
    · iapply memberWatch_facts ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 2) γr s₃ E₃ ρ₃ rfl rfl (kvSame_refl _) (by simp [client.WEnv.atIdx, watchEnv, memWAt3, memAt3, hR₃]) hlog0 hrb
      rw [show ((watchEnv cfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) γr pfx).atIdx 2).R = R₃ from rfl]
      iexact Hm₃
    · exfalso; omega
  ipureintro
  exact ⟨hp, hcfg.bridgesNodup, 0, (by show 0 < 3; omega), rfl, rfl⟩

end watch

end cluster3
end EtcdGrove
end Perennial
