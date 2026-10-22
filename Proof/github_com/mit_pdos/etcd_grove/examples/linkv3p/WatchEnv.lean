/-
**The clients' watch environment at the cluster** (W4c of `notes/watch-cut-plan.md`,
2026-10-22). Lean-first, no Rocq counterpart.

`watchEnv R₁ R₂ R₃ γr pfx` (`Defs.lean`): the three members at their bridges, the watch contract
at the cluster's history. A member's watch facts (`memberWatch`: its read view, its watch server,
no key written twice in a revision of its logs, its names the history's) give its
`watchMemberFacts` (`memberWatch_facts`: the laws by `watchLaws_hist`), and the three with their
`Watch` streams at the bridges give the watcher's facts at every connection to the bridges
(`watchEnv_conn`, by `watchConnFacts_of_members`), what `isNewClient_watcher_of` takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs
public import Proof.go_etcd_io.etcd.client.v3.WatchLawsHist
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section watch
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member's watch facts** (persistent): its read view at its apply environment, its watch
server there, no key written twice in a revision of its logs (from the workload,
`srvNoDupKeys_wk`), its names the history's (`memberOf`). -/
def memberWatch (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(isServerRead s E ρ.rd ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ client.srvNoDupKeys R ∗
    ⌜R.E = E ∧ v3rpc.memberOf γr.raft γr.kv ρ.rd⌝)

instance memberWatch_persistent (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : Persistent (memberWatch γr s E ρ R) := by
  unfold memberWatch; infer_instance

/-- **A member's watch facts are its `watchMemberFacts`** at the history's model. -/
theorem memberWatch_facts (V : client.WEnv GF) (γr : ReadNames) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (hWM : V.WM = v3rpc.etcdModelOfHistory γr.raft γr.kv)
    (hWL : V.WL = v3rpc.histWL γr.raft γr.kv) (hlog0 : γr.kv.log0 = [[], []]) :
    memberWatch γr s E ρ V.R ⊢ client.watchMemberFacts V := by
  iintro #H
  iunfold memberWatch at H
  icases H with ⟨#Hrd, ⟨%pw, #Hws⟩, #Hnd, %h⟩
  obtain ⟨hE, hm⟩ := h
  subst hE
  ihave %Hlink := client.watchSrvLink_of_server pw V.R $$ Hws
  ihave #Htok := client.watchTokPool_of_server pw V.R $$ Hws
  ihave #Hsm := client.srvLogsSmall_of_read V.R s ρ.rd Hlink $$ Hrd
  ihave #Hinvs := client.srvKVInvs_of_read s V.R.E ρ.rd $$ Hrd
  ihave #Hlaws := client.watchLaws_hist V γr.raft γr.kv ρ.rd pw hWM hWL hm hlog0 $$ [Hinvs Hws]
  · iframe #
  iunfold client.watchMemberFacts
  iframe #
  ipureintro; exact Hlink

theorem watchEnv_addrs (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) :
    (watchEnv R₁ R₂ R₃ γr pfx).addrs = [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] := rfl

theorem watchEnv_memOf₁ (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) :
    (watchEnv R₁ R₂ R₃ γr pfx).memOf bridgeAddr₁ = R₁ := by
  simp [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ, List.find?]
theorem watchEnv_memOf₂ (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) :
    (watchEnv R₁ R₂ R₃ γr pfx).memOf bridgeAddr₂ = R₂ := by
  simp [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ, List.find?]
theorem watchEnv_memOf₃ (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) :
    (watchEnv R₁ R₂ R₃ γr pfx).memOf bridgeAddr₃ = R₃ := by
  simp [client.WEnv.memOf, client.WEnv.idxOf, watchEnv, memAt3, List.range_succ, List.find?]

/-- **The watcher's facts at every connection to the bridges** (see the file header). -/
theorem watchEnv_conn [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) (hp : pfx ≠ [])
    (hlog0 : γr.kv.log0 = [[], []]) (s₁ s₂ s₃ : Loc) (E₁ E₂ E₃ : apply.AEnv GF)
    (ρ₁ ρ₂ ρ₃ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ client.eofOk ∗
      memberWatch γr s₁ E₁ ρ₁ R₁ ∗ memberWatch γr s₂ E₂ ρ₂ R₂ ∗ memberWatch γr s₃ E₃ ρ₃ R₃ ∗
      isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) bridgeAddr₁
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₁.γ) (v3rpc.watchSpec R₁) ∗
      isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) bridgeAddr₂
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₂.γ) (v3rpc.watchSpec R₂) ∗
      isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) bridgeAddr₃
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R₃.γ) (v3rpc.watchSpec R₃) ⊢
      □ ∀ (conn : Loc) (ics : List GoFunc),
        grpcConn (GF := GF) conn [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] ics [] -∗
          client.watchConnFacts { watchEnv R₁ R₂ R₃ γr pfx with conn := conn, ics := ics } := by
  iintro ⟨#P1, #P2, #P3, #Heof, #Hm₁, #Hm₂, #Hm₃, #Hs₁, #Hs₂, #Hs₃⟩
  iintro !> %conn %ics #Hc
  iapply watchConnFacts_of_members wp_ErrAny hAs (watchEnv R₁ R₂ R₃ γr pfx) conn ics
  rw [watchEnv_addrs]
  simp only [isGrpcStreams, watchEnv_memOf₁, watchEnv_memOf₂, watchEnv_memOf₃]
  iframe #
  isplitr
  · iintro !> %i %hi
    have hn : (watchEnv R₁ R₂ R₃ γr pfx).nm = 3 := rfl
    rcases i with _ | _ | _ | i
    · iapply memberWatch_facts ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 0) γr s₁ E₁ ρ₁ rfl rfl hlog0
      rw [show ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 0).R = R₁ from rfl]
      iexact Hm₁
    · iapply memberWatch_facts ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 1) γr s₂ E₂ ρ₂ rfl rfl hlog0
      rw [show ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 1).R = R₂ from rfl]
      iexact Hm₂
    · iapply memberWatch_facts ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 2) γr s₃ E₃ ρ₃ rfl rfl hlog0
      rw [show ((watchEnv R₁ R₂ R₃ γr pfx).atIdx 2).R = R₃ from rfl]
      iexact Hm₃
    · exfalso; omega
  ipureintro
  refine ⟨hp, ?_, 0, (by show 0 < 3; omega), rfl⟩
  first
    | (rw [watchEnv_addrs]; decide)
    | decide

end watch

end linkv3p
end EtcdGrove
end Perennial
