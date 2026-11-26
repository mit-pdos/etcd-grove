/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/newUserClient.lean`: the configuration
literal (one `WithNoProxy()` option, `zap.NewNop()`'s logger) and `etcd_dist.authd.New_user_dist`.
Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewUserDist
public import Spec.go_uber_org.zap.NewNop
public import Spec.google_golang_org.grpc.WithNoProxy
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem newUserClient.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_WithNoProxy : grpc.WithNoProxy.spec (GF := GF) (hG := hG))
    (wp_New : New_user_dist.spec (GF := GF) (hG := hG)) :
    newUserClient.spec (GF := GF) (hG := hG) := by
  intro π addr name pw V Γ Htb Hpe Hsz Hname Hpw Hau Hauth
  wp_start as ⟨Hlt, #Hms⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply wp_NewNop as %lg #Hzlg
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  (try wp_auto)
  wp_apply wp_WithNoProxy as %o #Ho
  wp_apply wp_slice_literal (V := GoInterface) [o]
  try (isplitr; (ipureintro; rfl))
  iintro %dol ⟨Hdol, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hdol with #Hdol
  haveI : ThreadBoundLe GF (2 ^ 30) := ⟨Htb⟩
  wp_apply (wp_New _ [addr] V Γ Hau Hauth (by simp [principalOf, Hname, Hpw])) $$ [$Hlt]
    as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iexists 1
        iunfold noProxyOptsAt, dialOptsAt
        iexists [o]
        iframe Hdol
        (try simp only [List.replicate_succ, List.replicate_zero])
        iapply BigSepL2.bigSepL2_singleton.2
        iexact Ho
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ Hpe
      · simp [Hlg]
    ipureintro; exact Hsz
  icases Hcl with (⟨%Hcerr, #Hnc, #Hcfg, -⟩ | %Hcfail)
  · subst Hcerr
    ihave #HNP : clientNoProxy (GF := GF) cl $$ []
    · iunfold clientNoProxy
      iexists _, 1
      isplitr
      · ipureintro; omega
      isplitr
      · iexact Hcfg
      iunfold noProxyOptsAt, dialOptsAt
      iexists [o]
      (try simp only)
      iframe Hdol
      (try simp only [List.replicate_succ, List.replicate_zero])
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Ho
    iapply HΦ
    iframe Hlt
    ileft
    isplitr
    · ipureintro; rfl
    iexists _
    isplitl
    · iunfold userCli
      iframe #
      ipureintro; rfl
    ipureintro
    simp [principalOf, Hname, Hpw]
  · obtain ⟨Hcerr, Hnull⟩ := Hcfail
    iapply HΦ
    iframe Hlt
    iright
    ipureintro; exact ⟨Hcerr, Hnull⟩

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
