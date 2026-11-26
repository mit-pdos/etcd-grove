/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/ownLease.lean`: the grant
(`etcd_dist.authd.Lease_GrantOn_dist` at the member the endpoint serves; `grantPut.wp_proof`'s first half), its
live lease's lessor lower bound (`lease.leaseLiveFrom_lb`). Lean-first (no Rocq counterpart); F7 (fork), option (3).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ownLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantOnDist
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
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

set_option maxHeartbeats 1600000 in
theorem ownLease.wp_proof
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Grant : Lease_GrantOn_dist.spec (GF := GF) (hG := hG)) :
    ownLease.spec (GF := GF) (hG := hG) := by
  intro π cl addr V Γ mid cfg γR L₀ n₀ Qg Hau Hls Hauth Hrev HγR hAs
  wp_start as ⟨Hlt, #Hu, #Hat, #HL0, #Hn0, #HQg⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave ⟨%lp, #Hlu⟩ := leaseUserAt_of_userCli cl addr V cfg Γ mid $$ [Hu Hat]
  · iframe #
  ihave #Hlu' := Hlu
  iunfold leaseUserAt at Hlu'
  icases Hlu' with ⟨#Hlc, -, %Htok⟩
  iunfold view.leaseClientAt at Hlc
  icases Hlc with ⟨-, -, #Hlf, -⟩
  (try wp_auto)
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -, #Hgout, -⟩
  (try wp_auto)
  wp_apply (wp_Grant cl lp addr V Γ mid cfg γR L₀ n₀ gctx gcd none (W64 9000000000) Qg Hau Hls Hauth Hrev HγR
      (outTokOk_none _)) $$ [$Hlt] as %gr %gerr ⟨Hlt, Hg⟩
  · iframe #
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hg with (⟨%Hgerr, %mg, -, -, -, ⟨%gi, %gl, Hlv, -⟩, -, -⟩ | %Hgfail)
  · subst Hgerr
    ihave ⟨%m, -, #Hlb, -⟩ := lease.leaseLiveFrom_lb (Γ.ls mid) gi mg.id gl $$ Hlv
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitr
    · ipureintro; rfl
    iexists m; iexact Hlb
  · cases gerr with
    | nil => exact absurd rfl Hgfail.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
