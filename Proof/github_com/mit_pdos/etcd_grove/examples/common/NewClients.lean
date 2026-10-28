/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/NewClients.lean` (2026-10-23; linkv3p's
`newClient` proof until then, the partition plan's S3a). Lean-first (no Rocq counterpart). `New` over
`clientCfgOk` of the configuration's literal (the endpoints read-only, no dial options, no TLS, no
credentials, the logger; `DialTimeout` and the keepalive pair unconstrained, the default retries).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClients

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem NewClients.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    NewClients.spec (GF := GF) (hG := hG) := by
  intro eps addrs lg V Htb Hlg Hplain
  wp_start as #Heps
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_auto
  -- `clientv3.New(Config{Endpoints: eps, DialTimeout: ..., DialKeepAliveTime: ..., Logger: lg})`
  wp_apply (wp_New _ addrs V (fun _ => iprop(True))) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact Hplain
      · simp [Hlg]
    isplitr
    · iunfold clientAuthPre; ileft; ipureintro; left; rfl
    ipureintro; exact Htb
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  · subst Hcerr
    iapply HΦ
    ileft
    iframe #
    ipureintro; rfl
  · obtain ⟨Hcerr, Hnull⟩ := Hcfail
    iapply HΦ
    iright
    ipureintro; exact ⟨Hcerr, Hnull⟩

end proof

end common
end EtcdGrove
end Perennial
