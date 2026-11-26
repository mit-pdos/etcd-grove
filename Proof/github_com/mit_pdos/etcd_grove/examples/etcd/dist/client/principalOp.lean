/-
Proof of `Spec/.../dist/client/principalOp.lean` (#50 F7 S7). Lean-first (no Rocq counterpart).

`who := in.(string)`; `principalClient(sys.([]string), who)` (its spec): on an error the answer `false`; else a user
client `userCli cl a V cfg` of one of the members' addresses `a`, whose principal is `who`'s or none, which is
`Work.spec_dist`'s client (`userClientAt_of_userCli`, `watchClient_of_userCli`; the members' fact at `a`,
`membersAt_of_mem`), with the principals' environment `akDistEnv` the service hands over (`akDistEnv_eq_G`);
`auth.Work` through it, the deferred `Close` (`clientCoreAt_of_new`), the answer `true`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkDist
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRunLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem principalOp.wp_proof
    (wp_principalClient : principalClient.spec (GF := GF) (hG := hG))
    (wp_Work : etcd_auth.Work.spec_dist (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG)) :
    principalOp.spec (GF := GF) (hG := hG) := by
  intro π Γ γR addrs hV Htb Hpe hne hauth hau hAs sys x w
  simp only [principalWire, prP, prQ, principalTok, ← akDistEnv_eq_G]
  wp_start as ⟨⟨Hlt, %sl, %Hsys, #Hsl, #Hms⟩, %Hx, #Henv, %Hw⟩
  obtain ⟨rfl, -⟩ := Hx
  subst Hsys
  ihave #Pauth : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  let V : WEnv GF := Classical.choice hV
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_principalClient sl addrs w V Γ Htb Hpe hne hau hauth) $$ [$Hlt] as %cl %err ⟨Hlt, Hc⟩
  · iframe #
  icases Hc with (⟨%Herr, %a, %cfg, %ha, #Hu, %hP⟩ | %Hfail)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hfail
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    isplitr
    · iexists sl; iframe #; ipureintro; rfl
    iexists false
    isplitr; · ipureintro; rfl
    itrivial
  subst Herr
  (try wp_auto)
  -- `auth.Work(cli, who)`: the client at `a`, the principals' environment
  ihave #Hma := membersAt_of_mem addrs Γ a ha $$ Hms
  ihave ⟨%api, #Huc⟩ := userClientAt_of_userCli cl a V cfg Γ $$ [Hu Hma]
  · iframe #
  ihave ⟨%wc, #Hwc⟩ := watchClient_of_userCli cl a V cfg Γ $$ [Hu Hma]
  · iframe #
  wp_apply (wp_Work cl api wc w a addrs V Γ cfg γR Hw ha hauth hau hP hAs) $$ [$Hlt] as Hlt
  · iframe #
  (try wp_auto)
  -- the deferred `cli.Close()`
  ihave #Hu' := Hu
  iunfold userCli at Hu'
  icases Hu' with ⟨#Hnc, #Hnp, -, -⟩
  ihave #Hcore := clientCoreAt_of_new cl [a] V $$ [Hnc Hnp]
  · iframe #
  wp_apply wp_Close as %ce -
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  isplitr
  · iexists sl; iframe #; ipureintro; rfl
  iexists true
  isplitr; · ipureintro; rfl
  itrivial

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
