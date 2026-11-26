/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/MainDeploymentLogger.lean` (N5).
Lean-first (no Rocq counterpart).

`MainDeploymentLogger(d, i, lg)`: `deployment.WellFormed(d)` first (`WellFormed.spec`: `nil` only for a well-formed
deployment); on its error, or `i` out of range, it returns. Else the deployment is well formed (at most 64 members,
so `i` fits), member `i`'s share applies, and it runs `MainLogger(ConfigOf(d, i), lg)`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeploymentLogger
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainLogger
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.ConfigOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem MainDeploymentLogger.wp_proof
    (wp_WellFormed : WellFormed.spec (GF := GF) (hG := hG))
    (wp_ConfigOf : ConfigOf.spec (GF := GF) (hG := hG))
    (wp_MainLogger : MainLogger.spec (GF := GF) (hG := hG)) :
    MainDeploymentLogger.spec (GF := GF) (hG := hG) := by
  intro CS π TB RB v d i m lg ps ctxs boot Hm Hauth Hfips Hbf Hbgo HLv Haf Hbuq Hrf Hdbo Hms
  wp_start as ⟨#Hzlg, Htok, #Hrepr, #Hvoff, Hwa, Hshare⟩
  ihave #Pdep : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_WellFormed v d Hfips) $$ [] as %err %Herr
  · iframe #
  cases err with
  | ok ei =>
    -- the check failed: return
    repeat' (first
      | wp_if_destruct
      | wp_auto)
    iapply HΦ; itrivial
  | nil =>
  have Hd : d.WellFormed := Herr rfl
  obtain ⟨-, -, -, hlen, -⟩ := Hd.members
  have hi : i < d.members.length := (List.getElem?_eq_some_iff.1 Hm).1
  have hlen64 : d.members.length ≤ 64 := by unfold typed.maxMembers at hlen; exact hlen
  iunfold deploymentRepr at Hrepr
  icases Hrepr with ⟨#Hmem, %Htok', %Hcfg, #Hwl, %ss, #Hnd, #Hns⟩
  ihave %Hsl := ownSlice_len $$ Hmem
  have hsl := Hsl.1
  rw [List.length_map] at hsl
  repeat' (first
    | wp_if_destruct
    | wp_auto)
  -- `i < 0` and `i >= len(d.Members)` are false: `i` is a member's index, below 64
  · exfalso; word
  · exfalso; word
  -- `MainLogger(ConfigOf(d, i), lg)`
  wp_apply (wp_ConfigOf v d i m Hm hlen64) $$ [] as %cv #Hcv
  · iunfold deploymentRepr
    isplitr; · iexact Hmem
    isplitr; · ipureintro; exact Htok'
    isplitr; · ipureintro; exact Hcfg
    isplitr; · iexact Hwl
    iexists ss
    isplitr; · iexact Hnd
    iexact Hns
  (try wp_auto)
  ihave Hsh := Hshare $$ %Hd
  wp_apply (wp_MainLogger cv lg d i m ps ctxs boot Hd Hm Hauth Hfips Hbf Hbgo HLv Haf Hbuq Hrf Hdbo Hms)
    $$ [Htok Hwa Hsh]
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial

end
