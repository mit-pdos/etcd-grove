/- Lean-first (no Rocq counterpart).

Proof of `MainReadyAuth.spec` (`MainReady`'s auth arm, #50 F7 S12) over `NodeCount` and `RunAuth.spec`: the guards
as `MainReady.wp_proof`'s watch arm, then `RunAuth` from `authShare`'s parts.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReadyAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormedLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open Net client etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 1600000 in
/-- See the file header. -/
theorem MainReadyAuth.wp_proof
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRA : RunAuth.spec (GF := GF) (hG := hG)) :
    MainReadyAuth.spec (GF := GF) (hG := hG) := by
  intro π ρ _ _ _ w eps nodes epsL ns ready
  wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
  obtain ⟨hk, hV, htb, hrb, hAs⟩ := Hp
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_auto
  wp_if_destruct
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial
  have hne : epsL ≠ [] := by
    intro h; rw [h] at Hel; simp at Hel; word
  wp_apply hNC
  wp_if_destruct
  · wp_func_call; wp_call; wp_auto
    simp only [Workload.val, hk]
    wp_auto
    iunfold authShare at Hsh
    icases Hsh with ⟨%Γ, %γR, %σ0, %Hq, #Hms, #HkvI, #HL0, HkV, Hview, HPS⟩
    obtain ⟨hauth, hγR, hau, hσ0⟩ := Hq
    icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
    wp_apply (hRA Γ eps nodes epsL ns ready γR σ0 hV htb hAs hne hauth hγR hau hσ0)
      $$ [Hlt HkV Hview HPS] as %r -
    · iframe #; iframe
    iapply HΦ; ipureintro; trivial
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end etcd_dist
end EtcdGrove
end Perennial

end
