/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/ClientPutDist.lean`: `cli.Put` through the
`KV` field (`Client.Put`'s promotion, `ptr_Put_unfold`) is `(*kv).Put`, whose cross-machine contract is the
interim axiom `KV_Put_dist` (a hypothesis here), at putget's put update fired at most once
(`putAu_of_putGetInvK`, `kvOpAu_one`). Until 2026-11-25 (O1-B, `notes/etcd-dist-plan.md` §18.3) an
axiom of its own over the published view. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientPutDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.KeyOps

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem Client_Put_dist.wp_proof (wp_KV_Put : KV_Put_dist.spec (GF := GF) (hG := hG)) :
    Client_Put_dist.spec (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid γf ci cd key val sl hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hnp, #Hat, #Hctx, #Hce, #Hopts, #Hinv⟩ HΦ
  ihave #Hms := membersAt_one (Gg := hG.goose_globalGS) ep Γ mid $$ Hat
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl [ep] V Γ $$ [Hcl Hnp Hms]
  · iframe #
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  -- putget's put update, fired at most once (`Γ.auth = false`: the put is sent at most once)
  ihave #Hau := putAu_of_putGetInvK Γ.kv γf key val $$ Hinv
  ihave Hau1 := kvOpAu_one Γ.kv (.put (putKeyOp key val)) (fun _ => monoNatLbOwn γf 1) $$ Hau
  iunfold kvOpAu1 at Hau1
  iunfold kvAu1 at Hau1
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_KV_Put cl api [ep] V Γ ci cd key val sl [] (fun _ => iprop(□ monoNatLbOwn γf 1)) hauth)
    $$ [Hlt Hau1] as %resp %err ⟨Hlt, Hout⟩
  · (try iframe Hlt)
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    isplitl [Hau1]
    · simp only [show putWireOf (opPutModel key val []) = putKeyOp key val from rfl]
      iexact Hau1
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, -, #HQ, -, -⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexact HQ
  · iright
    ipureintro; exact Herr

end proof

end etcd_dist
end EtcdGrove
end Perennial
