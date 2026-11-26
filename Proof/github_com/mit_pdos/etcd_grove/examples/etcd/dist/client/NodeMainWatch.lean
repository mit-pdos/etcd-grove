/-
Proof of `Spec/.../dist/client/NodeMainWatch.lean` (#50 N10a). Lean-first (no Rocq counterpart).

M1's `NodeMain.wp_proof` up to the arm (the guards, `NodeCount`, `Rotate`), then the watch arm:
`newClient(Rotate(eps, c))` (its failure returns), the client a KV client of the share's view
(`kvClient_of_new`), and `remote.ServeClient` at the writer service (`writerSvc`, whose protocols are the
share's, `svcAddr_writerSvc`) with `writerCodec`'s codec, `writerOp` as the report's loop
(`reportOp_svcOp`) over the machine's resource `writerTok`, which the client closure hands over.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMainWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]

set_option maxHeartbeats 1600000 in
theorem NodeMainWatch.wp_proof
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRot : Rotate.spec (GF := GF) (hG := hG))
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_writerCodec : writerCodec.spec (GF := GF) (hG := hG))
    (wp_writerAttempt : writerAttempt.spec (GF := GF) (hG := hG))
    (wp_writerOp : writerOp.spec (GF := GF) (hG := hG))
    (wp_ServeClient : ∀ [π : NetProtoGS] [ρ : RemoteGS],
      github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
        (GF := GF) (hG := hG) (I := WN × List wkv) (O := List wrec)) :
    NodeMainWatch.spec (GF := GF) (hG := hG) := by
  intro π ρ w c addr eps epsL
  wp_start as ⟨%Hp, #Heps, HNP⟩
  obtain ⟨Hk, Hb⟩ := Hp
  have hnc : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, Hk]
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  ihave #Prem : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_apply hNC
  rw [hnc]
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  have h0 : 0 ≤ sint.Z c := by word
  have h1 : sint.Z c < sint.Z w.clients := by word
  have hne : epsL ≠ [] := by
    intro h
    rw [h] at Hel
    simp at Hel
    word
  ispecialize HNP $$ %(And.intro h0 (And.intro h1 hne))
  iunfold nodeWatchPre at HNP
  icases HNP with ⟨Hlt, %Γ, %Hpp, #Hms, #Haddr⟩
  obtain ⟨hauth, hV, htb, hpl, hAs⟩ := Hpp
  simp only [Workload.val, Hk]
  wp_auto
  -- `cli, err := newClient(Rotate(eps, c))`
  wp_apply (hRot (V := GoString) (T := go.string) eps DFrac.discard epsL c) as %out ⟨-, Hout⟩
  · iframe #
    ipureintro
    intro _
    exact ⟨h0, Hb h0 h1⟩
  imod ownSlice_persist _ _ _ $$ Hout with #Hout
  wp_apply (wp_newClient out (rotateL epsL (sint.nat c)) (Classical.choice hV) htb hpl) $$ [$Hlt]
    as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp⟩ | %Hcfail)
  rotate_left
  · -- no client: `NodeMain` returns
    obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl (rotateL epsL (sint.nat c)) (Classical.choice hV) Γ
    $$ [Hnc Hnp Hms]
  · iframe #
  wp_auto
  ipersist cli
  -- `remote.ServeClient(c, addr, newClient, writerOp, writerCodec(), writerAttempt(w.Ops))`
  wp_apply (wp_writerCodec WN (wP (Gg := hG.goose_globalGS) Γ) (wQ (Gg := hG.goose_globalGS) Γ))
    as %cd #Hcd
  wp_apply wp_writerAttempt as %d -
  wp_apply (wp_ServeClient (writerSvc Γ) c addr _ _ cd d
      (writerTok Γ (rotateL epsL (sint.nat c)) (Classical.choice hV))) $$ [Hlt] as ⟨⟩
  (try iframe Prem)
  (try iframe Hcd)
  isplitr [Hlt]
  · rw [← svcAddr_writerSvc]; iexact Haddr
  isplitr [Hlt]
  · iapply reportOp_svcOp
    unfold reportOp
    iintro %sys %x %i
    iintro !> %Ψ ⟨Htok, #Hiv, HP⟩ HΨ
    iapply (wp_writerOp Γ (rotateL epsL (sint.nat c)) (Classical.choice hV) hauth hAs sys x i)
      $$ [Htok HP] HΨ
    iframe
    iframe #
  · iintro %Ψ HΨ
    wp_auto
    iapply HΨ
    unfold writerTok
    iexists cl, api
    iframe Hlt Hkc
    ipureintro; rfl

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
