/-
Proof of `Spec/.../dist/client/NodeMainAuth.lean` (#50 F7 S8). Lean-first (no Rocq counterpart).

`NodeMainWatch.wp_proof`'s guards (`NodeCount`: 4 for `Auth`), then the auth arm: `remote.ServeClient` at the
principal service (`principalSvcG`, the share's protocols as they are: the principals' wire holds no values)
with `principalCodec`'s codec and `principalOp` as the report's loop (`reportOp_svcOp`) over the machine's
resource `principalTok`, which the client closure (`func(int) any { return eps }`) hands over.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMainAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalOp
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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]

set_option maxHeartbeats 1600000 in
theorem NodeMainAuth.wp_proof
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (wp_principalCodec : principalCodec.spec (GF := GF) (hG := hG))
    (wp_principalOp : principalOp.spec (GF := GF) (hG := hG))
    (wp_ServeClient : ∀ [π : NetProtoGS] [ρ : RemoteGS],
      github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
        (GF := GF) (hG := hG) (I := GoString) (O := Bool)) :
    NodeMainAuth.spec (GF := GF) (hG := hG) := by
  intro π ρ w c addr eps epsL
  wp_start as ⟨%Hk, #Heps, HNP⟩
  have hnc : w.goNodeCount = W64 4 := by simp [Workload.goNodeCount, Hk]
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
  have h1 : sint.Z c < 4 := by word
  have hne : epsL ≠ [] := by
    intro h
    rw [h] at Hel
    simp at Hel
    word
  ispecialize HNP $$ %(And.intro h0 (And.intro h1 hne))
  iunfold nodeAuthPre at HNP
  icases HNP with ⟨Hlt, %Γ, %γR, %Hpp, #Hms, #Haddr⟩
  obtain ⟨hauth, hau, hV, htb, hpl, hAs⟩ := Hpp
  simp only [Workload.val, Hk]
  wp_auto
  ipersist eps
  -- `remote.ServeClient(c, addr, newClient, principalOp, principalCodec(), principalAttempt)`
  wp_apply (wp_principalCodec (prP (Gg := hG.goose_globalGS) Γ γR epsL) prQ) as %cd #Hcd
  wp_apply (wp_ServeClient (principalSvcG (Gg := hG.goose_globalGS) Γ γR epsL) c addr _ _ cd _
      (principalTok Γ epsL)) $$ [Hlt] as ⟨⟩
  (try iframe Prem)
  (try iframe Hcd)
  isplitr [Hlt]
  · iexact Haddr
  isplitr [Hlt]
  · iapply reportOp_svcOp
    unfold reportOp
    iintro %sys %x %i
    iintro !> %Ψ ⟨Htok, #Hiv, HP⟩ HΨ
    iapply (wp_principalOp Γ γR epsL hV htb hpl hne hauth hau hAs sys x i) $$ [Htok HP] HΨ
    iframe
    iframe #
  · iintro %Ψ HΨ
    wp_auto
    ispecialize HΨ $$ %(interface.mkOk (go.GoType.SliceType go.string) #eps)
    iapply HΨ
    iunfold principalTok
    isplitl [Hlt]
    · iexact Hlt
    iexists eps
    iframe #
    ipureintro; rfl

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
