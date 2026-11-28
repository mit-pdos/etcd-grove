/-
The proof of `rpctransport.Transport.send`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.wp_proof
    (wp_Call : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.Call.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C j M req reply Φm Rargs D Θ
  wp_start as ⟨#Ht, %Hsm, Henc, HD, #Hdec⟩
  obtain ⟨Hsplit, Hlen, Hrne⟩ := Hsm
  unfold isTrans
  iNamed Ht
  wp_auto
  wp_apply (wp_map_lookup2 _ _ pm P j DfracDiscarded) $$ [$Hpm] as -
  cases hP : P !! j with
  | none =>
    simp only [Option.getD, Option.isSome]
    wp_auto
    wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iright
    iapply errStr_intro $$ HE
  | some p =>
    simp only [Option.getD, Option.isSome]
    ihave #Hp := (BigSepM.bigSepM_lookup (Φ := fun a p => peerOk (GF := GF) γ snapP W a p)
      (show get? P j = some p from hP)) $$ HP
    iunfold peerOk at Hp
    icases Hp with ⟨%na, #Hc, #Hsv⟩
    iunfold svcAt at Hsv
    icases Hsv with ⟨%S, %HS, #Hincl⟩
    wp_auto
    have hsm : (go!"RaftRPC." : GoString) ++ M = svcName ++ go!"." ++ M := rfl
    rw [hsm]
    ihave Henc := Hlaws.enc_mono req _
      (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ S M bs Φm ∗ Rargs)) $$ [Henc]
    · iframe Henc
      iintro %bs ⟨%Hl, Hd, HR⟩
      iframe HR
      isplitr; · ipureintro; exact Hl
      iapply Hincl $$ Hd
    wp_apply (wp_Call p W na (svcName ++ go!"." ++ M) svcName M S req reply Φm Rargs D Θ C d
        (C.enc req (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ S M bs Φm ∗ Rargs))))
      $$ [$Hc $Hcodec $Henc $HD $Hdec] as %r Hr
    · isplitr
      · ipureintro; exact ⟨Hsplit, HS, Hrne⟩
      isplitr
      · ipureintro; exact Hlen
      iintro H; iexact H
    (try simp only [CallOK])
    icases Hr with (⟨%Hr0, -, %rep, HΘ⟩ | ⟨%Hr1, -⟩ | %Hr2)
    · subst Hr0
      wp_auto
      iapply HΦ
      ileft
      isplitr; · ipureintro; rfl
      iexists rep; iexact HΘ
    · subst Hr1
      wp_auto
      wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
      (try wp_auto)
      iapply HΦ
      iright
      iapply errStr_intro $$ HE
    · subst Hr2
      wp_auto
      wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
      (try wp_auto)
      iapply HΦ
      iright
      iapply errStr_intro $$ HE

end proof

end Perennial
