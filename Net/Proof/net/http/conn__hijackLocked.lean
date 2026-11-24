/-
The proof of `conn.hijackLocked` (`Net/Spec/net/http/conn__hijackLocked.lean`): `abortPendingRead`
gives the reader's resources back; a byte kept (or read and dropped) means `Z cn`, refuted by
`zLaw` with the acceptor's end not written; then the deadlines, the writer's reset, the
`ReadWriter` and `setState`.
-/
module

public import Net.Spec.net.http.conn__hijackLocked
public import Net.Spec.net.http.connReader__abortPendingRead
public import Net.Spec.net.Conn__SetDeadline
public import Spec.bufio.Writer__Reset
public import Net.Proof.net.http.ServerConnLemmas
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions]
variable [bufio_sem : bufio.Assumptions]

theorem wp_NewReadWriter (r w : Loc) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! bufio.NewReadWriter)) (Val #r)) (Val #w))
    {{ (b : Loc), RET #b; True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem conn.hijackLocked.wp_proof
    (wp_abort : connReader.abortPendingRead.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Reset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG)) :
    conn.hijackLocked.spec (GF := GF) (hG := hG) := by
  intro c cr s γ t cn a la ra P Q hs Z tm br bw sz b
  wp_start as ⟨Hhj, #Hr, #Hrwc, #Hbr, #Hbw, Hraw, #Hsrv, #Hs, Hst, #Hcr, #Htm, #Hcrwc, Hph, Hrr,
    #Hca, Hsend, #Hz, Hrdl⟩
  wp_auto
  wp_apply wp_abort cr γ t cn a la ra P hs Z tm b $$ [$Hcr $Htm $Hcrwc $Hca $Hrdl $Hph $Hrr]
    as ⟨Hph, Hrr, Hown, %b1, Hrdl⟩
  iunfold crOwn at Hown
  icases Hown with ⟨%c', %hb, %ab, Hc, Hhb, Hir, Hab, #Hcok, Hrd⟩
  iunfold crRead at Hrd
  icases Hrd with ⟨⟨%arr, Hbuf⟩, %R, Hrecv, HR⟩
  -- the reader's token at the head: a byte past it is refuted
  icases HR with (⟨%HR, %Hhb⟩ | HZ)
  rotate_left
  · iexfalso
    iunfold zLaw at Hz
    iapply Hz $$ %cn HZ Hsend
  subst HR Hhb
  wp_apply wp_SetDeadline t cn true a la ra _
      (fun _ => iprop(∃ b' : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b')) $$ [$Hca Hrdl]
    as %err0 ⟨%res0, ⟨%b2, Hrdl⟩, -⟩
  · imod deadline_au (Gg := hG.goose_globalGS) cn true (W64 0) _ b1 $$ Hrdl with ⟨%st, Hend, Hcl⟩
    imodintro
    iexists st
    iframe Hend
    iintro %res %st' %Hd Hend
    imod Hcl $$ %res %st' %Hd Hend with ⟨-, Hrdl⟩
    imodintro; iexists _; iexact Hrdl
  wp_apply wp_Reset bw sz _ $$ [$Hraw] as Hraw
  · ipureintro; right; refine ⟨_, rfl, ?_⟩
    intro h
    injection h with h
    simp only [net.TCPConn.ty, bufio.Writer.ty] at h
    injection h with h
    exact absurd h (by decide)
  wp_apply wp_NewReadWriter as %buf -
  wp_apply wp_setState c s _ (W64 3) (by decide) $$ [$Hsrv $Hs $Hst] as Hst
  iapply HΦ
  iframe Hhj Hraw Hst Hrecv Hsend Hrdl
  iunfold crLeft
  iframe Hph Hrr
  iexists c', false, ab
  iframe Hc Hhb Hir Hab
  iexists arr; iexact Hbuf

end proof

end net.http
end Perennial
