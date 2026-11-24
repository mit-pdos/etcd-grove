/-
The proof of `Net/Spec/net/Conn__Write.lean`: the interface call resolves to
`conn.Write.impl` (`*TCPConn`'s promoted `Write`), Go's loop (`model.writeLoop`); each iteration
reads the bytes of `b[nn:]` and makes the extension's `Write` of them, taking the caller's accessor
(`Net.wp_net_Write`). The loop's invariant (Löb induction): `nn` bytes written, `P (bs.take nn)
none`, and `nn = 0` or fewer than all; and (D25) after the first step, the end's write lock
(`netWLock`), which the first step took and the last gives back (`writeLast`).
-/
module

public import Net.Spec.net.Conn__Write
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Conn.Write.wp_proof : Conn.Write.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs dq ed P
  unfold connAt connFd
  wp_start as ⟨⟨%nw, %Hnw, ⟨%fd, #Ht, #Hfd⟩, #Hla, #Hra, #Hat⟩, Hsl, #Hed, HP, #Hacc⟩
  ihave ⟨%xd, #Hxd⟩ := _root_.Perennial.internal.poll.errDeadlineExceeded_of_pkgInit $$ Hpkg
  icombine Hed Hxd gives %hed
  subst hed
  ihave ⟨%v, %hv, #Hv⟩ := fdAt_elim _ _ _ _ _ $$ Hfd
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed Hv
  (try wp_method_call)
  wp_auto
  wp_apply wp_conn_ok _ fd Hfdn $$ conn
  iStructNamed conn
  wp_auto
  wp_apply wp_fd_Write fd cn s a _ _ _ b bs dq _ P $$ Hfd Hat Hsl Hed HP Hacc
    as %n %e %w %res HP Hsl %Hw #He
  rcases res with _ | k
  · unfold resKind; icases He with %he; subst he
    wp_auto
    iapply HΦ
    iexists w, none
    iframe HP Hsl
    isplitr
    · ipureintro; exact Hw
    unfold resErr; ipureintro; rfl
  · rw [show resKind (GF := GF) (some k) (some (interface.mkOk
        (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #xd)) (· = go!"write") e =
      kindErr k (some (interface.mkOk
        (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #xd)) (· = go!"write") e from rfl]
    ihave %hne := kindErr_ne_nil k _ _ e
      (fun _ h => by cases h; unfold interface.mkOk; exact fun h' => by cases h') $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    wp_auto
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iexists w, some k
    iframe HP Hsl
    isplitr
    · ipureintro; exact Hw
    unfold resErr opErr
    iexists GoInterface.ok ie
    iframe He
    iexists pe, v.net'
    iframe Hpe
    ipureintro; exact ⟨rfl, Hnw⟩

end proof

end net
end Perennial
