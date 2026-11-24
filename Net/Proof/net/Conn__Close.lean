/-
The proof of `Net/Spec/net/Conn__Close.lean`: the interface call resolves to
`conn.Close.impl` (`*TCPConn`'s promoted `Close`), the extension's `Close`, taking the caller's
update (`Net.wp_net_Close`).
-/
module

public import Net.Spec.net.Conn__Close
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

theorem Conn.Close.wp_proof : Conn.Close.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra Q
  unfold connAt connFd
  wp_start as ⟨⟨%nw, %Hnw, ⟨%fd, #Ht, #Hfd⟩, #Hla, #Hra, #Hat⟩, HAU⟩
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
  wp_apply wp_fd_Close fd cn s a _ _ _ Q $$ Hfd Hat HAU as %res %e HQ #He
  rcases res with _ | k
  · unfold resKind; icases He with %he; subst he
    wp_auto
    iapply HΦ
    iexists none; iframe HQ
    unfold resErr; ipureintro; rfl
  · rw [show resKind (GF := GF) (some k) none (· = go!"close") e =
      kindErr k none (· = go!"close") e from rfl]
    ihave %hne := kindErr_ne_nil k none _ e (fun _ h => by cases h) $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    wp_auto
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iexists some k
    iframe HQ
    unfold resErr opErr
    iexists GoInterface.ok ie
    iframe He
    iexists pe, v.net'
    iframe Hpe
    ipureintro; exact ⟨rfl, Hnw⟩

end proof

end net
end Perennial
