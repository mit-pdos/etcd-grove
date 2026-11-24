/-
The proof of `listen` (`Net/Spec/.../lib/remote/listen.lean`): `net.Listen` at `a` (its update
`listen_au`, and `a`'s validity `addrTok_ok`, from `a`'s protocols `svcAddr`), retried after a
`time.Sleep` while it fails; the loop's invariant: the last `Listen`'s results, a listener or an
error (non-nil, `net.opErr_netErr`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.listen
public import Net.Spec.net.Listen
public import Perennial.Spec.time.Sleep
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem listen.wp_proof
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    listen.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S a
  wp_start as #Haddr
  iunfold svcAddr at Haddr
  ihave %Hok := addrTok_ok a $$ [Haddr]
  · iapply addrProto_tok $$ Haddr
  wp_auto
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a as %li %err HL
  · iframe %Hok
    iapply listen_au $$ Haddr
  ihave HI : (∃ (li : GoInterface) (err : GoInterface), "Hl" ∷ l_ptr ↦ li ∗ "Herr" ∷ err_ptr ↦ err ∗
      "HL" ∷ ((⌜err = GoInterface.nil⌝ ∗ ∃ l, net.isListener li l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
          netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
        ∃ pe : Loc, ⌜err = interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe⌝) : IProp GF)
      $$ [l err HL]
  · iexists li, err
    iframe l err
    icases HL with (⟨%He, Hl⟩ | ⟨%x, %ex, -, #HE, -⟩)
    · ileft
      iframe Hl
      ipureintro; exact He
    · iright
      icases net.opErr_netErr _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne
      iexists pe
      ipureintro; rfl
  wp_for HI
  icases HL with (⟨%He, Hli⟩ | ⟨%pe, %He⟩)
  · -- listening: return the listener
    subst He
    wp_auto
    cleanup_bool_decide
    (try wp_auto)
    iapply HΦ
    iexact Hli
  · -- a failure: sleep, then listen again
    subst He
    wp_auto
    cleanup_bool_decide
    (try wp_auto)
    wp_apply wp_Sleep
    wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a as %li' %err' HL
    · iframe %Hok
      iapply listen_au $$ Haddr
    wp_for_post
    iframe
    iexists li', err'
    iframe Hl Herr
    icases HL with (⟨%He', Hli⟩ | ⟨%x, %ex, -, #HE, -⟩)
    · ileft
      iframe Hli
      ipureintro; exact He'
    · iright
      icases net.opErr_netErr _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe', rfl⟩ := Hne
      iexists pe'
      ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
