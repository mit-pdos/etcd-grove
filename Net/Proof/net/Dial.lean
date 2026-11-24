/-
The proof of `Net/Spec/net/Dial.lean`: `Dial.impl`'s extension `Dial` (`Net.wp_net_Dial`),
then a new `*TCPConn` holding the dialer's end, as a `Conn`.
-/
module

public import Net.Spec.net.Dial
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

theorem Dial.wp_proof : Dial.spec (GF := GF) (hG := hG) := by
  intro nw hnw a Qfail Qok
  wp_start as ⟨%Hla, HAU⟩
  wp_auto
  wp_apply wp_netOk nw hnw
  (try wp_auto)
  wp_apply wp_extDial a $$ %Hla
  isplit
  · icases HAU with ⟨HQf, -⟩
    unfold failV
    wp_auto
    wp_apply wp_anyTCPAddr as %x #Hx
    wp_apply wp_extAnyString as %nm
    wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
    · unfold edAt; itrivial
    (try wp_auto)
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iright
    iframe HQf
    iexists x
    iframe Hx
    unfold resErr opErr
    iexists e
    iframe He
    iexists pe, nw
    iframe Hpe
    ipureintro; exact ⟨rfl, hnw⟩
  · icases HAU with ⟨-, HAU⟩
    imod HAU with ⟨%S, Hp, Hk⟩
    imodintro
    iexists S
    iframe Hp
    iintro %c %hc Hp #Hat Hfr
    ihave Hk := Hk $$ %c %hc Hp Hat Hfr
    isplit
    · icases Hk with ⟨Hk, -⟩
      iintro Hfr
      imod Hk $$ Hfr with HQ
      imodintro
      wp_auto
      wp_apply wp_newConn c false a nw $$ %hnw Hat as %tc %la %ra #Hc
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists c
      iframe HQ
      unfold isConn
      iexists tc, la, ra
      iframe Hc
      ipureintro; rfl
    · icases Hk with ⟨-, Hk⟩
      iintro Hend Hdir
      imod Hk $$ Hend Hdir with HQf
      imodintro
      unfold failV
      wp_auto
      wp_apply wp_anyTCPAddr as %x #Hx
      wp_apply wp_extAnyString as %nm
      wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
      · unfold edAt; itrivial
      (try wp_auto)
      wp_alloc pe as Hpe
      ipersist Hpe
      wp_auto
      iapply HΦ
      iright
      iframe HQf
      iexists x
      iframe Hx
      unfold resErr opErr
      iexists e
      iframe He
      iexists pe, nw
      iframe Hpe
      ipureintro; exact ⟨rfl, hnw⟩

end proof

end net
end Perennial
