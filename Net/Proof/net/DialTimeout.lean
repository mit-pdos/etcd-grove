/-
The proof of `Net/Spec/net/DialTimeout.lean`: `DialTimeout.impl`'s extension `Dial`
(`Net.wp_net_Dial`), then a new `*TCPConn` holding the dialer's end, or the failure's error: an
`*os.SyscallError`, `errTimeout`'s value or `poll.ErrDeadlineExceeded`'s, by the model's choices
(`AnyBool`).
-/
module

public import Net.Spec.net.DialTimeout
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

set_option hygiene false in
/-- The rest of a failure, once its `Err` `e` is made (`He`: what it is). -/
local macro "dt_tail" : tactic => `(tactic| (
    (try wp_auto)
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    wp_apply wp_opError $$ %hnw as %err #Herr
    (try wp_auto)
    iapply HΦ
    iright
    iframe HQ
    iexists x, _
    iframe Hx Herr He))

set_option hygiene false in
/-- A failure (after the extension's `Dial`): the model's choice of its `Err`. -/
local macro "dt_fail" : tactic => `(tactic| (
    rw [Conn_ty_eq]
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_net_AnyBool
    iintro %b1
    cases b1
    · wp_auto
      wp_bind (ExternalOp _ _ _)
      iapply wp_net_AnyBool
      iintro %b2
      cases b2
      · wp_auto
        unfold model.deadlineErr
        wp_auto
        ihave #He : iprop(sysErr (GF := GF) (fun _ => True) ed ∨ ⌜ed = et ∨ ed = ed⌝) $$ []
        · iright; ipureintro; exact .inr rfl
        dt_tail
      · unfold errTimeout at *
        wp_auto
        ihave #He : iprop(sysErr (GF := GF) (fun _ => True) et ∨ ⌜et = et ∨ et = ed⌝) $$ []
        · iright; ipureintro; exact .inl rfl
        dt_tail
    · wp_auto
      wp_bind (ExternalOp _ _ _)
      iapply wp_net_AnyString
      iintro %nm
      wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He0
      simp only [kindErr]
      ihave #He : iprop(sysErr (GF := GF) (fun _ => True) e ∨ ⌜e = et ∨ e = ed⌝) $$ [He0]
      · ileft; iexact He0
      dt_tail))

theorem DialTimeout.wp_proof : DialTimeout.spec (GF := GF) (hG := hG) := by
  intro nw hnw a dur et ed Qfail Qok
  wp_start as ⟨%Hla, #Het, #Hed, HAU⟩
  wp_auto
  wp_apply wp_netOk nw hnw
  (try wp_auto)
  wp_apply wp_extDial a $$ %Hla
  isplit
  · icases HAU with ⟨HQf, -⟩
    unfold failV
    wp_auto
    wp_apply wp_extAnyBool as %b1
    cases b1
    · wp_auto
      wp_apply wp_extAnyBool as %b2
      cases b2
      · wp_auto
        wp_apply wp_anyTCPAddr as %x #Hx
        (try wp_auto)
        wp_alloc pe as Hpe
        ipersist Hpe
        wp_auto
        iapply HΦ
        iright
        iframe HQf
        iexists x, ed
        iframe Hx
        isplitl
        · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
        · iright; ipureintro; exact .inr rfl
      · wp_auto
        wp_apply wp_anyTCPAddr as %x #Hx
        (try wp_auto)
        wp_alloc pe as Hpe
        ipersist Hpe
        wp_auto
        iapply HΦ
        iright
        iframe HQf
        iexists x, et
        iframe Hx
        isplitl
        · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
        · iright; ipureintro; exact .inl rfl
    · wp_auto
      wp_apply wp_extAnyString as %nm
      wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
      · unfold edAt; itrivial
      (try wp_auto)
      wp_apply wp_anyTCPAddr as %x #Hx
      (try wp_auto)
      wp_alloc pe as Hpe
      ipersist Hpe
      wp_auto
      iapply HΦ
      iright
      iframe HQf
      iexists x, e
      iframe Hx
      isplitl
      · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
      · ileft; unfold kindErr; dsimp only; iexact He
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
      wp_apply wp_extAnyBool as %b1
      cases b1
      · wp_auto
        wp_apply wp_extAnyBool as %b2
        cases b2
        · wp_auto
          wp_apply wp_anyTCPAddr as %x #Hx
          (try wp_auto)
          wp_alloc pe as Hpe
          ipersist Hpe
          wp_auto
          iapply HΦ
          iright
          iframe HQf
          iexists x, ed
          iframe Hx
          isplitl
          · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
          · iright; ipureintro; exact .inr rfl
        · wp_auto
          wp_apply wp_anyTCPAddr as %x #Hx
          (try wp_auto)
          wp_alloc pe as Hpe
          ipersist Hpe
          wp_auto
          iapply HΦ
          iright
          iframe HQf
          iexists x, et
          iframe Hx
          isplitl
          · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
          · iright; ipureintro; exact .inl rfl
      · wp_auto
        wp_apply wp_extAnyString as %nm
        wp_apply wp_kindErr (c := NetErr.sys.code) .sys none nm (fun _ => True) trivial rfl $$ [] as %e #He
        · unfold edAt; itrivial
        (try wp_auto)
        wp_apply wp_anyTCPAddr as %x #Hx
        (try wp_auto)
        wp_alloc pe as Hpe
        ipersist Hpe
        wp_auto
        iapply HΦ
        iright
        iframe HQf
        iexists x, e
        iframe Hx
        isplitl
        · unfold opErr; iexists pe, nw; iframe Hpe; ipureintro; exact ⟨rfl, hnw⟩
        · ileft; unfold kindErr; dsimp only; iexact He

end proof

end net
end Perennial
