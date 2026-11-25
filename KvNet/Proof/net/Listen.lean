-- The copy for the part `KvNet/` of `Net/Proof/net/Listen.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/Listen.lean`: `Listen.impl`'s extension `Listen`
(`Net.wp_net_Listen`), then a new `*TCPListener` holding the listener's id, as a `Listener`.
-/
module

public import KvNet.Spec.net.Listen
public import KvNet.Proof.net.OpErrorMsg

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

theorem Listen.wp_proof : Listen.spec (GF := GF) (hG := hG) := by
  intro nw hnw a
  wp_start as ⟨%Hla, Htok⟩
  wp_auto
  wp_apply wp_netOk nw hnw
  (try wp_auto)
  wp_apply wp_extListen a $$ %Hla Htok
  isplit
  · -- a failure
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
    iexists x
    iframe Hx
    iapply resErr_intro hnw
      (by first | exact edTyped_none | (intro x h; cases h; exact ⟨_, rfl⟩)) $$ Hpe He
    all_goals first | iapply addrOrNil_nil | (iapply addrOrNil_addr; iassumption)
  · -- a new listener
    iintro %lid %hl0 Hl #Hlat
    wp_auto
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    wp_apply wp_modelFD $$ Hpkg as %fd #Hfd
    (try wp_auto)
    wp_alloc tl as Htl
    ipersist Htl
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists lid
    iframe Hl Hlat
    unfold isListener lisAt lisFd
    iexists tl, x
    isplitr
    · ipureintro; rfl
    iexists nw
    iframe Hx
    isplitr
    · ipureintro; exact hnw
    isplitl
    · iexists fd, _, _
      iframe Htl Hfd
    · ipureintro; exact hl0

end proof

end net
end Perennial
