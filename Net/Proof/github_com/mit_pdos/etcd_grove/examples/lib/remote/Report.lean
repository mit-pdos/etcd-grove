/-
The proof of `Report` (`Net/Spec/.../lib/remote/Report.lean`): `EncIn` (a request longer than
`maxLen` goes to `hang`), one `attempt` with the caller's update, and, on an answer, `DecOut` of its
bytes, the far side's answer's: an output `o`'s, whose decoding describes `o` (`wireOk`), or an
answer `v` that is not one, whose decoding is `v`; with what `attempt` gave of it.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Report
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.hang

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

theorem Report.wp_proof (wp_attempt : attempt.spec (GF := GF) (hG := hG) (I := I) (O := O))
    (wp_hang : hang.spec (GF := GF) (hG := hG)) :
    Report.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S a x i Φo cd d
  wp_start as ⟨#Hm, #Ha, #Hcd, #Hx, HL, Hu⟩
  iunfold wireOk at Hcd
  icases Hcd with ⟨#HEncIn, -, -, #HDecOut, -, #HDecUnk⟩
  wp_auto
  wp_apply HEncIn $$ %x %i Hx as %req Hreq
  ihave %Hrl := ownSlice_len $$ Hreq
  wp_if_destruct
  · wp_apply wp_hang as HF
    iexfalso
    iexact HF
  have Hlen : (S.encIn i).length ≤ maxLen := by
    have h1 := Hrl.1
    have : sint.nat req.len = uint.nat req.len := by word
    simp only [maxLen]; word
  wp_apply wp_attempt S a i Φo req (DFrac.own 1) d Hlen $$ [Hreq HL Hu] as %rep %ok ⟨-, Hres⟩
  · iframe Hm Ha Hreq HL Hu
  icases Hres with (%Hf | ⟨%Hok, Hv⟩)
  · subst Hf
    wp_auto
    iapply HΦ
    ileft
    itrivial
  subst Hok
  wp_auto
  icases Hv with (⟨%o, Hrep, HΦo⟩ | ⟨%v, Hrep, %Hu⟩)
  · wp_apply HDecOut $$ %o %rep %(DFrac.own 1) [Hrep] as %y %good Hy
    · iexact Hrep
    iapply HΦ
    cases good
    · ileft
      itrivial
    · ispecialize Hy $$ %rfl
      iright
      isplitr
      · ipureintro; rfl
      ileft
      iexists o
      iframe Hy HΦo
  · wp_apply HDecUnk $$ %i %v %rep %(DFrac.own 1) %Hu [Hrep] as %y %good %Hy
    · iexact Hrep
    iapply HΦ
    cases good
    · ileft
      itrivial
    · obtain rfl := Hy rfl
      iright
      isplitr
      · ipureintro; rfl
      iright
      ipureintro; exact Hu

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
