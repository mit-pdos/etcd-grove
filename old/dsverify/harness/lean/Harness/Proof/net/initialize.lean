/-
The proof of `Spec/net/initialize.lean`: the trusted initializers that do nothing, `ErrClosed`'s
(two global allocations and stores), and the initializers of `time` and `io`.
-/
module

public import Harness.Spec.net.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.initialize'.wp_proof
    (wp_time_initialize : time.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG)) :
    net.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_time_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Htime⟩
  repeat (first | wp_call | wp_auto)
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) net.errNetClosing go.error as Hnc
  wp_apply net.wp_connErr as %x Hx
  wp_apply wp_GlobalAlloc (V := GoInterface) (go!"net.ErrClosed") go.error as HE
  repeat (first | wp_call | wp_auto)
  ipersist Hnc
  ipersist Hx
  ipersist HE
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  iexists x
  iframe Hnc Hx
  unfold net.ErrClosed
  iexact HE

end proof

end Perennial
