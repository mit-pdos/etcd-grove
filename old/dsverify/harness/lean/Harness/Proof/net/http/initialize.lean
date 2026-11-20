/-
The proof of `Spec/net/http/initialize.lean`.
-/
module

public import Harness.Spec.net.http.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.http.Assumptions]

set_option goose.wp.extras true in
theorem net.http.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_net_initialize : net.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_bufio_initialize : bufio.initialize'.spec (GF := GF) (hG := hG)) :
    net.http.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) net.http.errHead go.error as HE
  wp_apply wp_GlobalAlloc (V := Loc) net.http.DefaultServeMux
    (go.GoType.PointerType net.http.ServeMux.ty) as HM
  wp_apply wp_GlobalAlloc (V := GoInterface) net.http.errStatus go.error as HS
  wp_apply wp_sync_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_net_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hnet⟩
  wp_apply wp_errors_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_bufio_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hbufio⟩
  wp_apply errors.wp_New_errorString as %xs #ES
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string net.http.Handler.ty)
    as %mp Hmp
  irename «$r0» => Hs
  generalize «$r0_ptr» = mux at *
  iStructNamed Hs
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %x #EH
  ipersist HM
  ipersist HE
  ipersist HS
  ipersist m
  imod ghost_map_alloc_empty (K := GoString) (V := GoInterface) with ⟨%γr, Hr⟩
  imod ghostVar_alloc ([] : List GoString) with ⟨%γo, Ho⟩
  ihave ⟨Ho1, Ho2⟩ := ghostVar_split_half γo 1 ([] : List GoString) $$ Ho
  imod sync.init_Mutex (net.http.muxInv mp (γr, γo)) ⊤
      (structFieldRef net.http.ServeMux go!"mu" mux) $$ [mu] [Hmp Hr Ho1] with #Hmu
  · iexact mu
  · inext; unfold net.http.muxInv; iexists ∅, []
    iframe Hmp Hr Ho1
    ipureintro; intro p; simp
  imod inv_alloc net.http.muxN ⊤ (net.http.ownerInv (γr, γo)) $$ [Ho2] with #Hinv
  · inext; unfold net.http.ownerInv; ileft; iexact Ho2
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  unfold net.http.isInit errors.newVar
  isplitl
  · iexists x
    iframe HE EH
  isplitl
  · iexists xs
    iframe HS ES
  isplitl
  · iexists mux, mp, (γr, γo)
    unfold net.http.defaultMux net.http.isMux
    iframe HM m Hmu Hinv
  itrivial

end proof

end Perennial
