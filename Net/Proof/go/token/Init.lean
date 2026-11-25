/-
The initializer of `go/token` (the part `Net/`'s translation, `Net/Code/go/token.toml`): its
`wp_initialize'`, proved. It allocates the package's variables, stores `tokens` (the array of the
tokens' names) and runs `init` (go1.27's: `keywords`, the map of the keyword tokens' names to their
tokens). Its fact is `True` (`Base.lean`): no proof reads these variables.
-/
module

public import Net.Proof.go.token.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go.token

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go.token.Assumptions]

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go.token get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go.token }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) keywords _ as Hkw
  wp_apply wp_GlobalAlloc (V := _) tokens _ as Htk
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (wp_map_make2 (K := GoString) (V := w64) _ go.string Token.ty) as %mref Hm
  try wp_auto
  ipersist Hkw
  ipersist Htk
  ihave #Hta : (∃ a : GoArray GoString 89, globalAddr tokens ↦□ a ∗ ⌜a.arr.length = 89⌝ :
      IProp GF) $$ []
  · iexists _
    iframe Htk
    ipureintro
    simp
  iclear Htk
  icases Hta with ⟨%a, #Hta, %Hal⟩
  ihave HI : (∃ (iv : w64) (m : GMap GoString w64), "i" ∷ i_ptr ↦ iv ∗ "Hm" ∷ mref ↦$ m ∗
      "%Hiv" ∷ ⌜61 ≤ uint.Z iv ∧ uint.Z iv ≤ 86⌝ : IProp GF) $$ [i Hm]
  · iexists _, _
    iframe
    ipureintro
    word
  wp_for HI
  by_cases hc : sint.Z iv < sint.Z (W64 86)
  · simp only [hc, decide_true, ↓reduceIte]
    have hk : (sint.Z iv).toNat < a.arr.length := by rw [Hal]; word
    icases array_acc (GF := GF) _ (sint.Z iv) _ _ _ (a.arr[(sint.Z iv).toNat]'hk) (by word)
      (List.getElem?_eq_getElem hk) $$ Hta with ⟨#Hx, -⟩
    try wp_auto
    rw [ite_eq_left (by word)]
    try wp_auto
    wp_apply (wp_mapInsert go.string mref m _ iv) $$ Hm as Hm
    try wp_auto
    wp_for_post
    iframe
    iexists iv + W64 1, _
    iframe
    ipureintro
    have : sint.Z (W64 86) = 86 := by word
    word
  · simp only [hc, decide_false, ↓reduceIte, Bool.false_eq_true]
    try wp_auto
    iframe Hown
    is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go.token get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go.token }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)

end init

end go.token

end Perennial
