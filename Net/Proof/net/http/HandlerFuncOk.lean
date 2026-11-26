/-
A function `f` that serves the requests under `pfx` with the protocol `P` makes `HandlerFunc(f)` a
handler of them (`handlerOk`), by `HandlerFunc.ServeHTTP`'s spec. Lean-first.
-/
module

public import Net.Spec.net.http.HandlerFunc__ServeHTTP
public import Net.Proof.net.http.ProtoDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemma
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
theorem handlerOk_func (wp_SH : HandlerFunc.ServeHTTP.spec (GF := GF) (hG := hG))
    (f : GoFunc) (P : HProto GF) (pfx : GoString) :
    (□ ∀ (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface)
        (I : RespSt → IProp GF) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF),
      ⌜∀ x, S x ⊢ ⌜x.length < 2 ^ 60⌝⌝ -∗ servePre P pfx w r R τ rd I S E -∗
      WP (App (App (Val #f) (Val #w)) (Val #r))
        {{ v, ⌜v = #() ∨ v.isPanic = true⌝ ∗ serveDone P R τ I S v }}) ⊢
    handlerOk (interface.mkOk net.http.HandlerFunc.ty #f) P pfx := by
  iintro #H
  iunfold handlerOk
  iexists ⟨net.http.HandlerFunc.ty, #f⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %w %r %R %τ %rd %I %S %E %HS Hpre
  iapply (wp_SH f w r (fun v => serveDone P R τ I S v))
  iapply H
  · ipureintro; exact HS
  · iexact Hpre

end lemma

end net.http
end Perennial
