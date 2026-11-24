/-
Go's own `os.ignoringEINTR(fn)` (`file_posix.go`, translated since 2026-11-24, Go-model overlays S5:
`Mkdir` and `Remove` are Go's, over `syscall`'s models) and `os.fixLongPath` (the identity off
Windows). `ignoringEINTR` calls `fn` until it returns something other than `syscall.EINTR`.
`os.wp_ignoringEINTR`: for an `fn` that returns `errnoErr e` (what `syscall`'s models of
`Mkdir`, `Unlink` and `Rmdir` return), from a resource `I` it keeps on `EINTR`. Untrusted.
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `fixLongPath(p)`: `p` (`file_unix.go`'s, off Windows). -/
theorem os.wp_fixLongPath (p : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! os.fixLongPath)) (Val #p)) {{ RET #p; True }} := by
  wp_start as -
  try wp_auto
  iapply HΦ
  try itrivial

/-- What a call of `fn` gives `ignoringEINTR`: from `I`, `errnoErr e` with `I` again for `EINTR`
(`e = 4`), `Ψ e` otherwise. -/
def os.eintrCall (fn : GoFunc) (I : IProp GF) (Ψ : w64 → IProp GF) : IProp GF :=
  iprop(∀ Φ : val → IProp GF, I -∗
    (∀ e : w64, ((⌜e = W64 4⌝ ∗ I) ∨ (⌜e ≠ W64 4⌝ ∗ Ψ e)) -∗ Φ #(errnoErr e)) -∗
    WP (App (Val #fn) (Val #())) {{ Φ }})

/-- `ignoringEINTR(fn)` for an `fn` that returns `errnoErr e` (`os.eintrCall`): `I` before each
call, kept by a call returning `EINTR`; the first other result `e` ends it, with `Ψ e`. -/
theorem os.wp_ignoringEINTR (fn : GoFunc) (I : IProp GF) (Ψ : w64 → IProp GF) :
    {{ I ∗ □ os.eintrCall fn I Ψ }}
      (App (Val (@! os.ignoringEINTR)) (Val #fn))
    {{ (e : w64), RET #(errnoErr e); Ψ e }} := by
  wp_start as ⟨HI, #Hfn⟩
  try wp_auto
  wp_for
  wp_bind (App (Val #fn) (Val #()))
  iapply Hfn $$ HI
  iintro %e Hr
  icases Hr with (⟨%he, HI⟩ | ⟨%he, HΨ⟩)
  · subst he
    unfold errnoErr
    simp only [show ¬ (W64 4 = 0) by decide, ↓reduceIte]
    try wp_auto
    wp_for_post
    iframe
  · by_cases h0 : e = 0
    · subst h0
      unfold errnoErr
      simp only [↓reduceIte]
      try wp_auto
      wp_for_post
      iapply HΦ $$ HΨ
    · have h' : errnoErr e = (interface.mkOk syscall.Errno.ty #e : GoInterface) := by
        unfold errnoErr; rw [if_neg h0]
      rw [h']
      try wp_auto
      try rw [decide_eq_false (show ¬ (interface.mkOk syscall.Errno.ty #e =
        interface.mkOk syscall.Errno.ty #(W64 4)) by
          intro hc; injection hc with _ hv; exact he (go.intoVal_inj hv))]
      try wp_auto
      wp_for_post
      rw [← h']
      iapply HΦ $$ HΨ

end proof

end EtcdGrove
end Perennial
