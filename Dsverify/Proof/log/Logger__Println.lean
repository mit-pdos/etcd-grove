/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `l.Println(args...)` on a
non-`nil` `*Logger`, with arguments `argOk` allows (`Logger__Printf.lean`'s header), returns and
gives the argument slice back. Perennial's trusted model of `log` does not translate `*Logger`'s
methods. Go's `log.go`: `Println` is `Printf`'s path with `fmt.Appendln(b, v...)` (operands in their
default formats: `fmt` calls `Error()` of an error operand and no other method of `argOk`'s values);
a nil `l` panics (excluded). The field `wp_Logger_Println` of craq's statement premise `LogHyp` until
dsv-fix4. Review: `notes/axiom-review/dsv-fix4/log-logger.md`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.despreston.go_craq (argOk)

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [log.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom log.Logger.Println.wp_proof : ∀ (l : Loc) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac), l ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end ax

end Perennial
