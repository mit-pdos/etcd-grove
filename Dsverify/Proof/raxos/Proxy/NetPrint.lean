/-
Package `proxy`: `fmt.Println` of a string and an error (`waitForConnections`'s
`fmt.Println("TCP accept error:", err)`), over the hypothesis `hyp.fmt.Println.spec`
(`Hyp.lean`; the lab proved its `wp_Println_ok` over its own model of `fmt`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open hyp.fmt (printOk)

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Println(a...)` for operands `printOk` allows (the hypothesis, with `fmt`'s `isPkgInit`). -/
theorem wp_Println_ok [hp : hyp.PrintlnHyp GF] (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ □ ([∗list] x ∈ xs, printOk x) ∗ arg ↦*{dq} xs :
        IProp GF) }}
      (App (Val (@! fmt.Println)) (Val #arg))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); arg ↦*{dq} xs }} :=
  hp.Println arg xs dq

/-- The two operands of `fmt.Println("...", err)`. -/
theorem printOk_str_err (s : GoString) (err : GoInterface) :
    ⌜∀ ii, err = interface.ok ii → go.typeSetContains ii.ty fmt.Formatter.ty = false⌝ ∗
      models_lab.errAny (GF := GF) err ⊢
      □ ([∗list] x ∈ [interface.mkOk go.string #s, err], printOk x) := by
  iintro ⟨%Hnf, #He⟩
  imodintro
  isplitr
  · iunfold printOk; ileft; ipureintro
    intro ii hii
    exact fmt.ArgsWf.cons_string s [] fmt.ArgsWf.nil ii (by rw [hii]; simp)
  isplitl
  · iunfold printOk; iright; iframe He; ipureintro; exact Hnf
  iempintro

end proofs

end Perennial.raxos
