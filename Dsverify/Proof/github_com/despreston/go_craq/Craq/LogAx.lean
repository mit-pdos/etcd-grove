/-
**Trust-boundary axioms** (dsv-fix6, mit-pdos/etcd-grove#49): `log.Default` and `*log.Logger`'s
`Printf`/`Println` on the operands go-craq logs (`argOk`, `Craq/LogHyp.lean`, whose header argues
what Go's `fmt` does with each). Until dsv-fix6 the statement premise `LogHyp` of
`craq_remote_robust`, with a wider operand condition the dsv-fix4 review refuted
(`notes/axiom-review/dsv-fix4/log-logger.md`); restated over the narrowed `argOk` and reviewed again:
`notes/axiom-review/dsv-fix6/log-logger-2.md`. Retirement: `*Logger`'s methods as Perennial-trusted
code beside its package-level `Printf`/`Println`, then translated over `fmt`'s model
(`notes/dsv-fix6.md`, craq).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions]
variable [github_com.despreston.go_craq.store.Assumptions]
variable [github_com.despreston.go_craq.transport.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.despreston.go_craq.LogDefault.wp_proof :
  github_com.despreston.go_craq.LogDefault.spec GF

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.despreston.go_craq.LoggerPrintf.wp_proof :
  github_com.despreston.go_craq.LoggerPrintf.spec GF

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.despreston.go_craq.LoggerPrintln.wp_proof :
  github_com.despreston.go_craq.LoggerPrintln.spec GF

/-- The class the proofs take, from the axioms. -/
theorem github_com.despreston.go_craq.logSpecs_holds :
    github_com.despreston.go_craq.LogSpecs GF :=
  ⟨github_com.despreston.go_craq.LogDefault.wp_proof,
   github_com.despreston.go_craq.LoggerPrintf.wp_proof,
   github_com.despreston.go_craq.LoggerPrintln.wp_proof⟩

end ax

end Perennial
