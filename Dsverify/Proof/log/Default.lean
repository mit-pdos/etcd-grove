/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `log.Default()` returns a
non-`nil` `*Logger`. Perennial's trusted model of `log` leaves `Default` without a body (it reads
`std`, which the model does not allocate: `Perennial/Code/log.toml`). Go's `log.go`: `func Default()
*Logger { return std }`, and `std` is initialized at package initialization to `New(os.Stderr, "",
LstdFlags)`, a non-`nil` pointer never reassigned. The field `wp_Default` of craq's statement premise
`github_com.despreston.go_craq.LogHyp` until dsv-fix4 (`Dsverify/Proof/github_com/despreston/go_craq/
Craq/LogHyp.lean`). Review: `notes/axiom-review/dsv-fix4/log-logger.md`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [log.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom log.Default.wp_proof :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
      (App (Val (@! log.Default)) (Val #()))
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}

end ax

end Perennial
