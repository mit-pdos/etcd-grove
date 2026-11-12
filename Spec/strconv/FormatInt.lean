/-
`strconv.FormatInt`: the trust boundary (Perennial translates `strconv` names-only; the axiom is
`Proof/strconv/FormatInt.lean`). Lean-first (no Rocq counterpart); K2 of
`notes/k8s-compactor-plan.md`, U2 (the user's approval, 2026-11-04): the Kubernetes compactor writes
`FormatInt(rev, 10)` to `compact_rev_key`.
-/
module

public import Perennial.Proof.strconv.Base
public import Proof.strconv.FormatIntDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strconv.FormatInt(i, base)` of a base in `2..36`: `fmtInt i base`, the digits of `i` with a
leading `-` when negative. (Go panics on any other base, `internal/strconv/itoa.go`: the premise, as
`FormatUint`'s.) -/
abbrev strconv.FormatInt.spec : Prop :=
  ∀ (i : w64) (base : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ ⌜2 ≤ sint.Z base ∧ sint.Z base ≤ 36⌝ }}
    (App (App (Val (@! _root_.Perennial.strconv.FormatInt)) (Val #i)) (Val #base))
  {{ (str : GoString), RET #str; ⌜str = fmtInt i base⌝ }}

end spec

end EtcdGrove
end Perennial
