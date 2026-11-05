/-
`strconv.Itoa`: the trust boundary (Perennial translates `strconv` names-only; the axiom is
`Proof/strconv/Itoa.lean`). Lean-first (no Rocq counterpart); K4 of `notes/k8s-compactor-plan.md`:
the compactor example's writer puts `Itoa(i)`. Go's `Itoa(i)` is `FormatInt(int64(i), 10)`
(`strconv/itoa.go`), so its spec is `FormatInt.spec`'s at base 10.
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

/-- `strconv.Itoa(i)`: `fmtInt i 10`, `FormatInt(int64(i), 10)` (an `int` is 64 bits here). -/
abbrev strconv.Itoa.spec : Prop :=
  ∀ (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (Val (@! _root_.Perennial.strconv.Itoa)) (Val #i))
  {{ (str : GoString), RET #str; ⌜str = fmtInt i (W64 10)⌝ }}

end spec

end EtcdGrove
end Perennial
