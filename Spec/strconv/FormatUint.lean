/-
`strconv.FormatUint`: the trust boundary (Perennial translates `strconv` names-only). Lean-first
(no Rocq counterpart); the request path's unit 4a (the read loop's trace field).
-/
module

public import Perennial.Proof.strconv.Base
public import Proof.strconv.FormatUintDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strconv.FormatUint(i, base)` of a base in `2..36`: the digits of `i` (`fmtUint`, since
2026-10-27 for the model API server's resource versions, `examples/k8sdaemonset/apimodel`; until
then some string: the read loop's trace field, which the model does not read). (Go panics on any
other base, `internal/strconv/itoa.go`; the premise since audit B4b, 2026-10-18.) -/
abbrev strconv.FormatUint.spec : Prop :=
  ∀ (i : w64) (base : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ ⌜2 ≤ sint.Z base ∧ sint.Z base ≤ 36⌝ }}
    (App (App (Val (@! _root_.Perennial.strconv.FormatUint)) (Val #i)) (Val #base))
  {{ (str : GoString), RET #str; ⌜str = fmtUint i base⌝ }}

end spec

end EtcdGrove
end Perennial
