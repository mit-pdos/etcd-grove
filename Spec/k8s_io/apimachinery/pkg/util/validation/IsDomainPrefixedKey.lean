/-
`validation.IsDomainPrefixedKey(fldPath, key)` (apimachinery, names only): **the trust boundary**.
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace validation

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev IsDomainPrefixedKey.spec : Prop :=
  ∀ (fp : Loc) (key : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.IsDomainPrefixedKey))
      (Val #fp)) (Val #key))
  {{ (s : GoSlice), RET #s; ∃ errs : List Loc, s ↦* errs }}

end spec

end validation
end EtcdGrove
end Perennial
