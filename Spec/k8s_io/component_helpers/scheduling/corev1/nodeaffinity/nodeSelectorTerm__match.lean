/-
`(*nodeSelectorTerm).match(nodeLabels, nodeFields)` (`nodeaffinity.go:190`): `(false, t.parseErrs)`
for a term with parse errors, else whether its selectors match (some `bool`: the selectors are
opaque) and no error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

/-- **`t.match(lm, fm)`** on a parsed term (`termOk`) and two maps (read, possibly `nil`): with
parse errors, `(false, t.parseErrs)`; without, some `bool` and a `nil` error slice. -/
abbrev nodeSelectorTerm.match.spec : Prop :=
  ∀ (t : Loc) (tv : nodeSelectorTerm) (lm : Loc) (dql : DFrac)
    (oL : Option (GMap GoString GoString)) (fm : Loc) (dqf : DFrac)
    (oF : Option (GMap GoString GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity ∗
      t ↦ tv ∗ termOk tv ∗ ownMapD lm dql oL ∗ ownMapD fm dqf oF }}
    (App (App (Val (t @!! go.GoType.PointerType nodeSelectorTerm.ty @!! go!"match")) (Val #lm))
      (Val #fm))
  {{ (b : Bool) (es : GoSlice), RET (PairV #b #es); t ↦ tv ∗ ownMapD lm dql oL ∗ ownMapD fm dqf oF ∗
      ⌜(tv.parseErrs' ≠ slice.nil → b = false ∧ es = tv.parseErrs') ∧
        (tv.parseErrs' = slice.nil → es = slice.nil)⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
