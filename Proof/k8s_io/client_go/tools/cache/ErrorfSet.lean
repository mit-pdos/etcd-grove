/-
`fmt.Errorf` with a `sets.Set[string]` argument (`storeIndex.addIndexers`' conflict error,
`fmt.Errorf("indexer conflict: %v", oldKeys.Intersection(newKeys))`). Lean-first.

Perennial's `fmt.wp_Errorf` admits only arguments of predeclared basic types (`fmt.ArgsWf`): its
model of `Errorf` ignores the arguments, which is faithful only when Go's formatting calls none of
their methods. A `sets.Set[string]` argument is such a case: its dynamic type is the named map type
`Set[string]`, whose method set (`Insert`, `Delete`, `Has`, ..., `Len`; `set.go`) has no `Error`,
`String`, `Format` or `GoString`, and whose keys (`string`) and values (`sets.Empty`, an empty
struct with no methods) have none either, so `%v` prints the map without calling a method. The
lemma is proved from the model as Perennial proves `wp_Errorf` (no axiom); the premise on the
arguments records that faithfulness claim. The general fix is a Perennial change: `ArgWf`
admitting maps (and structs) whose types have no formatting methods (`notes/perennial-changes.md`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(format, args...)` with `sets.Set[string]` arguments**: a non-nil error. -/
theorem wp_Errorf_setArgs (format : GoString) (args_sl : GoSlice) (args : List GoInterface)
    (_hargs : ∀ a ∈ args, ∃ m : Loc,
      a = interface.mkOk (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string) #m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); True }} := by
  wp_start as _
  wp_apply errors.wp_New as %err _
  iapply HΦ
  itrivial

end proof

end cache
end EtcdGrove
end Perennial
