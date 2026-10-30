/-
`fmt.Errorf` with string and `map[string]string` arguments (the DaemonSet lister's expansion's
errors: `fmt.Errorf("... %s in namespace %s with labels: %v", pod.Name, pod.Namespace,
pod.Labels)`). Lean-first.

As `tools/cache`'s `ErrorfSet.lean`: Perennial's `fmt.wp_Errorf` admits only arguments of
predeclared basic types (`fmt.ArgsWf`); its model of `Errorf` ignores the arguments, faithful when
Go's formatting calls none of their methods. A `map[string]string` (an unnamed map type of strings)
has no methods and neither do its keys and values, so `%v` prints it without calling one. The lemma
is proved from the model (no axiom); the premise on the arguments records that faithfulness claim
(`notes/perennial-changes.md`, `ArgWf` admitting maps whose types have no formatting methods).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(format, args...)` with string and `map[string]string` arguments**: a non-nil
error. -/
theorem wp_Errorf_labelArgs (format : GoString) (args_sl : GoSlice) (args : List GoInterface)
    (_hargs : ∀ a ∈ args, (∃ x : GoString, a = interface.mkOk go.string #x) ∨
      ∃ m : Loc, a = interface.mkOk (go.GoType.MapType go.string go.string) #m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); True }} := by
  wp_start as _
  wp_apply errors.wp_New as %err _
  iapply HΦ
  itrivial

end proof

end appslisters
end EtcdGrove
end Perennial
