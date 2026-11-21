/-
`fmt.Errorf` with string and `map[string]string` arguments (the DaemonSet lister's expansion's
errors: `fmt.Errorf("... %s in namespace %s with labels: %v", pod.Name, pod.Namespace,
pod.Labels)`): a trust-boundary axiom since fmtmodel (2026-11-20). Lean-first.

Until then a lemma proved over Perennial's previous model of `Errorf` (`errors.New(format)`, which ignored
the arguments), its statement taking no ownership of the maps: false of Go, which reads a map it formats
and dies with the runtime's fatal `concurrent map read and map write` on a concurrent write (as
`tools/cache`'s `ErrorfSet.lean`, `notes/axiom-review/errorf-setargs.md`). Perennial's model of `fmt`
now calls what Go calls and is stuck on reflection into a map, so the statement is an axiom, with a
fraction of each map's points-to in its premise, given back.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
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
error (trust boundary; see the file header). Go (go1.27.3): a `string` is printed by its kind; a
`map[string]string` has no methods, so `printArg` (`fmt/print.go:674`) finds none (`handleMethods`,
line 614) and `printValue` prints the map (line 793: `fmtsort.Sort` reads its entries, strings printed
by kind), reading the map, of which the caller lends a fraction; under another verb the same with
`%!verb(...)` around it, and `%p` prints its address. `Errorf` (`fmt/errors.go:23-95`) returns a non-nil
error. -/
axiom wp_Errorf_labelArgs (format : GoString) (args_sl : GoSlice) (args : List GoInterface)
    (_hargs : ∀ a ∈ args, (∃ x : GoString, a = interface.mkOk go.string #x) ∨
      ∃ m : Loc, a = interface.mkOk (go.GoType.MapType go.string go.string) #m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗
        [∗list] a ∈ args, ⌜∃ x : GoString, a = interface.mkOk go.string #x⌝ ∨
          ∃ (m : Loc) (dq : DFrac) (st : GMap GoString GoString),
            ⌜a = interface.mkOk (go.GoType.MapType go.string go.string) #m⌝ ∗ m ↦${dq} st }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        [∗list] a ∈ args, ⌜∃ x : GoString, a = interface.mkOk go.string #x⌝ ∨
          ∃ (m : Loc) (dq : DFrac) (st : GMap GoString GoString),
            ⌜a = interface.mkOk (go.GoType.MapType go.string go.string) #m⌝ ∗ m ↦${dq} st }}

end proof

end appslisters
end EtcdGrove
end Perennial
