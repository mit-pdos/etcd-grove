/-
`fmt.Errorf` with a `sets.Set[string]` argument (`storeIndex.addIndexers`' conflict error,
`fmt.Errorf("indexer conflict: %v", oldKeys.Intersection(newKeys))`): a trust-boundary axiom since
fmtmodel (2026-11-20). Lean-first.

Until then a lemma proved over Perennial's previous model of `Errorf` (`errors.New(format)`, which ignored
the arguments), its statement taking no ownership of the map: false of Go, which reads the map
(`printValue`'s `reflect.Map` case, `fmt/print.go:793-815`, `fmtsort.Sort` iterating it) and dies with
the runtime's fatal `concurrent map read and map write` (`internal/runtime/maps/map.go:432`) if another
goroutine writes it meanwhile (`notes/axiom-review/errorf-setargs.md`). Perennial's model of `fmt` now
calls what Go calls and is stuck on reflection into a map, so the statement is an axiom, with a fraction
of each map's points-to in its premise, given back.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs
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

/-- **`fmt.Errorf(format, args...)` with `sets.Set[string]` arguments**: a non-nil error (trust
boundary; see the file header). Go (go1.27.3): a `Set[string]`'s method set (`Insert`, `Delete`, `Has`,
..., `Len`; apimachinery's `sets/set.go`) has no `Error`, `String`, `Format` or `GoString`, so
`printArg` (`fmt/print.go:674`) finds no method (`handleMethods`, line 614) and `printValue` prints the
map (line 793: `fmtsort.Sort` reads its entries, each key a `string` and each value a `sets.Empty`, an
empty struct without methods, printed by kind), reading the map, of which the caller lends a fraction;
under a verb other than the method verbs it prints the map the same way (`%!d(...)` around it), and
`%p` prints its address. `Errorf` (`fmt/errors.go:23-95`) returns a non-nil error. The argument slice is
only read (the post forgets it, as the statement did). -/
axiom wp_Errorf_setArgs (format : GoString) (args_sl : GoSlice) (args : List GoInterface)
    (_hargs : ∀ a ∈ args, ∃ m : Loc,
      a = interface.mkOk (k8s_io.apimachinery.pkg.util.sets.Set''.ty go.string) #m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗
        [∗list] a ∈ args, ∃ (m : Loc) (dq : DFrac) (st : GMap GoString sets.Elem),
          ⌜a = interface.mkOk (k8s_io.apimachinery.pkg.util.sets.Set''.ty go.string) #m⌝ ∗ m ↦${dq} st }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        [∗list] a ∈ args, ∃ (m : Loc) (dq : DFrac) (st : GMap GoString sets.Elem),
          ⌜a = interface.mkOk (k8s_io.apimachinery.pkg.util.sets.Set''.ty go.string) #m⌝ ∗ m ↦${dq} st }}

end proof

end cache
end EtcdGrove
end Perennial
