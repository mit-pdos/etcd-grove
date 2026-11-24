/-
`maps.Keys(m)` on a `map[string]runtime.Object`, as the checker uses it:
`slices.Sorted(maps.Keys(s.Items))` (`Model.list`, `Model.listItems`). `Keys` returns an iterator
`f`, and `slices.Sorted(f)` returns a fresh slice of the map's keys at the time of the `Sorted`
call, each once, strictly increasing in Go's string order (`go.GoStringLt`, bytewise), for a map of
at most `2^62` keys (`slices.Sort`'s heapsort index arithmetic overflows past that). One spec for
the pair, at this one map type (`spec_objMap`): the iterator is used only by `Sorted`, and what it
yields depends on the map when it runs, not when `Keys` returns. Proved
(`maps.Keys.wp_proof_objMap`) from Perennial's `maps.wp_Sorted_Keys_string`
(`Perennial/Proof/maps/Results.lean`); until 2026-11-23 an axiom (k8s 7g, `notes/k8s-7g-trust.md`),
without the size premise (ledger, 2026-11-23, "`maps.Keys.spec_objMap`").

`Keys(m)` reads nothing when called and allocates only the closure, so it never panics and returns
a non-nil func value (the post's `f : GoFunc`); every run of the closure ranges over `m` as it is
then. `Sorted(seq)` is `s := Collect(seq); Sort(s); return s`. For an empty map the result is the
nil slice, which `s ↦* []` holds of. The map is only read (fraction `dq` back). Go evidence of
the shape: `examples/k8s/etcd3/trustspecs_test.go` `TestMapsKeysSorted`, `TestMapsKeysNoPanic`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Base
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev maps.Keys.spec_objMap : Prop :=
  ∀ (m : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.maps }}
    (App (Val #(functions _root_.Perennial.maps.Keys
      [go.GoType.MapType go.string k8s_io.apimachinery.pkg.runtime.Object.ty, go.string,
        k8s_io.apimachinery.pkg.runtime.Object.ty])) (Val #m))
  {{ (f : GoFunc), RET #f;
      □ ∀ (M : GMap GoString GoInterface) (dq : DFrac) (Φ : val → IProp GF),
        isPkgInit pkg_id.slices -∗ m ↦${dq} M -∗ ⌜GMap.size M ≤ 2 ^ 62⌝ -∗
        ▷ (∀ (s : GoSlice) (ks : List GoString),
            m ↦${dq} M -∗ s ↦* ks -∗
            ⌜(∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Pairwise go.GoStringLt⌝ -∗ Φ #s) -∗
        WP (App (Val #(functions _root_.Perennial.slices.Sorted [go.string])) (Val #f)) {{ Φ }} }}

end spec

end EtcdGrove
end Perennial
