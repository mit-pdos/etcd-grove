/-
`maps.Keys(m)` on a `map[string]runtime.Object`, as the checker uses it:
`slices.Sorted(maps.Keys(s.Items))` (`Model.list`, `Model.listItems`). `Keys` returns an iterator
`f`, and `slices.Sorted(f)` (names-only too) returns a fresh slice of the map's keys at the time of
the `Sorted` call, each once, strictly increasing in Go's string order (`go.GoStringLt`, bytewise).
One spec for the pair, at this one map type (`spec_objMap`): the iterator is used only by
`Sorted`, and what it yields depends on the map when it runs, not when `Keys` returns. Its axiom
is `maps.Keys.wp_proof_objMap` (k8s 7g, `notes/k8s-7g-trust.md`), until Perennial has iterator
specs: it translates `maps.Keys` (since `70706ce5e`) but `slices.Sorted` names only
(`notes/perennial-changes.md`, "Generic maps and slices iterators").

Faithful (go1.27.3, `maps/iter.go`, `slices/iter.go`, `slices/sort.go`): `Keys(m)` is
`func(yield func(K) bool) { for k := range m { if !yield(k) { return } } }`: it reads nothing when
called and allocates only the closure, so it never panics and returns a non-nil func value (the
post's `f : GoFunc`, a typed value and so never a panic value; changed in place from `(f : val)`,
which no caller could use, k8s 7g step 3 STOP 2a, decided by etcd-grove-03); every run of the closure ranges over `m` as it is then.
`Sorted(seq)` is `s := Collect(seq); Sort(s); return s`; `Collect` is `AppendSeq([]E(nil), seq)`,
whose yield always returns true, so a range over the unmodified map appends each key once (the
order is unspecified and does not matter after the sort); `Sort` on `[]string` sorts by `cmp.Less`,
`<` on strings, which is bytewise lexicographic (`go.GoStringLt` compares bytes by `uint.Z`). The
keys are distinct, so the result is strictly increasing and is the only such list. For an empty
map the result is the nil slice, which `s ↦* []` holds of. The map is only read (fraction `dq`
back). The heapsort fallback's index overflow needs `2^62` elements, which no map in memory has.
Go evidence: `examples/k8s/etcd3/trustspecs_test.go` `TestMapsKeysSorted` (5000 random maps with
non-ASCII and invalid UTF-8 keys: each key once, strictly increasing by Go's `<`; an empty map gives
nil; a key added after `Keys` and before `Sorted` is listed; a second `Sorted` of the same iterator
re-reads the map), `TestMapsKeysNoPanic` (`Keys` of a nil, an empty and a non-empty map returns
without panicking, and the func is non-nil). Lean-first.
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
        isPkgInit pkg_id.slices -∗ m ↦${dq} M -∗
        ▷ (∀ (s : GoSlice) (ks : List GoString),
            m ↦${dq} M -∗ s ↦* ks -∗
            ⌜(∀ k, k ∈ ks ↔ (M !! k).isSome) ∧ ks.Pairwise go.GoStringLt⌝ -∗ Φ #s) -∗
        WP (App (Val #(functions _root_.Perennial.slices.Sorted [go.string])) (Val #f)) {{ Φ }} }}

end spec

end EtcdGrove
end Perennial
