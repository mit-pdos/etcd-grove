/-
`cmp.Diff(x, y)` (go-cmp v0.7.0, `cmp/compare.go`; names-only here) with no options, on two
`[]eventReference` (the checker's `compareEvents`, `watch.go`): `""` exactly when both slices are
nil or both non-nil, and equal element by element. Stated at this type only (`spec_eventRefs`); its
other calls in the checker (`Replay.validateList`'s and `compareEvents`' error messages) are on
paths the proofs show unreachable. Its axiom will be `cmp.Diff.wp_proof_eventRefs` (k8s 7g,
`notes/k8s-7g-trust.md`).

Faithful: `Diff` runs `compareAny` and returns `""` if the result is equal; otherwise it builds the
report and panics if the report is `""` (`(d == "") != s.result.Equal()`), so `""` iff `Equal`
(also its documentation: "It returns an empty string if and only if Equal returns true"). `Equal`
with no options: neither `eventReference` nor `watch.EventType` has an `Equal` method (which it
would call instead); slices are equal iff both nil or both non-nil ("Empty non-nil slices and nil
slices are not equal") and element by element up to the length; a struct field by field (all
three exported, so no panic on unexported fields), `string` and `uint64` by `==` (Lean's equality
of the fields: `Key'`, `Type'`, `ResourceVersion'`). Nil-ness is the model's `= slice.nil`. It
reads only the elements the points-tos hold and writes nothing the caller sees; the report's
randomized formatting only affects a non-empty result, which the spec does not describe. The
variadic options are the nil slice the translation passes for none (`Val #slice.nil`). Go
evidence: `examples/k8s/etcd3/correctness/cmpdiff_test.go` `TestCmpDiffEventRefs` (11 cases: nil
and empty differ) and `TestCmpDiffEventRefsRandom` (20000 random pairs; no `Equal` method, no
unexported field). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev cmp.Diff.spec_eventRefs : Prop :=
  ∀ (s1 s2 : GoSlice)
    (xs1 xs2 : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference)
    (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.go_cmp.cmp ∗
      s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}
    (App (App (App (Val #(functions _root_.Perennial.github_com.google.go_cmp.cmp.Diff []))
      (Val #(interface.mkOk (go.GoType.SliceType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference.ty) #s1)))
      (Val #(interface.mkOk (go.GoType.SliceType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference.ty) #s2)))
      (Val #slice.nil))
  {{ (d : GoString), RET #d;
      ⌜d = go!"" ↔ ((s1 = slice.nil ↔ s2 = slice.nil) ∧ xs1 = xs2)⌝ ∗
      s1 ↦*{dq1} xs1 ∗ s2 ↦*{dq2} xs2 }}

end spec

end EtcdGrove
end Perennial
