/-
`reflect.Append(v, e)` of the addressable `Value` `v` of the slice variable at `p : []Obj` and the
addressable `Value` `e` of the `Obj` at `q` (passed in the one-element variadic slice `esl`): the
slice with the object appended, as its `Value`, consuming the old slice's elements and capacity
(as Perennial's `slice.append`: with spare capacity the result shares the backing array); the
variable is unchanged until `Set`.

Faithful: `Append` grows by `growslice` and copies the element, as `append` does
(`reflect/value.go`; `TestAppendSet`).

The trust boundary: an axiom, `Proof/reflect/Append.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`; stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev reflect.Append.spec : Prop :=
  ∀ (v : _root_.Perennial.reflect.Value) (p : Loc) (dq : DFrac) (s : GoSlice)
    (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (e : _root_.Perennial.reflect.Value) (esl : GoSlice) (dqe : DFrac) (q : Loc) (dq' : DFrac)
    (o : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflElem v (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) p ∧
        reflElem e github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty q⌝ ∗
      esl ↦*{dqe} [e] ∗
      p ↦{dq} s ∗ s ↦* os ∗ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj s (DFrac.own 1) ∗
      q ↦{dq'} o }}
    (App (App (Val (@! _root_.Perennial.reflect.Append)) (Val #v)) (Val #esl))
  {{ (w : _root_.Perennial.reflect.Value), RET #w; ∃ s', ⌜reflSliceV w github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty s'⌝ ∗
      esl ↦*{dqe} [e] ∗
      s' ↦* (os ++ [o]) ∗ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj s' (DFrac.own 1) ∗
      p ↦{dq} s ∗ q ↦{dq'} o }}

end spec

end EtcdGrove
end Perennial
