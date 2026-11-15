/-
`reflect.Copy(w, v)` of a `MakeSlice` `Value` `w` (the slice `sd : []Obj`) and the addressable
`Value` `v` of the slice variable at `p`: copies `min` of the lengths, returns it, the source
unchanged.

Faithful: `Copy` is `typedslicecopy` of `min(len(dst), len(src))` elements (`reflect/value.go`;
`TestCopy`).

The trust boundary: an axiom, `Proof/reflect/Copy.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`; stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`). Lean-first (no Rocq counterpart).
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
abbrev reflect.Copy.spec : Prop :=
  ∀ (w : _root_.Perennial.reflect.Value) (sd : GoSlice) (ds : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (v : _root_.Perennial.reflect.Value) (p : Loc) (dq dq' : DFrac) (ss : GoSlice)
    (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflSliceV w github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty sd ∧
        reflElem v (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) p⌝ ∗
      sd ↦* ds ∗ p ↦{dq} ss ∗ ss ↦*{dq'} os }}
    (App (App (Val (@! _root_.Perennial.reflect.Copy)) (Val #w)) (Val #v))
  {{ RET #(W64 (min ds.length os.length : Int)); p ↦{dq} ss ∗ ss ↦*{dq'} os ∗
      sd ↦* (os.take ds.length ++ ds.drop os.length) }}

end spec

end EtcdGrove
end Perennial
