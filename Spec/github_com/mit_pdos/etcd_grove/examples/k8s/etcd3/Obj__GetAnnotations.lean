/- Lean-first (no Rocq counterpart).

`(*Obj).GetAnnotations()` (k8setcd3.go; `metav1.Object`'s, stage E of 7f-6:
`storage.AnnotateInitialEventsEndBookmark`'s): a fresh map holding only the initial-events-end
annotation if the object is annotated, else `nil`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Obj.GetAnnotations.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} v }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) go!"GetAnnotations" #p)) (Val #()))
  {{ (m : GoMap), RET #m; p ↦{dq} v ∗
      if v.Annotated' then
        ownMap m (DFrac.own 1) (<[go!"k8s.io/initial-events-end" := go!"true"]> ∅ : GMap GoString GoString)
      else ⌜m = map.nil⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
