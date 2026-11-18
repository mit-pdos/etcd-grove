/- Lean-first (no Rocq counterpart).

`(*Obj).SetAnnotations(m)` (k8setcd3.go; `metav1.Object`'s, stage E of 7f-6:
`storage.AnnotateInitialEventsEndBookmark`'s): the object is annotated iff the map holds `"true"`
at the initial-events-end key.
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
abbrev Obj.SetAnnotations.spec : Prop :=
  ∀ (p : Loc) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (m : GoMap) (dq : DFrac)
    (M : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦ v ∗
      ownMap m dq M }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) go!"SetAnnotations" #p)) (Val #m))
  {{ RET #(); p ↦ { v with Annotated' := decide (M !! go!"k8s.io/initial-events-end" = some go!"true") } ∗
      ownMap m dq M }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
