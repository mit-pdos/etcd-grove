/- Lean-first (no Rocq counterpart).

`(*Obj).GetResourceVersion()` (k8setcd3.go; `metav1.Object`'s, stage 7b): the versioner's
string of the object's resource version (`rvStr`).
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
abbrev Obj.GetResourceVersion.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (name uid val : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name uid val rv }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) go!"GetResourceVersion" #p))
      (Val #()))
  {{ RET #(rvStr rv); p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name uid val rv }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
