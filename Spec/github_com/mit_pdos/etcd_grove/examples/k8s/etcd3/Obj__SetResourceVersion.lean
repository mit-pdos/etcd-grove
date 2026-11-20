/- Lean-first (no Rocq counterpart).

`(*Obj).SetResourceVersion(s)` (k8setcd3.go; `metav1.Object`'s, k8s 7g): the resource version
`setRVL s` (`ObjRV.lean`): `0` for `""`, the decimal value of `s` if it parses, unchanged
otherwise.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjRV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Obj.SetResourceVersion.spec : Prop :=
  ∀ (p : Loc) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦ v }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) go!"SetResourceVersion" #p)) (Val #s))
  {{ RET #(); p ↦ { v with ResourceVersion' := setRVL s v.ResourceVersion' } }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
