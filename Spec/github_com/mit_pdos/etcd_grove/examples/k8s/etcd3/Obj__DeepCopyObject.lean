/- Lean-first (no Rocq counterpart).

`(*Obj).DeepCopyObject()` (k8setcd3.go; `runtime.Object`'s): a fresh `*Obj` holding a copy of the
object (k8s 7g step 3: the maintainers' checker copies its objects before writing them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base

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
abbrev Obj.DeepCopyObject.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} v }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) go!"DeepCopyObject" #p)) (Val #()))
  {{ (c : Loc), RET #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #c);
      p ↦{dq} v ∗ c ↦ v }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
