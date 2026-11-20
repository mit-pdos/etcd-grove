/- Lean-first (no Rocq counterpart).

`(*ObjList).SetContinue(c)` (k8setcd3.go; `metav1.ListInterface`'s, k8s 7g step 3): sets the
list's continue token.
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
abbrev ObjList.SetContinue.spec : Prop :=
  ∀ (p : Loc) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList) (c : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦ v }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) go!"SetContinue" #p))
      (Val #c))
  {{ RET #(); p ↦ { v with Continue' := c } }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
