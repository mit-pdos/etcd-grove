/- Lean-first (no Rocq counterpart).

`(*ObjList).GetResourceVersion()` (k8setcd3.go; `metav1.ListInterface`'s, which the
maintainers' checker reads through `meta.ListAccessor`, k8s 7g step 3): the versioner's string of
the list's resource version (`rvStr`).
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
abbrev ObjList.GetResourceVersion.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} v }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) go!"GetResourceVersion" #p))
      (Val #()))
  {{ RET #(rvStr v.ResourceVersion'); p ↦{dq} v }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
