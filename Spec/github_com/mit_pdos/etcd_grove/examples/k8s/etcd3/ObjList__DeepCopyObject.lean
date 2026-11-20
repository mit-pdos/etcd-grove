/- Lean-first (no Rocq counterpart).

`(*ObjList).DeepCopyObject()` (k8setcd3.go; `runtime.Object`'s, k8s 7g step 3: the maintainers'
checker copies an expected list before setting its continue token, `equalListResponse`): a fresh
`*ObjList` with the same resource version and continue token, a fresh copy of the remaining item
count, and a fresh, non-nil copy of the items (`append([]Obj{}, l.Items...)`: a nil `Items` becomes
an empty one).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Deep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8sDeep

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev ObjList.DeepCopyObject.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (sl : GoSlice) (rv : w64) (cont : GoString) (rp : Loc)
    (items : Option (List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)) (rem : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk sl rv cont rp ∗
      itemsRep dq sl items ∗ remRep dq rp rem }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) go!"DeepCopyObject" #p)) (Val #()))
  {{ (c : Loc), RET #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #c);
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk sl rv cont rp ∗
      itemsRep dq sl items ∗ remRep dq rp rem ∗
      ∃ (sl' : GoSlice) (rp' : Loc),
        c ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk sl' rv cont rp' ∗
        itemsRep (DFrac.own 1) sl' (some (items.getD [])) ∗ remRep (DFrac.own 1) rp' rem }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
