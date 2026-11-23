/- Lean-first (no Rocq counterpart).

`(*Model).create(key, obj)` (`correctness/model.go`) on the owned model `m` (`execute`'s clone),
with `key` the store key of `x`'s key and `obj` a read-only `*Obj` holding `createObjL x`
(`realRequest(x)`'s object): the response, the next model and the change of `rcreateL x m`
(k8s 7g step 3).
The model has fewer than `2^62` items (a write may add one; `itemsRO` keeps at most `2^62`, the bound of
`slices.Sorted(maps.Keys(s.Items))`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev Model.create.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (op : Loc),
  GMap.size m.items < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelOwn mp m ∗ op ↦□ createObjL x }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"create" #mp))
      (Val #(k8s_etcd3.storeKeyL x.Key')))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op)))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (cp : Loc),
      RET (PairV #r #cp);
      modelOwn mp (rcreateL x m).2.1 ∗ respRep r (rcreateL x m).1 ∗ changeRep cp (rcreateL x m).2.2 }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
