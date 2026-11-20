/- Lean-first (no Rocq counterpart).

`newObjList()` (`realcheck.go`, the `correctness.Model`'s `NewListFunc`): a new `*ObjList`, as a
`runtime.Object`, owned and zero (k8s 7g step 3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev newObjList.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObjList)) (Val #()))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #p : GoInterface);
      p ↦ (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
