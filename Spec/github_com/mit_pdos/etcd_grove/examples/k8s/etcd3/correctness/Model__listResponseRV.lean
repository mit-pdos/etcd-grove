/- Lean-first (no Rocq counterpart).

`(*Model).listResponseRV(output)` (`correctness/model.go`) on the frozen model `m`: the output's
list resource version, if positive (`listRespRVL`; `0, false` otherwise). Premise: the output's
object is nil or a list (`listOrNilD`; `meta.ListAccessor`'s spec has no row for the driver's
`*Obj`, nor for an error value; k8s 7g step 3, accepted as a form by etcd-grove-03).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev Model.listResponseRV.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)
    (rr : RResp),
  listOrNilD rr.obj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ respRep r rr }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"listResponseRV" #mp))
      (Val #r))
  {{ RET (PairV #((listRespRVL rr).getD 0) #((listRespRVL rr).isSome)); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
