/- Lean-first (no Rocq counterpart).

`(*Model).delete(ctx, key, preconditions, validateDeletion)` (`correctness/model.go`, with the
D30g patch) on the owned model `m` (`execute`'s clone), with the arguments `realRequest(x)` passes:
`key` the store key of `x`'s key, the `*Preconditions` of `kpreOf x` (`preconditions(x)`) and
`validateFor(x.HasReject, x.Reject)`'s closure (`validateD`, not the nil func): the response, the
next model and the change of `rdeleteL x m` (k8s 7g step 3). The model's items are the driver's
objects (`itemsFitL`), so that the stored object is an `objAtD` that `Check` takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ModelFit

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
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Model.delete.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (ctx : GoInterface) (pp : Loc) (vf : GoFunc),
  itemsFitL m → vf ≠ func.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelOwn mp m ∗ k8s.preAt pp (k8s_etcd3.kpreOf x) ∗ k8s_etcd3.validateD x.HasReject' x.Reject' vf }}
    (App (App (App (App
      (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"delete" #mp))
      (Val #ctx)) (Val #(k8s_etcd3.storeKeyL x.Key'))) (Val #pp)) (Val #vf))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (cp : Loc), RET (PairV #r #cp);
      modelOwn mp (rdeleteL x m).2.1 ∗ respRep r (rdeleteL x m).1 ∗ changeRep cp (rdeleteL x m).2.2 }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
