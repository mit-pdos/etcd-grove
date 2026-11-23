/- Lean-first (no Rocq counterpart).

`(*Model).update(ctx, key, ignoreNotFound, preconditions, tryUpdate, cachedExistingObject)`
(`correctness/model.go`, with the D30g patch) on the owned model `m` (`execute`'s clone), with the
arguments `realRequest(x)` passes: `key` the store key of `x`'s key, `x.IgnoreNotFound`, the
`*Preconditions` of `kpreOf x` (`preconditions(x)`), `tryUpdateFor(x)`'s closure (`tryUpdateD`, not
the nil func) and any cached object (unused): the response, the next model and the change of
`rupdateL x m` (k8s 7g step 3). The model's items are the driver's objects (`itemsFitL`) and the
input fits (`inFits`), so that the stored object is an `objAtD` that `Check` and the closure take.
The model has fewer than `2^62` items (a write may add one; `itemsRO` keeps at most `2^62`, the bound of
`slices.Sorted(maps.Keys(s.Items))`).
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
abbrev Model.update.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (ctx : GoInterface) (pp : Loc) (uf : GoFunc)
      (cx : GoInterface),
  itemsFitL m → k8s_etcd3.inFits x → uf ≠ func.nil → GMap.size m.items < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelOwn mp m ∗ k8s.preAt pp (k8s_etcd3.kpreOf x) ∗ k8s_etcd3.tryUpdateD x uf }}
    (App (App (App (App (App (App
      (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"update" #mp))
      (Val #ctx)) (Val #(k8s_etcd3.storeKeyL x.Key'))) (Val #x.IgnoreNotFound')) (Val #pp))
      (Val #uf)) (Val #cx))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (cp : Loc), RET (PairV #r #cp);
      modelOwn mp (rupdateL x m).2.1 ∗ respRep r (rupdateL x m).1 ∗ changeRep cp (rupdateL x m).2.2 }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
