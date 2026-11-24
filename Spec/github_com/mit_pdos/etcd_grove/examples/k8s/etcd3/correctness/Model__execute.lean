/- Lean-first (no Rocq counterpart).

`(*Model).execute(input)` (`correctness/model.go`) on the frozen model `m` (`Step`'s receiver) and
the request `realRequest(x)` (`reqRep`): the response and the change of `rexecL x m`, and the next
model: a fresh owned clone holding `(rexecL x m).2.1` for a write (create, delete, update), the
receiver itself for a read (get, list; `(rexecL x m).2.1 = m`). The model's items are the driver's
objects (`itemsFitL`) and the input fits (`inFits`), for `update` and `delete`; a list's input
meets `Model.list.spec`'s premises (`MinRV` parses, a non-negative limit, no limit with
`MinRV "0"`). (k8s 7g step 3.)
The model has fewer than `2^62` items (a write may add one; `itemsRO` keeps at most `2^62`, the bound of
`slices.Sorted(maps.Keys(s.Items))`).
-/
module

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
abbrev Model.execute.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input)
    (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request),
  itemsFitL m → k8s_etcd3.inFits x →
  (x.Kind' = W64 4 → (k8s_etcd3.parseRVD x.MinRV').isSome ∧ 0 ≤ sint.Z x.Limit' ∧
    (0 < sint.Z x.Limit' → x.MinRV' ≠ go!"0")) →
  GMap.size m.items < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ reqRep r x }}
    (App (Val #(methods (go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"execute" #mp))
      (Val #r))
  {{ (resp : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)
      (np cp : Loc), RET (PairV (PairV #resp #np) #cp);
      respRep resp (rexecL x m).1 ∗ changeRep cp (rexecL x m).2.2 ∗
      (if k8s_etcd3.isWriteL x then modelOwn np (rexecL x m).2.1
       else iprop(⌜np = mp ∧ (rexecL x m).2.1 = m⌝)) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
