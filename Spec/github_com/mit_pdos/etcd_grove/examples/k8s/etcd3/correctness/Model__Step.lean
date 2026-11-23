/- Lean-first (no Rocq counterpart).

`(*Model).Step(input, output)` (`correctness/model.go`, porcupine's step) on the frozen model `m`,
the request `realRequest(x)` (`reqRep`) and the store's response `output` (the view `out`):
`rstepL x m out`'s verdict, next model (frozen) and change. A read leaves the model; a write
passes when `output` deep-equals `execute`'s response and then moves to its clone.

Premises: `execute`'s (the model's items are the driver's objects, the input fits, a list's
options), the input's minimum resource version parses (`validateGet`'s and `validateList`'s), the
model's response has no `RErr.other` error (the driver's requests never make one: a key
`PrepareKey` rejects, a resource version that does not parse; discharged in step 5), the output's
error is flat (`flatE`) and its object nil or a list for a list, nil or an object for a get.
`IsTooManyRequests` answers `false` on every flat error, so `Step`'s first branch (and its panic on
a write) is never taken. (k8s 7g step 3.)
The model has fewer than `2^62` items (a write may add one; `itemsRO` keeps at most `2^62`, the bound of
`slices.Sorted(maps.Keys(s.Items))`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ErrViews
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ModelFit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map k8s_etcd3
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
abbrev Model.Step.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input)
    (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (out : RResp),
  itemsFitL m → inFits x → (parseRVD x.MinRV').isSome →
  (x.Kind' = W64 4 → 0 ≤ sint.Z x.Limit' ∧ (0 < sint.Z x.Limit' → x.MinRV' ≠ go!"0")) →
  (rexecL x m).1.err ≠ .other → flatE out.err →
  (x.Kind' = W64 4 → listOrNilD out.obj) →
  (isWriteL x = false → x.Kind' ≠ W64 4 → objOrNilD out.obj) →
  GMap.size m.items < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ reqRep r x ∗ respRep ro out }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"Step" #mp))
      (Val #r)) (Val #ro))
  {{ (b : Bool) (np cp : Loc), RET (PairV (PairV #b #np) #cp);
      ⌜b = (rstepL x m out).1⌝ ∗ modelAt np (rstepL x m out).2.1 ∗ changeRep cp (rstepL x m out).2.2 }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
