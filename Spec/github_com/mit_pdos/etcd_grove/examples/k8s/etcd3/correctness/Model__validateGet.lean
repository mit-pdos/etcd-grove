/- Lean-first (no Rocq counterpart).

`(*Model).validateGet(opts, expected, output)` (`correctness/model.go`) on the frozen model `m`,
with `opts` `realRequest(x)`'s get options (`ResourceVersion` `x.MinRV`, which parses), `expected`
`execute`'s response (the view `exp`) and `output` the store's (`out`): `rvalidateGetL x m exp out`.
Premises: both errors are flat (`flatE`: the checker's `IsNotFound`, `IsTooLargeResourceVersion`
and `SuggestsClientDelay` read them; no `RErr.other`, which has no such view), and the output's
object is nil or an object (`objOrNilD`: the versioner's `ObjectResourceVersion`). The responses
are compared by `reflect.DeepEqual.spec_k8s` clause 2 (two deep errors) or clause 4 (the output's
too-large error). (k8s 7g step 3.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ErrViews

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
abbrev Model.validateGet.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (opts : k8s_io.apiserver.pkg.storage.GetOptions)
    (re ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (exp out : RResp),
  opts.ResourceVersion' = x.MinRV' → (parseRVD x.MinRV').isSome →
  flatE exp.err → flatE out.err → objOrNilD out.obj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ respRep re exp ∗ respRep ro out }}
    (App (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"validateGet" #mp))
      (Val #opts)) (Val #re)) (Val #ro))
  {{ RET #(rvalidateGetL x m exp out); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
