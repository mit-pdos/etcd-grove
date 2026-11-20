/- Lean-first (no Rocq counterpart).

`(*Model).validateList(key, opts, expected, output)` (`correctness/model.go`) on the frozen model
`m`, with `key` the list's key `x.ListKey'` and `opts` `listOptions(in)` (`listOptsV x`, whose
`MinRV` parses), `expected` `execute`'s response (the view `exp`) and `output` the store's (`out`):
`rvalidateListL x m exp out`. Premises: both errors are flat (`flatE`: `IsTooLargeResourceVersion`
and `SuggestsClientDelay` read them; no `RErr.other`), and both objects are nil or lists
(`listOrNilD`: `meta.ListAccessor` in `equalListResponse` and `listResponseRV`). (k8s 7g step 3.)
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
abbrev Model.validateList.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input)
    (re ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (exp out : RResp),
  (parseRVD x.MinRV').isSome → flatE exp.err → flatE out.err → listOrNilD exp.obj → listOrNilD out.obj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ respRep re exp ∗ respRep ro out }}
    (App (App (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"validateList" #mp))
      (Val #x.ListKey')) (Val #(listOptsV x))) (Val #re)) (Val #ro))
  {{ RET #(rvalidateListL x m exp out); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
