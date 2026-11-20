/- Lean-first (no Rocq counterpart).

`(*Model).equalListResponse(key, opts, expected, output)` (`correctness/model.go`) on the frozen
model `m`, with `key` the list's key `x.ListKey'` and `opts` `listOptions(in)` (`listOptsV x`):
`equalListRespL x m exp out` (the same response, or, with a limit, two lists that differ only by
the output's continue token, which `validCacherContinueL` allows). Premises: both objects are nil
or lists (`listOrNilD`: `meta.ListAccessor`), the expected error has a deep view (`deepErrE`) and
the output's is flat (`flatE`): the first `reflect.DeepEqual` compares the two responses,
`reflect.DeepEqual.spec_k8s` clause 2, or clause 4 for the output's too-large error (k8s 7g step 3).
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

/-- See the file header. -/
abbrev Model.equalListResponse.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input)
    (re ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (exp out : RResp),
  listOrNilD exp.obj → listOrNilD out.obj → deepErrE exp.err → flatE out.err →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m ∗ respRep re exp ∗ respRep ro out }}
    (App (App (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"equalListResponse" #mp))
      (Val #x.ListKey')) (Val #(listOptsV x))) (Val #re)) (Val #ro))
  {{ RET #(equalListRespL x m exp out); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
