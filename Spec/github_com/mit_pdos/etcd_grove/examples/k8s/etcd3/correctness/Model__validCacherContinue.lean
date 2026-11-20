/- Lean-first (no Rocq counterpart).

`(*Model).validCacherContinue(key, opts, expContinue, outContinue)` (`correctness/model.go`) on the
frozen model `m`, with `key` the list's key `x.ListKey'` and `opts` `listOptions(in)`
(`listOptsV x`): `validCacherContinueL x m outContinue` (no token in the output, a selecting
predicate, and exactly `limit` matching items; k8s 7g step 3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

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
abbrev Model.validCacherContinue.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (expC outC : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp m }}
    (App (App (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"validCacherContinue" #mp))
      (Val #x.ListKey')) (Val #(listOptsV x))) (Val #expC)) (Val #outC))
  {{ RET #(validCacherContinueL x m outC); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
