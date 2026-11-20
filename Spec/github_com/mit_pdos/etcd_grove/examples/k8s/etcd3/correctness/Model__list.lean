/- Lean-first (no Rocq counterpart).

`(*Model).list(key, opts)` (`correctness/model.go`) on the frozen model `m`, with `key` the list's
key `x.ListKey'` and `opts` `listOptions(in)` (`listOptsV x`): the response `rlistL x m` (k8s 7g
step 3). Premises (the driver's lists, `kInOk`): the resource version parses (as
`ListReadConsistency.spec`), the limit is not negative, and a positive limit comes with a resource
version other than `"0"`: `list`'s panics on a negative limit and on a limit with resource version
`"0"` (#108003) are not reached. Its other panics are not reached on `predicate(in)` (non-nil
selectors and `GetAttrs`, no continue token) and `listOptions(in)` (no `RecordTimestamps`).
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
abbrev Model.list.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input),
  (parseRVD x.MinRV').isSome → 0 ≤ sint.Z x.Limit' →
  (0 < sint.Z x.Limit' → x.MinRV' ≠ go!"0") →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp m }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"list" #mp))
      (Val #x.ListKey')) (Val #(listOptsV x)))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response), RET #r;
      respRep r (rlistL x m) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
