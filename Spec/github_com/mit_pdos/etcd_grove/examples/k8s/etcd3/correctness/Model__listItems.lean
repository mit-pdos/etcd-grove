/- Lean-first (no Rocq counterpart).

`(*Model).listItems(key, opts)` (`correctness/model.go`) on the frozen model `m`, with `opts`
`listOptions(in)` (`listOptsV x`: its predicate `predicate(in)`, recursive iff `x.Recursive'`): no
error and fresh copies of the items in `key`'s scope that the predicate matches, in key order
(`listItemsL x key m`; k8s 7g step 3).
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
abbrev Model.listItems.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp m }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"listItems" #mp))
      (Val #key)) (Val #(listOptsV x)))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = GoInterface.nil⌝ ∗ objsOwn sl (listItemsL x key m) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
