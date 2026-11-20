/-
Lean-first (no Rocq counterpart).

`(*Model).initialEvents(request)` (`correctness/model.go`) on the frozen model `m`, with a request on
`key` whose options are as `Model.listItems`' (a predicate `predicate(in)`'s, any
`AllowWatchBookmarks`; recursive iff `x.Recursive'`): no error and an Added event for each item
`listItems` returns (`listItemsL x key m`), in order, read-only (`evsRO`; the nil slice when there
is none) (k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Model.initialEvents.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (key : GoString) (opts : k8s_io.apiserver.pkg.storage.ListOptions)
    (b : Bool),
  opts.Predicate' = { k8s_etcd3.predV x with AllowWatchBookmarks' := b } →
  opts.Recursive' = x.Recursive' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp m }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty)
      go!"initialEvents" #mp))
      (Val #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest.mk key opts)))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = GoInterface.nil⌝ ∗ evsRO sl ((listItemsL x key m).map fun o => ⟨evAdded, .obj o⟩) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
