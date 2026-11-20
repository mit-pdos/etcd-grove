/-
Lean-first (no Rocq counterpart).

`WatchValidator.validateBookmarks(events)` (`correctness/watch.go`) on the validator `realCheck`
builds (`validatorV rp`: the driver's versioner) and read-only events of views `rs` the pure check
accepts (`bookmarksOkR rs`): `nil` (k8s 7g step 5; accepting runs only). The driver's package is
initialized (its objects' methods, `objectRV`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

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
abbrev WatchValidator.validateBookmarks.spec : Prop :=
  ∀ (rp : Loc) (sl : GoSlice) (rs : List REv),
  bookmarksOkR rs = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ evsRO sl rs }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"validateBookmarks" #(validatorV rp))) (Val #sl))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
