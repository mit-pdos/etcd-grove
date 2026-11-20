/- Lean-first (no Rocq counterpart).

`WatchValidator.ValidateWatch(request, response)` (`correctness/watch.go`), on the validator
`realCheck` builds (`NewWatchValidator(versioner{}, replay, keyFunc)`: the driver's versioner and
`keyFunc`, the frozen replay `R`), the driver's watch `x` as the request (`wreqRep`, `wInPre`) and a
response without error whose events have the views `rs` (`evsRO`): `nil` when the pure check accepts
(`validateWatchL R x rs`) (k8s 7g step 5). Only the accepting run is specified: a rejection's error
formats `cmp.Diff` of two objects, which has no spec (`cmp.Diff.spec_eventRefs` covers
`[]eventReference` only), and `realCheck` calls it only on watches B5 accepts
(`validateWatchL_of_watchOkL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

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
abbrev WatchValidator.ValidateWatch.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest)
    (sl : GoSlice) (rs : List REv),
  wInPre x → validateWatchL R x rs = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ wreqRep req x ∗ evsRO sl rs }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"ValidateWatch" #(validatorV rp))) (Val #req))
      (Val #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchResponse.mk sl
        GoInterface.nil)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
