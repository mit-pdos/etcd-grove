/- Lean-first (no Rocq counterpart).

`toPorcupineModel(s)` (`realcheck.go`, TestCorrectness's `ToPorcupineModel`): a porcupine model of the
maintainers' `correctness.Model` from the frozen initial model `s` (k8s 7g step 5, decision 1): `isModel` of
`realMS L init`, for any table `L` of the operations' values and views (`realM L init`: `Step` on a value
decoded by `L`'s first entry with it). Its `Init` clones `s`, its `Step` type-asserts and calls
`Model.Step`, its `Equal` is `Model.Equal`; no `Hash`, no `Partition`, no `StepContext`. The initial model has
at most `2^61` items (`realMS`'s bound at index `0`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev toPorcupineModel.spec : Prop :=
  ∀ (mp : Loc) (init : RM) (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp))),
  itemsFitL init → GMap.size init.items ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp init }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toPorcupineModel)) (Val #mp))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m;
      github_com.anishathalye.porcupine.isModel (realMS L init) m }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
