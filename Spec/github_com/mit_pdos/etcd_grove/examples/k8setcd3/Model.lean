/- Lean-first (no Rocq counterpart).

`Model(st0)` (k8setcd3.go): the store as a porcupine model, against `pM (kSpec g0) decOp`
(`k8setcd3S g0`, `MDefs.lean`) for the seeded store `g0` that `st0` holds, in the parts
`isModel_of_step` assembles: `Partition`, `StepContext` and `Hash` are `nil`; `Init` returns a
value of the initial state (one configuration, the seeded store); `Equal` returns `true` only on
equal lists, so on one state; and `Step` steps as `pM (kSpec g0) decOp` does.
`(k8setcd3S g0).rep k` is `stRepB g0 (k + g0.items.length + 1)`: a value made by `k` steps has
items and pending inputs fewer than `k + g0.items.length + 1` (`Bounded`), so the `make`s of
`len + 1` stay far from overflow below porcupine's index `2^60` (the premise bounds the seeded
store's items the same way).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8setcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  ∀ (s0 : mstore) (g0 : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      storeOwn s0 g0 ∗ ⌜g0.items.length < 2 ^ 60⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.Model)) (Val #s0))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗ github_com.anishathalye.porcupine.initSpec (k8setcd3S g0) m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗
      github_com.anishathalye.porcupine.stepSpec (k8setcd3S g0) m.Step' ∗
      github_com.anishathalye.porcupine.isEqHash (k8setcd3S g0) m }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
