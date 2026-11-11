/- Lean-first (no Rocq counterpart).

`Model(st0, h0)` (k8s_etcd3.go): the store as a porcupine model, against `pM (kSpec g0) decOp`
(`k8setcd3S g0`, `MDefs.lean`) for the seeded store and history `g0` that `st0` and `h0` hold
(`h0` read-only: `Init` reads it on every call), in the parts
`isModel_of_step` assembles: `Partition`, `StepContext` and `Hash` are `nil`; `Init` returns a
value of the initial state (one configuration, the seeded store and its history); `Equal` returns `true` only on
equal lists, so on one state; and `Step` steps as `pM (kSpec g0) decOp` does.
`(k8setcd3S g0).rep k` is `stRepB g0 (k + g0.st.items.length + g0.hist.length + 1)`: a value
made by `k` steps has items, history and pending inputs fewer than that (`Bounded`), so the
`make`s of `len + 1` and the history's length stay far from overflow below porcupine's index
`2^60` (the premise bounds the seeded store's items and history the same way).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  ∀ (s0 : mstore) (hsl : GoSlice) (hs : List mstore) (g0 : HSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      storeOwn s0 g0.st ∗ hsl ↦*□ hs ∗ ([∗list] x;g ∈ hs;g0.hist, storeOwn x g) ∗
      ⌜g0.st.items.length + g0.hist.length < 2 ^ 60⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Model)) (Val #s0))
      (Val #hsl))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗ github_com.anishathalye.porcupine.initSpec (k8setcd3S g0) m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗
      github_com.anishathalye.porcupine.stepSpec (k8setcd3S g0) m.Step' ∗
      github_com.anishathalye.porcupine.isEqHash (k8setcd3S g0) m }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
