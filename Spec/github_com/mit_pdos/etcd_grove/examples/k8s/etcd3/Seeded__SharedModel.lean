/-
Lean-first (no Rocq counterpart).

# `Seeded.SharedModel(revs, mode)` (k8s-dist K9 step 4, `notes/k8s-dist-k9.md` §2.1)

The store shared with foreign writers as a porcupine model, against `sharedM g0 R mode`
(`sharedS`, `SharedModelDefs.lean`) for the seeded store and history `g0` that `s` holds and the
history's revisions `R` that `r` holds, in the parts `isModel_of_step` assembles: `Partition`,
`StepContext` and `Hash` are `nil`; `Init` returns a value of the initial state; `Equal` returns
`true` only on values of one state; `Step` steps as `sharedM` does. The seeded history is well
formed (`HWf`), its revision and `R`'s below `2^62` and its items below `2^61` (`SharedBounded`'s
room: see `SharedModelDefs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedModelDefs

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
abbrev Seeded.SharedModel.spec : Prop :=
  ∀ (s : Seeded) (hs : List mstore) (g0 : HSt) (r : Revs) (R : RevsL) (mode : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      storeOwn s.st0' g0.st ∗ s.h0' ↦*□ hs ∗ ([∗list] x;g ∈ hs;g0.hist, storeOwn x g) ∗
      revsOwn r R ∗
      ⌜HWf g0 ∧ uint.nat g0.st.rv ≤ 2 ^ 62 ∧ g0.st.items.length < 2 ^ 61 ∧ RevsLBelow R⌝ }}
    (App (App (Val #(methods Seeded.ty go!"SharedModel" #s)) (Val #r)) (Val #mode))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗
      github_com.anishathalye.porcupine.initSpec (sharedS g0 R (uint.nat mode)) m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗
      github_com.anishathalye.porcupine.stepSpec (sharedS g0 R (uint.nat mode)) m.Step' ∗
      github_com.anishathalye.porcupine.isEqHash (sharedS g0 R (uint.nat mode)) m }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
