/- Lean-first (no Rocq counterpart).

`perclient.Run(model, apply, gen, clock, clients, ops, timeout)` (perclient.go): lintest's `Run`
(`Spec/.../lib/lintest/Run.lean`, whose header says what the premises mean) with an `apply` told
which client calls it: client `id`'s operations are `apply(id, i)`. The one difference in the
premises is `applySpecId` (`Proof/.../lintest/perclient/Defs.lean`): `apply(id, ·)` is logically
atomic for every client index `0 ≤ id < clients`. The conclusion is lintest's: porcupine never
reports `Illegal`, and `Ok` with no timeout.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace perclient

open Iris Iris.BI github_com.anishathalye.porcupine lintest

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (apply gen clock : GoFunc)
    (inOk : GoInterface → IProp GF) (libState : σ → IProp GF) (clockVal : w64 → IProp GF) (t0 : w64) (Eapp Eclk : CoPset)
    (clients ops dur : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient ∗
      context.isClosedchanInit ∗
      isModel S m ∗ applySpecId S inOk libState Eapp clients apply ∗ genSpec gen inOk ∗
      clockSpec clockVal Eclk clock ∗ libState S.M.init ∗ clockVal t0 }}
    (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Run))
      (Val #m)) (Val #apply)) (Val #gen)) (Val #clock)) (Val #clients)) (Val #ops))
      (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end perclient
end EtcdGrove
end Perennial
