/- Lean-first (no Rocq counterpart).

`RunLin(model, apply, gen, clock, clients, ops, timeout)` (lintest.go): `Run`'s clients and
check (its premises are `Run`'s: see `Spec/.../lintest/Run.lean`), and, when porcupine answers
`Ok`, the linearization it found, as Kubernetes' `TestCorrectness` reads it
(`orderByLinearization(operations, info.PartialLinearizations()[0][0])`).

**If the library is linearizable, porcupine never reports `Illegal`**, and with no timeout it
reports `Ok`; and on `Ok` the second result holds all `clients * ops` operations of the trace
in an order that linearizes them: in that order (`List.range`) the model runs them from its
initial state, and no operation returns before an earlier one is called. (The trace is not
named in the spec: that the result is a permutation of it is the length and the code.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

/-- See the file header. -/
abbrev RunLin.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (apply gen clock : GoFunc)
    (inOk : GoInterface → IProp GF) (libState : σ → IProp GF) (clockVal : w64 → IProp GF) (t0 : w64) (Eapp Eclk : CoPset)
    (clients ops dur : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest ∗
      context.isClosedchanInit ∗
      isModel S m ∗ applySpec S inOk libState Eapp apply ∗ genSpec gen inOk ∗
      clockSpec clockVal Eclk clock ∗ libState S.M.init ∗ clockVal t0 }}
    (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin))
      (Val #m)) (Val #apply)) (Val #gen)) (Val #clock)) (Val #clients)) (Val #ops))
      (Val #dur))
  {{ (r : GoString) (lsl : GoSlice), RET (PairV #r #lsl);
      ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ ∗
      (⌜r = go!"Ok"⌝ -∗ ∃ lops : List Operation, lsl ↦* lops ∗ opsIoOk S lops ∗
        ⌜(lops.length : Int) = sint.Z clients * sint.Z ops ∧
          Theory.IsLinearization S.M (histOf lops) (List.range lops.length)⌝) }}

end spec

end lintest
end EtcdGrove
end Perennial
