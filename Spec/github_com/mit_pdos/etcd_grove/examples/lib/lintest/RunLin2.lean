/- Lean-first (no Rocq counterpart).

`RunLin2(model, apply, gen, clock, clients, ops, clients2, ops2, timeout)` (lintest.go):
`RunLin` with two groups of clients (2026-11-08, k8s 7f, `notes/k8s-7f-scope.md`: the k8s
driver's watchers, whose operations are whole watches, beside its unary clients). Clients `0` to
`clients - 1` run `ops` operations each, clients `clients` to `clients + clients2 - 1` run `ops2`
each; `gen` is called with every client's index. The premises are `RunLin`'s for the two groups
together: `0 ≤ clients`, `0 ≤ clients2`, `clients + clients2 < 2^31`, `0 ≤ ops`, `0 ≤ ops2`, and
the trace's length `clients * ops + clients2 * ops2 < 2^60`.

**If the library is linearizable, porcupine never reports `Illegal`**, and with no timeout it
reports `Ok`; and on `Ok` the second result holds all `clients * ops + clients2 * ops2`
operations of the trace in an order that linearizes them (as `RunLin`'s). `RunLin` is
`RunLin2` with an empty second group.
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
abbrev RunLin2.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (apply gen clock : GoFunc)
    (inOk : GoInterface → IProp GF) (libState : σ → IProp GF) (clockVal : w64 → IProp GF) (t0 : w64) (Eapp Eclk : CoPset)
    (clients ops clients2 ops2 dur : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z clients → 0 ≤ sint.Z clients2 → sint.Z clients + sint.Z clients2 < 2 ^ 31 →
  0 ≤ sint.Z ops → 0 ≤ sint.Z ops2 →
  sint.Z clients * sint.Z ops + sint.Z clients2 * sint.Z ops2 < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest ∗
      context.isClosedchanInit ∗
      isModel S m ∗ applySpec S inOk libState Eapp apply ∗ genSpec gen inOk ∗
      clockSpec clockVal Eclk clock ∗ libState S.M.init ∗ clockVal t0 }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin2))
      (Val #m)) (Val #apply)) (Val #gen)) (Val #clock)) (Val #clients)) (Val #ops))
      (Val #clients2)) (Val #ops2)) (Val #dur))
  {{ (r : GoString) (lsl : GoSlice), RET (PairV #r #lsl);
      ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ ∗
      (⌜r = go!"Ok"⌝ -∗ ∃ lops : List Operation, lsl ↦* lops ∗ opsIoOk S lops ∗
        ⌜(lops.length : Int) = sint.Z clients * sint.Z ops + sint.Z clients2 * sint.Z ops2 ∧
          Theory.IsLinearization S.M (histOf lops) (List.range lops.length)⌝) }}

end spec

end lintest
end EtcdGrove
end Perennial
