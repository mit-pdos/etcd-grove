/- Lean-first (no Rocq counterpart).

`Run(model, apply, gen, clock, clients, ops, timeout)` (lintest.go): `clients` goroutines each
run `ops` operations of the library `apply` on inputs from `gen`, traced as etcd's robustness
tests trace etcd (a `porcupine.Operation` per call, its call and return timestamps read from
`clock` just before and just after it), and porcupine checks the trace
(`CheckOperationsVerbose`, as etcd does).

**If the library is linearizable, porcupine never reports `Illegal`**, and with no timeout
(`timeout <= 0`) it reports `Ok`. The premises:

- `model` is porcupine's model `S` (`isModel`), with sequential specification `S.M`;
- `apply` is logically atomic against `S.M` over the library's abstract state `libState`
  (`applySpec`), which starts at `S.M.init`, on the inputs `i` with `inOk i` (the library's
  well-formed inputs: e.g. of the dynamic type it asserts);
- `clock` is logically atomic and monotone over its abstract value `clockVal`
  (`clockSpec`), e.g. `CounterClock`'s;
- `gen` returns an input `i` with `inOk i` (`genSpec`), any such input, so randomized
  traffic is covered;
- the invariants of the library and the clock (`Eapp`, `Eclk`) are not `Run`'s
  (`lintestN`);
- `clients * ops < 2^60` (porcupine's bound on a history, `HistOk`), `ops ≥ 0`, and
  `0 ≤ clients < 2^31` (`make` panics on a negative length; `sync.WaitGroup.Add` on a counter
  past `2^31 - 1`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (apply gen clock : GoFunc)
    (inOk : GoInterface → IProp GF) (libState : σ → IProp GF) (clockVal : w64 → IProp GF) (t0 : w64) (Eapp Eclk : CoPset)
    (clients ops dur : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
      isModel S m ∗ applySpec S inOk libState Eapp apply ∗ genSpec gen inOk ∗
      clockSpec clockVal Eclk clock ∗ libState S.M.init ∗ clockVal t0 }}
    (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.Run))
      (Val #m)) (Val #apply)) (Val #gen)) (Val #clock)) (Val #clients)) (Val #ops))
      (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end lintest
end EtcdGrove
end Perennial
