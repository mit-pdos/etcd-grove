/- Lean-first (no Rocq counterpart).

`realCheck(st0, ops, timeout)` (`realcheck.go`, k8s 7g step 5): Kubernetes' `TestCorrectness` check, run on the
driver's history `ops` after `RunLin2` answered `Ok` and `failureFree(ops)` held. It never answers `Illegal`, and
answers `Ok` with no timeout (`timeout ≤ 0`): porcupine's run on the unary operations (the maintainers' `Model`,
`toPorcupineModel(initialModel(st0))`) is decided `Ok` (B2), its one linearization replays (`NewReplay`) and every
operation validates (`Replay.Validate`, B4), and every watch that ran is accepted by `ValidateWatch` (B5).

The premises are what `Check` has at the call: `RunLin2`'s `Ok` post (the history `ops` with its operations'
`ioOk` facts, linearized by its own order for the driver's model `pM (kSpec g0) decOp`, `HistOk`), `failureFree`'s
answer (`okOut` of every operation), the seeded configuration's facts (`RunOk g0`, what B2/B4 need of it), a
history short enough that the revisions do not wrap (`2^63`), and a seeded store of fewer than `2^60` items (`Model`'s
premise: the checker's models stay below `2^62` items, `slices.Sorted`'s bound).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input mstore)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev realCheck.spec : Prop :=
  ∀ (s0 : mstore) (g0 : HSt) (sl : GoSlice) (lops : List github_com.anishathalye.porcupine.Operation)
    (dur : w64),
  github_com.anishathalye.porcupine.Theory.IsLinearization (linkv.pM (kSpec g0) decOp)
    (github_com.anishathalye.porcupine.histOf lops) (List.range lops.length) →
  github_com.anishathalye.porcupine.HistOk lops →
  (∀ o ∈ lops, ∀ x y, o.Input' = boxIn x → o.Output' = boxOut y → okOut x y = true) →
  RunOk g0 → uint.nat g0.st.rv + lops.length < 2 ^ 63 → g0.st.items.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      context.isClosedchanInit ∗ storeOwn s0 g0.st ∗ sl ↦* lops ∗
      github_com.anishathalye.porcupine.opsIoOk (k8setcd3S g0) lops }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realCheck)) (Val #s0))
      (Val #sl)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
