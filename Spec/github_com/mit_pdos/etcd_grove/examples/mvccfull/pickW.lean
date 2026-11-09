/- Lean-first (no Rocq counterpart).

`pick(w, n)` (`examples/mvccfull/config.go`), **with its weights** (`pick.specW`): any alternative
in `[0, n)` (`0` when `n ≤ 0`), as `pick.spec`; and, when some alternative below `n` has a positive
weight and the positive weights of the first `n` sum below `2 ^ 63` (so `total` does not wrap), the
chosen alternative has a positive weight: `r = choose(total)` is below `total`, so the second loop
returns at an alternative `i` with `r < w[i]`, `w[i] > 0`, before falling through to `n - 1`. (When
`total` wraps, the fall-through can return `n - 1` at any weight: the premise is needed.)

It is stronger than `pick.spec` (its first conjunct), which becomes its corollary (one proof per
function: `pick.spec` to be derived from `pick.wp_proofW`). The readers' F1 scope premise
(`readMixOk`, `Readers.lean`) is this premise at `n = 6` with the hashes' weight not positive.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev pick.specW : Prop :=
  ∀ (w : GoSlice) (ws : List w64) (dq : DFrac) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ w ↦*{dq} ws }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.pick)) (Val #w)) (Val #n))
  {{ (x : w64), RET #x; w ↦*{dq} ws ∗
      ⌜0 ≤ sint.Z x ∧ (0 < sint.Z n → sint.Z x < sint.Z n) ∧ (sint.Z n ≤ 0 → x = W64 0)⌝ ∗
      ⌜(∃ i : Nat, (i : Int) < sint.Z n ∧ 0 < ((ws.map sint.Z).getD i 0)) →
        (((ws.map sint.Z).take (sint.nat n)).map (fun z => max 0 z)).sum < 2 ^ 63 →
        0 < (ws.map sint.Z).getD (sint.nat x) 0⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
