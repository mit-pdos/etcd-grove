/- Lean-first (no Rocq counterpart).

`pick(w, n)` (`examples/mvccfull/config.go`): any alternative in `[0, n)` (`0` when `n ≤ 0`). The
weights `w` (read only) only make some alternatives likelier, or rule out those of weight `0` when
another is positive: the spec says nothing of them (a safety proof needs only the range; the
coverage claim of `config.go` is about the Go code, not proved here). The sum of the weights may
wrap: then `choose(n)` or the last alternative, still in range.
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
abbrev pick.spec : Prop :=
  ∀ (w : GoSlice) (ws : List w64) (dq : DFrac) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ w ↦*{dq} ws }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.pick)) (Val #w)) (Val #n))
  {{ (x : w64), RET #x; w ↦*{dq} ws ∗
      ⌜0 ≤ sint.Z x ∧ (0 < sint.Z n → sint.Z x < sint.Z n) ∧ (sint.Z n ≤ 0 → x = W64 0)⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
