/-
`below(n)` (`examples/lib/cluster3/schedule.go`; the pure-premises plan's P4, 2026-11-24): a random
number in `[0, n)`, `primitive.RandomUint64() % n`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- For `n ≠ 0` (the modulus; `% 0` panics), `below(n)` returns a number below `n`. -/
abbrev below.spec : Prop :=
  ∀ (n : w64), uint.Z n ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.below)) (Val #n))
  {{ (r : w64), RET #r; ⌜uint.Z r < uint.Z n⌝ }}

end spec

end cluster3
end EtcdGrove
end Perennial
