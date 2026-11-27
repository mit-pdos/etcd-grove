/-
`mulBelow(a, b, bound)` (`examples/k8s/all/checked.go`; the pure-premises plan's P5, 2026-11-24; as
`etcd/all`'s): whether `a * b < bound`, computed without overflow (`b == 0 || a <= (bound-1)/b`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

/-- For `a, b ≥ 0` and `bound > 0` (Go `int`s), `mulBelow(a, b, bound)` returns whether the exact
product `a * b` is below `bound`. -/
abbrev mulBelow.spec : Prop :=
  ∀ (a b bound : w64), 0 ≤ sint.Z a → 0 ≤ sint.Z b → 0 < sint.Z bound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.all }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.mulBelow)) (Val #a))
      (Val #b)) (Val #bound))
  {{ RET #(decide (sint.Z a * sint.Z b < sint.Z bound)); True }}

end spec

end k8s_all
end EtcdGrove
end Perennial
