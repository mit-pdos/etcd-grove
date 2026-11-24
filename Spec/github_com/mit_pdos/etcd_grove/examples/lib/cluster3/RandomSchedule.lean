/-
`RandomSchedule(n)` (`examples/lib/cluster3/schedule.go`; the pure-premises plan's P4, 2026-11-24): a
fault schedule of `n` random steps (none if `n ≤ 0`), each drawn with `below`. A program that draws
its schedule with it (`etcd/all`'s and `k8s/all`'s `MainChecked`) is proved for every schedule it may
draw, with no premise on a schedule it is given. Lean-first (no Rocq counterpart).
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

/-- `RandomSchedule(n)` returns a slice of some steps, `n` of them when `n ≥ 0`. -/
abbrev RandomSchedule.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.RandomSchedule)) (Val #n))
  {{ (s : GoSlice), RET #s;
      ∃ steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step,
        s ↦* steps ∗ ⌜0 ≤ sint.Z n → steps.length = sint.nat n⌝ }}

end spec

end cluster3
end EtcdGrove
end Perennial
