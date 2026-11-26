/- Lean-first (no Rocq counterpart).

`anyInts(n)` (`examples/mvccfull/config.go`): a new slice of `n` ints, each any int (`anyInt`).
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
abbrev anyInts.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInts)) (Val #n))
  {{ (s : GoSlice) (ws : List w64), RET #s; s ↦* ws }}

end spec

end mvccfull
end EtcdGrove
end Perennial
