/- Lean-first (no Rocq counterpart).

`buildPath(prefix, n)` (`examples/mvccfull/mvccfull.go`): the `n`-th snapshot's file,
`prefix + "-b" + itoa(n) + ".db"` (`buildPathM`), for `n ≥ 0`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- The `n`-th snapshot's file. -/
def buildPathM (pfx : GoString) (n : Nat) : GoString := pfx ++ go!"-b" ++ itoaM n ++ go!".db"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev buildPath.spec : Prop :=
  ∀ (pfx : GoString) (n : w64), 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath)) (Val #pfx)) (Val #n))
  {{ RET #(buildPathM pfx (sint.nat n)); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
