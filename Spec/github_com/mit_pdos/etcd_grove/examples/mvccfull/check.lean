/- Lean-first (no Rocq counterpart).

`check(ok, msg)` (`examples/mvccfull/mvccfull.go`): returns when `ok` holds (otherwise it panics:
a failed check of the tester).
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
abbrev check.spec : Prop :=
  ∀ (ok : Bool) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ ⌜ok = true⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.check)) (Val #ok)) (Val #msg))
  {{ RET #(); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
