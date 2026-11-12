/- Lean-first (no Rocq counterpart).

`choose(n)` (`examples/mvccfull/config.go`): any number in `[0, n)`, `0` when `n ≤ 0` (the tester's
choices: `primitive.RandomUint64`, which returns any value).
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
abbrev choose.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.choose)) (Val #n))
  {{ (x : w64), RET #x;
      ⌜0 ≤ sint.Z x ∧ (0 < sint.Z n → sint.Z x < sint.Z n) ∧ (sint.Z n ≤ 0 → x = W64 0)⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
