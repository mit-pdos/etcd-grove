/-
`decimal(s, max)` (addrs.go): `(n, true)` for the value `n` of `s` as a canonical decimal numeral
of at most five digits, at most `max` (`decimalM`); otherwise `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Assumptions]

/-- See the file header. -/
abbrev deployment.decimal.spec : Prop :=
  ∀ (s : GoString) (mx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.decimal)) (Val #s)) (Val #mx))
  {{ (n : w64) (ok : Bool), RET (PairV #n #ok);
      ⌜(if ok then some (uint.nat n) else none) = decimalM s (uint.nat mx)⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
