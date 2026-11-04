/-
`keyOf(x, who, n)` (`examples/etcd/auth/etcd_auth.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- `keyOf(x, who, n)` is the key `x/<who>/<n>` (`keyOfK`). -/
abbrev keyOf.spec : Prop :=
  ∀ (x who n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.keyOf)) (Val #x))
      (Val #who)) (Val #n))
  {{ RET #(keyOfK x who n); True }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
