/-
`Principals()` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `Principals()` returns a new slice of the principals, `u`, `v`, `anon`, `bad`
(`principals`). -/
abbrev Principals.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.Principals)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* principals }}

end spec

end authkv
end EtcdGrove
end Perennial
