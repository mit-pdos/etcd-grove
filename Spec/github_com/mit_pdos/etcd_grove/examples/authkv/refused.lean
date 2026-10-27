/-
`refused(who, what, err)` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
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

/-- `refused(who, what, err)` returns (does not panic) when `err` is not `nil`: the request was
refused. -/
abbrev refused.spec : Prop :=
  ∀ (who what : GoString) (err : GoInterface),
  err ≠ GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.refused)) (Val #who))
      (Val #what)) (Val #err))
  {{ RET #(); True }}

end spec

end authkv
end EtcdGrove
end Perennial
