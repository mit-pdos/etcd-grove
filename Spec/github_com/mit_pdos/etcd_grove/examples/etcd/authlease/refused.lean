/-
`refused(who, what, err)` (`examples/etcd/authlease/authlease.go`; authkv's, copied for auth-lease S4, 2026-11-18). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- `refused(who, what, err)` returns (does not panic) when `err` is not `nil`: the request was
refused. -/
abbrev refused.spec : Prop :=
  ∀ (who what : GoString) (err : GoInterface),
  err ≠ GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused)) (Val #who))
      (Val #what)) (Val #err))
  {{ RET #(); True }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
