/-
`refused(who, what, err)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): panics if `err`
is `nil`. Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- `refused(who, what, err)` returns (does not panic) when `err` is not `nil`: the request was
refused. -/
abbrev refused.spec : Prop :=
  ∀ (who what : GoString) (err : GoInterface),
  err ≠ GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (App (App (Val (@! client.refused)) (Val #who)) (Val #what)) (Val #err))
  {{ RET #(); True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
