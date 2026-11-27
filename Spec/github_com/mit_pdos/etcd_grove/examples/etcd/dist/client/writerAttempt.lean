/- Lean-first (no Rocq counterpart).

`writerAttempt(nops)` (`examples/etcd/dist/client/nodes.go`): how long one writer call may take,
`nops * RequestTimeout + 30s` (a duration; Go's arithmetic wraps, so it never panics). #50 N10a.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev writerAttempt.spec : Prop :=
  ∀ (nops : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt)) (Val #nops))
  {{ (d : w64), RET #d; True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
