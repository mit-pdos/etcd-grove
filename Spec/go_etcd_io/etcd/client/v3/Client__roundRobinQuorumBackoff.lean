/-
`c.roundRobinQuorumBackoff(waitBetween, jitterFraction)` (`client/v3/client.go`, names only:
floats; item 5). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.roundRobinQuorumBackoff(w, j)` on a client `New` builds (`retryClientOk`): a backoff
function that returns (`backoffOk`). -/
abbrev Client.roundRobinQuorumBackoff.spec : Prop :=
  ∀ (c : Loc) (w : time.Duration) (j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"roundRobinQuorumBackoff")) (Val #w)) (Val #j))
  {{ (bf : GoFunc), RET #bf; backoffOk bf }}

end spec

end EtcdGrove
end Perennial
