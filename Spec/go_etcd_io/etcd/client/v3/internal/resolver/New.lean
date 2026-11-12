/-
`resolver.New(endpoints...)` (`client/v3/internal/resolver`, names only; item 5): etcd's manual
resolver over the endpoints. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `resolver.New(eps...)` of the endpoints `eps` (read-only): a non-nil resolver, not yet
dialed, with them (`etcdResolverOwn`). -/
abbrev resolver.New.spec : Prop :=
  ∀ (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗
      sl ↦*□ eps }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.resolver.New)) (Val #sl))
  {{ (r : Loc), RET #r; ⌜r ≠ null⌝ ∗ etcdResolverOwn r eps }}

end spec

end EtcdGrove
end Perennial
