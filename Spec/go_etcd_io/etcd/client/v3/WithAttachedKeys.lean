/-
`clientv3.WithAttachedKeys()` (`client/v3/op.go`; auth-lease S4, translated for the authlease checks'
`TimeToLive` with keys). Lean-first (no Rocq counterpart); see `InvLeaseRead.lean`'s `leaseOptSpec`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithAttachedKeys()`: a lease option setting `attachedKeys`. -/
abbrev WithAttachedKeys.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithAttachedKeys)) (Val #()))
  {{ (f : GoFunc), RET #f; leaseOptSpec f (fun _ => true) }}

end spec

end EtcdGrove
end Perennial
