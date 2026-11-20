/-
`storage.BackendQuota.Cost`: the trust boundary (`server/v3/storage` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `q.Cost(r)` reads the fields of a put or traverses the operations of a transaction.
The request predicate owns those fields, including the nested requests. A lease grant costs
a constant. The receiver's fields are unused (the capped applier passes a zero quota). -/
abbrev storage.BackendQuota.Cost.spec : Prop :=
  ∀ (q : Loc) (t : go.GoType) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ apply.quotaReqOk t r }}
    (App (Val (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty
      @!! go!"Cost")) (Val #(interface.mkOk t #r)))
  {{ (c : w64), RET #c; True }}

end spec

end EtcdGrove
end Perennial
