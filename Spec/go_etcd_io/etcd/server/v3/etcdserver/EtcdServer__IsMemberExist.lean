/-
`s.IsMemberExist(id)` (`server.go`, names-only: the trust boundary of unit P3b). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.IsMemberExist(id)` (`s.cluster.IsMemberExist(id)`: the members map looked up under the
cluster's mutex, `isRaftCluster`) returns some boolean. -/
abbrev EtcdServer.IsMemberExist.spec : Prop :=
  ∀ (s c : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"IsMemberExist")) (Val #id))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
