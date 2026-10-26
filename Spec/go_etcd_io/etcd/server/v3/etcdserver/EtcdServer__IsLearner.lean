/-
`s.IsLearner()` (`server.go`; names-only, the trust boundary of unit P3b, until D43 M4,
2026-10-26: translated over the cluster's `IsLocalMemberLearner`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.IsLearner()` (`s.cluster.IsLocalMemberLearner()`: the local member's `IsLearner`, read
under the cluster's mutex, `isRaftCluster`) returns some boolean. (Until D43 M4, 2026-10-26, given
that the local member is in the members map, `membership.localKept`: `IsLocalMemberLearner`
panicked otherwise; the fork's fix returns `false`.) -/
abbrev EtcdServer.IsLearner.spec : Prop :=
  ∀ (s c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"IsLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
