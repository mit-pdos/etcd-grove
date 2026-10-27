/-
`EtcdServer.Compact` (`v3_server.go`): the auto-compactor's `Compactable` (the spec-first pilot,
`notes/compactor-pilot-plan.md`, phase 1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Compact(ctx, r)` for a non-physical compaction request at a revision `r` the store has
reached (`v3compactor.revLb`: what both of C1's permits give): it proposes the compaction through
raft and returns, giving back the caller's reader slots. (Phase 1's statement: what the apply does
with the compaction is the server side's model step, C2/C3, not stated yet; the compactor ignores
`Compact`'s result.) -/
abbrev EtcdServer.Compact.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (r : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      v3compactor.compactReqIs p r ∗ v3compactor.revLb E.γ.idx r }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD }}

end spec

end EtcdGrove
end Perennial
