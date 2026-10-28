/-
`EtcdServer.Compact` (`v3_server.go`): the auto-compactor's `Compactable` (the spec-first pilot,
`notes/compactor-pilot-plan.md`, phase 1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactMode
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.CompactReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- What `Compact` returns: `nil` and a response whose header holds a revision the store has reached
(`s.kv.Rev()`, the call's last line), or an error the server's request path can report
(`applyErrIs`, which `errors.Is` can test: the compactor's `ErrCompacted` check). -/
def compactOutIs (E : apply.AEnv GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (v : etcdserverpb.ResponseHeader)
      (log : mvcc.Log), structFieldRef etcdserverpb.CompactionResponse go!"Header" resp ↦ h ∗ h ↦ v ∗
      mvcc.idxCert E.γ.idx log ∗ ⌜log ≠ [] ∧ v.Revision' = W64 ((log.length : Int) - 1)⌝) ∨
    (⌜resp = null⌝ ∗ applyErrIs err))

/-- `s.Compact(ctx, r)` for a non-physical compaction request (the pilot's scope: the compactor never
sets `Physical`; the physical wait, `Physc` and `ForceCommit`, is the gRPC caller's and not specified
yet) at a revision the store has reached (`srvRevLb`: the apply's `store.Compact` needs its
certificate, M2's review round 1, S2-3; the compactor's permit gives it), on a server in compaction
mode (`isServerReqC`: its KV invariant admits the compaction entry, S2-1): it proposes the
compaction through raft and returns `compactOutIs`, under a context carrying no trace (`traceutil.ctxTraceIs ctx
none`: `traceutil.EnsureTrace` reads `ctx.Value(TraceKey{})` and writes to a trace it finds; M2's
freeze repair, `notes/decisions.md`, "The compactor's contract after the freeze"),
giving back the caller's reader slots (the lead-time and logger mutexes', `E.RD`; the logger's and
the server's read facts, `isServerRead`, for `s.Logger()` and `s.kv.Rev()`: M2's S3 glue, which the
pilot's statement lacked) and the store's compaction-aware reader (`storeReaderC`: the
call's last line reads `s.kv.Rev()`).
(Phase 1's statement: what the apply does with the compaction, C2/C3, is not stated yet. The
compactor's C1 permit stops here until then: a per-call permit parameter would be vacuous, since each
caller picks it (round 3 of the review); C3 needs a server-wide permit, fixed at `NewServer` and
recorded by the compaction form of the proposal permit, designed with the model step.) -/
abbrev EtcdServer.Compact.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (r : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqC s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗
      mvcc.storeReaderC E.s E.γ ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx none ∗ srvRevLb E.γ r ∗
      compactReqIs p r }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗
      srvLgReader s ∗ E.RD ∗ mvcc.storeReaderC E.s E.γ ∗ compactOutIs E resp err }}

end spec

end EtcdGrove
end Perennial
