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
mode (`isServerReq` with `⌜E.cmp = true⌝`: the KV invariant admits the compaction entry in the
cluster's compaction mode, S2-1; M2's apply side, item 15, 2026-10-31: until then the compaction
mode's own view, `isServerReqC`; the readers' names the request path's, `ρ.rd`, F5-2: the
proposal's reached revision from the certificates `isServerRead` reaches. Go serves a client's
`Compact` RPC with the auto-compactor off too; such a server's invariant admits no compaction entry,
so a client compaction at an off server stays outside the model, review round 2's S-6): it proposes the
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
recorded by the compaction form of the proposal permit, designed with the model step.) 

**M2's scope restriction** (2026-10-30, the user's Q7 (a), the approval's item 35): the revision is
at least `1`, no compaction at revision `0` (`issues/etcd-restore-scheduled-compact-zero.md`: a
member that applied `Compact(0)` and installs an image with that compaction scheduled but unfinished
goes from compaction revision `0` back to `-1`). A client's `Compact(0)` RPC is out of M2's scope;
M2's compactor never issues it (both of its permits carry `0 < r`: `compactableOk_server`). The
premise is stricter than the decision by a margin (review round 5's S4): it also excludes the
negative revisions, which Go handles harmlessly (`updateCompactRev` answers `ErrCompacted` for
`rev ≤ compactMainRev`, which is at least `-1`, and writes no record); no caller issues one. -/
abbrev EtcdServer.Compact.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (r : Int),
  -- (M2, the storage side, 2026-10-30: M2's scope restriction, the user's Q7 (a), the approval's
  -- item 35) a revision past `0`
  1 ≤ r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ ⌜E.cmp = true⌝ ∗ isServerRead s E ρ.rd ∗ srvLeadTimeReader s ∗
      srvLgReader s ∗ E.RD ∗
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
