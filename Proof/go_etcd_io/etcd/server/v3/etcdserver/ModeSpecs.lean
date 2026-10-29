/-
**The server's mode variants of its merged specs** (the auth-mode merge,
`notes/auth-mode-merge-plan.md`, 2026-10-29): a merged spec is one statement for both auth modes,
the mode the environment's (`E.authOn`); for each, until its callers are merged too, the
statements of the two modes as they were (`specOff`, with the premise `E.authOn = false`, and
`specOn`, with `E.authOn = true`) and their corollaries `spec_off`/`spec_on` (no second proof:
`.claude/skills/spec/PRINCIPLES.md`, "One spec per function"). Each goes when no caller uses it.

The request path (step 5, 2026-10-29): `parseProposeCtxErr`, `processInternalRaftRequestOnce`,
`raftRequest`, `doSerialize`. Their proofs are over the mode `on` (`wp_proofM on`), so their
variants are `<F>.specM on` (the proposer's view `isServerReqM on` fixes `E.authOn = on`,
`isServerReqM_authOn`; `<F>.spec_M : <F>.spec → <F>.specM on`) and, for the mode-off proofs of
`Put`, `DeleteRange`, `Range` and `Txn` not merged yet, `<F>.specOff`, the mode-off statement before
the merge (over `isServerReq`, `reqPropOk`, the result at `kvModel`; `<F>.spec_off`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__parseProposeCtxErr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section variants
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## `snapshotIfNeededAndCompactRaftLog` -/

/-- **`spec` with auth off** (a corollary, `spec_off`): the off row (`srvApplyKV`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (γp : GName) (w : Nat),
  E.authOn = false →
  loopOk γ st ai →
  1 ≤ γs.cap →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1) the storage's floor past the applied index (`raftAdvancedC`'s)
      memFloorAtLeast ms γs (uint.Z ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`spec` with auth on** (a corollary, `spec_on`; the auth plan's E3p, 2026-10-27): the row with the
auth part at the model's auth state `sa` (`srvApplyKVOn`), kept (`snapshot` takes only the part both
rows share, `srvApplyKVCore`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (γp : GName) (w : Nat)
    (sa : auth.AuthState),
  E.authOn = true →
  loopOk γ st ai →
  1 ≤ γs.cap →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1) the storage's floor past the applied index (`raftAdvancedC`'s)
      memFloorAtLeast ms γs (uint.Z ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`specOff`**, `spec` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_off
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specOff (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w hoff
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w srvAuthSt0
  rw [hoff] at this
  exact this

/-- **`specOn`**, `spec` with the mode-`on` row (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_on
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w sa hon
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w sa
  rw [hon] at this
  exact this


end variants

/-! ## The request path -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`spec` in either auth mode** (the auth plan's E3b, 2026-10-26): the server as a proposer sees
it in the auth mode `on` (`isServerReqM`; the function reads none of the mode's rows). At
`on = false` it is `spec` (by definition). -/
abbrev EtcdServer.parseProposeCtxErr.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (err : GoInterface) (start : time.Time),
  context.isTypedErr err →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗
      (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"parseProposeCtxErr"))
      (Val #err)) (Val #start))
  {{ (e : GoInterface), RET #e; srvLeadTimeReader s ∗ ⌜e ≠ GoInterface.nil⌝ ∗ applyErrIs e }}

/-- **The handoff in either auth mode** (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): `spec`'s,
with the proposer's view of the server, the wait's results and the KV model of the mode
(`isServerReqM`; the applied result `resPostM`: in the mode `on` with the auth state the entry met
and the auth layer's verdict the model's grant there, `authTie`), and the proposal's permission at the header the server stamps
(`reqPropOkM`: in the mode `on` the check reads the request's principal, which the server fills in
from the context before it proposes; the result `Qh hm` is at that header `hm`, the one the post
names); (E3t, 2026-10-27) with auth on, the auth state after the entry published (`pubAfterM`);
(E3zb, 2026-10-28) with auth on, the stamped header's user bound to the context (`hdrBoundM`: the
store's `AuthInfoFromCtx` reads the context's token, `srvAuthBound` in `isServerReqM true`). At
`on = false` it is `spec` (`EtcdServer.processInternalRaftRequestOnce.wp_proof` is
derived from it, a constant `Qh`). -/
abbrev EtcdServer.processInternalRaftRequestOnce.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ irrNoHdrIs p rq ∗ reqPropOkM on ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq Qh ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ resPostM on E ρ rq' F res L ∗
            pubAfterM on E ρ rq' L ∗ □ Qh hm L ∗ hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

/-- **The handoff.** `s.processInternalRaftRequestOnce(ctx, r)`, any goroutine, at a context, for
a request `r` holding `rq` but for its header (which it sets: the fresh id `Next` returns, the
auth info's user name and revision), with no `ID` (the server's requests have none; `Apply` takes
the header's), one id credit, a reader slot of `s.leadTimeMu` and (2026-10-14, unit A2) the auth store's reader
resource `E.RD` (`AuthInfoFromCtx`):
* success (`err = nil`): `res` is the apply thread's result of applying `rq'`, the request the
  proposed data decode to (`irrWireOf`: `rq` with its header, up to the model's `[0]` range ends):
  `resultIs E rq' res` (the apply package's `applyStep` and `applyResultIs` at the KV state the
  entry met, and mvcc's certificate of the log after; 2026-10-14, unit C2a: `resultIsW E ρ.rd`, with
  the witness that the log after is applied through an index of the committed log, `appliedWit`);
  and (2026-10-14, unit T1) the result `Qr` of the proposal's update at a committed log (`reqPropOk
  ρ.kv rq Qr`: the request has no KV write, `Qr` trivial; or, since 2026-10-15 (unit T2), it is a
  plain write, a put, a delete or a transaction, with its client's update over the whole state,
  `Qr L` the client's `□ Q` at the state of `L`'s model): `□ Qr L` of the committed log `L` before
  the entry the result is of, whose model is the log `lb` the entry met (unit W-M3: the result's
  `y.log`, so the update's state is the write's);
* failure: no result, an error the gRPC layer can take (`applyErrIs`: in an error tree, a safe map
  key, with a message; 2026-10-12, unit 3a), and the proposal, if made, deposited (`srvMaybeDeposited`: it may
  still be applied: the request limit, the auth store's error, the marshal's error, the size
  limit come before the proposal; `Propose`'s error, the context's (`parseProposeCtxErr`) and the
  server's stop (`ErrStopped`) after it). -/
abbrev EtcdServer.processInternalRaftRequestOnce.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ lb : mvcc.Log, resultIsW E ρ.rd rq' F res lb ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

/-- **`spec` in either auth mode** (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): over
`processInternalRaftRequestOnce.specM`; the success post at the committed prefix `L` before the
entry, with what the proposer learns of the model there (`appliedOkM`, `modelOutM`: in the mode `on`
the auth state the entry met and the auth layer's verdict the model's grant there). -/
abbrev EtcdServer.raftRequest.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ irrNoHdrIs p rq ∗ reqPropOkM on ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq Qh ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel)
          (L : List EntryModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ srvRLogLb ρ.raft L ∗
          appliedOkM on E ρ rq' F resp L ∗ pubAfterM on E ρ rq' L ∗ □ Qh hm L ∗
          hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err ∗
            hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ rq))) }}

/-- `s.raftRequest(ctx, r)` (as `processInternalRaftRequestOnce`): success, the apply thread's
answer to `rq'` (`appliedOk`: dispatched, the apply package's response, no error); failure, no
response and an error (2026-10-14, unit C2a: the success with the result's witness at `ρ.rd`,
`appliedWit`): the apply's (`appliedErr`), or `processInternalRaftRequestOnce`'s (the
proposal, if made, deposited). Unit W-M3: the update's committed log `L` is the raft prefix whose
model is the log `lb` the entry met (`appliedOk`'s `x.log`), and the log after is certified. -/
abbrev EtcdServer.raftRequest.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (lb : mvcc.Log),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedOk E ρ.rd rq' F resp lb ∗
          ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ rq))) }}

/-- **`spec` in the auth mode `on`** (the auth plan's E3s, 2026-10-27): over the request and read
views in the mode (`isServerReqM on`, `isServerReadM on`; `spec` at `on = false`, by definition).
`doSerialize` reads only fields both modes share. With auth on (E3zb, 2026-10-28) the auth info
`chk` passed on is the caller's (`infoBoundM`: the empty one, or bound to the context's token),
given `AuthInfoFromCtx`'s binding with auth on (`AuthInfoFromCtx.spec`). -/
abbrev EtcdServer.doSerialize.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ isServerReadM on s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info ∗ infoBoundM on s E (GoInterface.ok ctx) info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}

/-- **`s.doSerialize(ctx, chk, get)`** at a context, with the permission check `chk` (a triple:
on any auth info, an error the gRPC layer can take) and the read `get` (`{G} get() {Q}`): the
request's auth info (`AuthInfoFromCtx`, or an empty one), `chk` of it, `get()`, then the
token's revision against the auth store's (`ErrAuthOldRevision`). Success: `get` ran (`Q`);
failure: an error the gRPC layer can take, and `get` ran or not (`G ∨ Q`). 2026-10-14 (unit A2):
the auth store's reader resource `E.RD`, which `AuthInfoFromCtx` and `chk` take and give back.
2026-10-23 (auth plan A1): `C info`, what a passed `chk` establishes of the auth info it saw (the
permission class of the request's keys, `apply.rangeClass`, `apply.txnClass`); success gives it
of some auth info (the context's, or the empty one). -/
abbrev EtcdServer.doSerialize.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}

end specs

/-! ## The instances from the spec -/

section corollaries
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.parseProposeCtxErr.spec_M
    (h : EtcdServer.parseProposeCtxErr.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.parseProposeCtxErr.specM (GF := GF) (hG := hG) on := by
  intro s E ρ err start Herr
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ err start Herr) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.processInternalRaftRequestOnce.spec_M
    (h : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.processInternalRaftRequestOnce.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ ctx cd p rq Qh F Hid0) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.raftRequest.spec_M
    (h : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.raftRequest.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ ctx cd p rq Qh F Hid0) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.doSerialize.spec_M
    (h : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.doSerialize.specM (GF := GF) (hG := hG) on := by
  intro s E ρ γr ctx cd chk get G Q C t e
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ γr ctx cd chk get G Q C t e) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

/-- The mode-off handoff from the spec (a constant result; the success post's model fact
`kvModel L = y.log`). -/
theorem EtcdServer.processInternalRaftRequestOnce.spec_off
    (h : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG)) :
    EtcdServer.processInternalRaftRequestOnce.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.processInternalRaftRequestOnce.spec_M h false
  intro s E ρ ctx cd p rq Qr F Hid0
  iintro %Φ Hpre HΦ
  iapply (hM s E ρ ctx cd p rq (fun _ => Qr) F Hid0) $$ [Hpre] [HΦ]
  · icases Hpre with ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
    ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr $$ Hok
    rw [isServerReqM_false]
    iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  · iintro !> %res %err ⟨Hrd, Hard, Hpost⟩
    iapply HΦ
    iframe Hrd Hard
    icases Hpost with (⟨%He, %hm, %rq', %Hw, HTr, %L, #HL, Hp, -, #HQ, -⟩ | Herr)
    · ileft
      isplitr
      · ipureintro; exact He
      iexists hm, rq'
      iframe HTr
      isplitr
      · ipureintro; exact Hw
      iunfold resPostM at Hp
      icases Hp with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, -⟩
      iexists y.log
      iunfold resultIsW
      isplitl [Hr1 Hr2 Hr3 Hr4 Hr5]
      · isplitr
        · ipureintro; exact Hnn
        iexists y, y', out
        iframe Hr1 Hr2 Hr3 Hr4 Hr5
        ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
      iexists L
      iframe HL HQ
      ipureintro; exact Hst.2.2.2
    · iright; iexact Herr

/-- The mode-off `raftRequest` from the spec. -/
theorem EtcdServer.raftRequest.spec_off
    (h : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.raftRequest.spec_M h false
  intro s E ρ ctx cd p rq Qr F Hid0
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
  ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr $$ Hok
  rw [← isServerReqM_false]
  iapply (hM s E ρ ctx cd p rq (fun _ => Qr) F Hid0) $$ [Ha Hb Hc Hd He Hf Hg Hok' Hi Hj] [HΦ]
  · iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  iintro !> %resp %err ⟨Hrd, Hard, Hpost⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hpost with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hok, -, #HQ, -⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hst, Ha1, Ha2, Ha3, Ha4, Ha5, -⟩
    iexists hm, rq', x.log
    isplitr
    · ipureintro; exact Hw
    isplitl [Ha1 Ha2 Ha3 Ha4 Ha5]
    · iunfold appliedOk
      iexists x, x', o, skip
      iframe Ha1 Ha2 Ha3 Ha4 Ha5
      ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
    iexists L
    iframe HL HQ
    ipureintro; exact Hst.2.2.2.1
  · iright
    icases Herr with ⟨%Hr, #HaE, (⟨%hm, %rq', %Hw, Ha, -⟩ | Hdep)⟩
    · iframe HaE
      isplitr
      · ipureintro; exact Hr
      ileft; iexists hm, rq'; iframe Ha; ipureintro; exact Hw
    · iframe HaE Hdep
      ipureintro; exact Hr

/-- The mode-off `doSerialize` from the spec (the auth info's binding dropped). -/
theorem EtcdServer.doSerialize.spec_off
    (h : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) :
    EtcdServer.doSerialize.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.doSerialize.spec_M h false
  intro s E ρ γr ctx cd chk get G Q C t e
  iintro %Φ Hpre HΦ
  iapply (hM s E ρ γr ctx cd chk get G Q C t e) $$ %Φ [Hpre]
  · rw [isServerReqM_false, isServerReadM_false]; iexact Hpre
  inext
  iintro %err ⟨Hrd, Hres⟩
  iapply HΦ
  iframe Hrd
  icases Hres with (⟨%He, ⟨%info, HC, -⟩, HQ⟩ | Hr)
  · ileft; iframe HQ; isplitr
    · ipureintro; exact He
    · iexists info; iexact HC
  · iright; iexact Hr

end corollaries

end EtcdGrove
end Perennial
