/-
`s.raftRequest(ctx, r)` (`v3_server.go`): the request's response, or the apply's error. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.raftRequest(ctx, r)` (as `processInternalRaftRequestOnce`): success, the apply thread's
answer to `rq'` (`appliedOk`: dispatched, the apply package's response, no error); failure, no
response and an error (2026-10-14, unit C2a: the success with the result's witness at `ρ.rd`,
`appliedWit`): the apply's (`appliedErr`), or `processInternalRaftRequestOnce`'s (the
proposal, if made, deposited). Unit W-M3: the update's committed log `L` is the raft prefix whose
model is the log `lb` the entry met (`appliedOk`'s `x.log`), and the log after is certified.

**In the environment's auth mode** (the auth-mode merge's step 5, 2026-10-29: one spec,
the mode `E.authOn`; the instances at a mode, `specM`, and the mode-off form, `specOff`, are
corollaries in `ModeSpecs.lean`). The mode views (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): over
`processInternalRaftRequestOnce.specM`; the success post at the committed prefix `L` before the
entry, with what the proposer learns of the model there (`appliedOkM`, `modelOutM`: in the mode `on`
the auth state the entry met and the auth layer's verdict the model's grant there). -/
abbrev EtcdServer.raftRequest.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ irrNoHdrIs p rq ∗ reqPropOkM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq Qh ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel)
          (L : List EntryModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ srvRLogLb ρ.raft L ∗
          appliedOkM E.authOn E ρ rq' F resp L ∗ pubAfterM E.authOn E ρ rq' L ∗ □ Qh hm L ∗
          hdrBoundM E.authOn s E (GoInterface.ok ctx) hm) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err ∗
            hdrBoundM E.authOn s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ rq))) }}

end spec

end EtcdGrove
end Perennial
