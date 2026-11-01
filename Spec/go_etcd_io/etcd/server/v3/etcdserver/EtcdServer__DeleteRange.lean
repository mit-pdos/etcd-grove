/-
`s.DeleteRange(ctx, r)` (`v3_server.go`): a delete through raft and the apply thread. Lean-first
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

/-- **`s.DeleteRange(ctx, r)`**, **in the environment's auth mode** (`E.authOn`; `Put.spec`'s,
the auth-mode merge's step 5): the delete's permission `deletePermitM` (off, its range end not
`[0]` and the client's update fired at most once; on, also the key and range end of the permission
cache's shape, the update told its grant); success, the apply package's answer to the wire request
`rq'` (`deleteOutcomeIs`), its result `Q` at the log the entry met, with auth on the header bound
to the context and the grant at the committed log before the entry; failure, the apply's error or
the proposal's. Its former specs are instances (`DeleteRange.spec_off`, `DeleteRange.spec_on`). -/
abbrev EtcdServer.DeleteRange.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op ∗ deletePermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ (∃ log', o = .applied log' false) ∧
            F <+: x.log⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log) ∗ hdrBoundM E.authOn s E (GoInterface.ok ctx) hm ∗
          □ (⌜E.authOn = true⌝ → ∃ L, ⌜grantedAt ρ.kv srvAuthSt0 rq' L⌝ ∗ pubAfterM true E ρ rq' L)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' F err ∗
            hdrBoundM E.authOn s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}

end spec

end EtcdGrove
end Perennial
