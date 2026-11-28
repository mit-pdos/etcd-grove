/-
`(*kv).Delete(ctx, key, opts...)` across machines, auth on, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVDeleteOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
written in. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`KV_DeleteOn_dist`: `(*kv).Delete(ctx, key, opts...)` across machines, auth on** (mirrors
`client.client_delete_on` at the cluster, in `KV_Delete_dist`'s statement: the update persistent
(`writeAuD`), the principal of `cfg`, a success's grant `writeCheckedD`; the error arm claims nothing).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVDeleteOnDist.lean`). Reviews (`notes/axiom-review/`): `f7-a.md` (`d946f6cbda`) SOUND, `f7-rerev-a.md` (`6d9d9fd662`) SOUND. Unchanged since (`f7-changed-since-review.md`) until 2026-11-27.

**2026-11-27: the request's shape** (weakenings, `notes/axiom-review/onpairs-deleteon.md`, `txnshape-narrowing.md`):
`auth.reqShape` of the caller's key and the range end, and `kvShapeAll (irrDeleteRange …)`, the shape the
permission cache decides on the wire request. Both are kept: over arbitrary option transformers the wire key
need not be `key`, so neither implies the other from the pure premises. The auth-on contract requires it of its
caller: `etcdDeleteSpecOnW`/`etcdDeleteSpecMW` (`Proof/go_etcd_io/etcd/client/v3/KVServiceOn.lean:106`/`:527`),
used by the handler's proof (`Results.lean:1372`), and `client.client_delete_on` takes `key ≠ []`. Without it
the axiom claimed a success for requests no proof covers, and its update applied a delete Go refuses with auth
on (empty or inverted ranges). Callers lose nothing real: etcd refuses an empty key before auth
(`ErrGRPCEmptyKey`), and an inverted range deletes nothing. -/
abbrev KV_DeleteOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ≠ [W8 0] ∧
        auth.reqShape key (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ∧
        kvShapeAll (irrDeleteRange (deleteWireOf (opDeleteModel key opts)))⌝ ∗
      writeAuD Γ.kv (principalOf cfg) (.deleteRange (deleteWireOf (opDeleteModel key opts))) L₀ Q ∗
      ⌜opSizeOk (opDeleteModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts))).length : Int) ∧
          m.prevs = (if (deleteWireOf (opDeleteModel key opts)).base.prevKV then
            rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts)) else []) ∧
          m.hdr.revision =
            W64 ((kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ).rev : Int) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ)⌝ ∗
        writeCheckedD eps Γ γR (principalOf cfg)
          (irrDeleteRange (deleteWireOf (opDeleteModel key opts))) L₀) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
