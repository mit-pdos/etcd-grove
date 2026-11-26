/-
`(*kv).Get(ctx, key, opts...)` across machines, auth on, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVGetOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
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

/-- **`KV_GetOn_dist`: `(*kv).Get(ctx, key, opts...)` across machines, auth on** (`KV_Get_dist`'s
statement, for an auth-on view, at the principal of `cfg`; a success also names the member `mid` that
served it and its check (`readCheckedD`): its verdict at its published auth index `m`, whose state is the
history's after a requested prefix `L ⊒ L₀` (the barrier's floor, `authFloorD`: a linearizable read's
check is no older than its read index, which is at least every commit before the call), and the
cluster-level `readAuthedD`). Serializable reads are not covered (no workload sends one with auth on):
`serializable = false` is a premise.

**Strengthened before approval** (F7 S5, 2026-11-26, the lead's approval #50 06:35Z; needs a fresh review): `authFloorD` also says every state member `mid` records from the floor's index `i` on is the history's after a committed prefix `L' ⊒ L₀` (`srvReqLogLb γR L'`), the shape `readCheckedD` has after N1 (`f7-getOn-n1.md`'s R1 argument). **Strengthened before approval, again** (F7 S5 review `f7-s5-review.md`, 2026-11-26): that conjunct under an update at a mask holding `authTieReadMask` (§2.2: as a plain wand it was false in the logic), and `outTokOk` covering the `authorization` key too (§1: UNSOUND before, an anonymous caller could send root's token under it).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVGetOnDist.lean`). Reviews (`notes/axiom-review/`): first `f7-a.md` (`d946f6cbda`: UNSOUND, the member names a free binder `A`; fixed by `Γ.au`), then `f7-rerev-a.md` (`6d9d9fd662`): SOUND (condition C), with precision note N1 on `readAuthedD`. **Changed since**: N1 applied (`readCheckedD` gives `srvReqLogLb γR L` at the permitted prefix `L`; a stronger post), not yet reviewed (`f7-changed-since-review.md`). **Re-reviewed** `f7-getOn-n1.md` (2026-11-26): SOUND with N1, given `serializable = false` (keep that
premise). **Retirement obligation R1** (from that review): a lemma that derives the committed `L` from
`authHistTie E ρ srvAuthSt0`: from `authStateAt γa i (srvAuthAtLog L')`, `i ≤ j` and `authStateAt γa j st`,
`∃ L ⊒ L', srvReqLogLb ρ.raft L ∗ ⌜st = srvAuthAtLog L⌝` (generalizing `authStateAt_setup`, `AuthTieRead.lean`,
via `srvReqLogLb_of_rlogLb` and `kvRaftOfOn_eqv`), under an update at a mask holding `authTieReadMask` (it opens
`authTieN`). It needs the **alignment lemma** (`notes/axiom-review/f7-s5-review.md` §2.1): the cap's states
`bootState :: admStates kv st₀ A` are pairwise distinct, because revisions strictly increase along it
(`bootState` has revision 0, `srvAuthSt0 = bump bootState` 1, `admEntry` requires `adminNext rq st ≠ st`, and
every `.next` outcome of `auth/Steps.lean` is a `bump`), so `authStateAt γa i (srvAuthAtLog L)` fixes
`i = |admStates L|`, and every `j > i` is an admin entry after `L`'s end (`L'` the prefix of `A` through it);
without it a history A→B→A would make R1 false. -/
abbrev KV_GetOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAtRes opts_sl opts R ∗ R ∗
      sortNamesIf (opGetModel key opts).base.sortSet ∗
      ⌜¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1 ∧
        (rangeWireOf (opGetModel key opts)).base.serializable = false⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∗
      ⌜opSizeOk (opGetModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗ □ Q σ ∗
          ⌜sint.Z (rangeWireOf (opGetModel key opts)).base.rev ≤ (σ.rev : Int) ∧
            txn.srvRangeOk (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ⌝ ∗
          readCheckedD eps Γ γR (principalOf cfg) L₀ (rangeWireOf (opGetModel key opts))) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝)) }}

/-! ### Admin calls (sent by the set-up's anonymous client; stated for either auth mode of the history) -/

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
