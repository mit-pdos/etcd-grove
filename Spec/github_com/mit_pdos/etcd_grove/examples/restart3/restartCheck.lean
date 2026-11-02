/-
`restartCheck(cli, m, name, peer, peerAddr, client, cluster, lg)` (`examples/restart3/restart3.go`;
the restart plan's R2, 2026-11-02; DRAFT): the member `m` stopped, `NPuts` puts of `k ↦ v2` through
`cli`, the member started again on its data directory and its gRPC API served at `client`, a client
of it, a `Get` of `k` through it, and a panic unless the `Get` returned `v2`. Lean-first (no Rocq
counterpart).

**The triple:** from a started member that can be stopped (`memberStop` and its request view
`isServerReq` at the names `ρ`), what `startMember.specRestart` needs besides the image and the
peer address the stop gives back (`bootstrap`'s restart contract, the URLs, the member's place in
the network), the right to listen on its client address, a thread token, and `New`'s client `cl`
of another member (`ep`, its registrations `kvRegsAt` at the read names `γr`) under the client's
invariant for `k ↦ v2` (`client.putGetInv`) at a KV state the stopped member's names share
(`ρ.rd.kv.st = γr.kv.st`): `restartCheck` returns, so it did not panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.put
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- See the file header. -/
abbrev restartCheck.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) (E₁ : apply.AEnv GF) (γr : ReadNames)
    (γf : GName) (cid mid : w64)
    (m s : Loc) (pl : GoInterface) (E : apply.AEnv GF) (ρ : ReqNames)
    (N : Nat) (name peerAddr caddr : GoString) (peer : GoSlice) (cluster lg : Loc)
    (M : GMap GoString GoSlice) (iu : GoString → List _root_.Perennial.net.url.URL)
    (Uok : BootURLs → Prop) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (id : w64) (γ : SrvRaft) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  ρ.rd.kv.st = γr.kv.st →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[common.httpURL peerAddr], [common.httpURL caddr], M, iu⟩ →
  plainEndpoint caddr → lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      memberStop m s pl γ id peerAddr γn (name ++ go!".etcd") ∗ isServerReq s E ρ ∗
      isNewClient cl [ep] V ∗ client.kvRegsAt (⟨ep, E₁, γr, cid, mid⟩ : client.SrvAt GF) ∗
      client.putGetInv γr γf go!"k" go!"v2" ∗
      netAddrFree (GF := GF) caddr ∗ threadTok ∗
      peer ↦*□ [common.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      common.bootPremiseR N ps bootLog ctxs dir token name Uok id ∗ common.commonPremises ∗
      context.isClosedchanInit ∗ netHttpOk γn id }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.restartCheck))
      (Val #cl)) (Val #m)) (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #caddr))
      (Val #cluster)) (Val #lg))
  {{ RET #(); True }}

end spec

end restart3
end EtcdGrove
end Perennial
