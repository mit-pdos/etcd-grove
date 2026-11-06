/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/etcd/restart/restart3.go`; the
restart plan's R2a, 2026-11-02; DRAFT): member `name` of `restart3`'s cluster built
(`etcdstart.BuildServer` at the snapshot settings), its raft handler served on a listener at
`peerAddr`, and the server started. Lean-first (no Rocq counterpart).

**`spec`, a first start:** `etcdstart.StartMember`'s, but the server built by `BuildServer.spec` (R2c-5;
until then a draft `specStop`), its cluster's names valid UTF-8, and the peer listener registered closable: an error (with the thread token), or the started member
(`etcdstart.memberUp`) and a stoppable member's record (`memberStop`).

**`specRestart`, a start after a stop** (R2c, R2d): the same, from the data directory the stop left
(`srvDiskImage`, at the stopped incarnation's names `ρ`), the peer address and its protocol's right,
as the stop gave them back (`etcdstart.memberRestartRes`), and `bootstrap`'s restart contract
(`etcdstart.bootPremiseR`): the
member started at new names `ρ'` that agree with `ρ` where the cluster sees them (`restartNames`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  -- (R2c-5) the initial cluster's names valid UTF-8 (`BuildServer.spec`'s, `bootPremise`'s condition)
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      threadTok ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      etcdstart.bootPremise N ps bootLog ctxs dir token name Uok id ∗ etcdstart.commonPremises ∗
      context.isClosedchanInit ∗
      etcdstart.memberBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id ∗
      -- (hub step 8, E3) the member's fresh bundle with its peer address: a first start
      etcdstart.memberFreshRes name ⟨some peerAddr, none⟩ γn }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (s : Loc) (pl : GoInterface),
        etcdstart.memberUp s ρ E₀ lg γn id ∗ memberStop m s pl γ id peerAddr γn ρ (name ++ go!".etcd")) }}

/-- See the file header (`specRestart`). -/
abbrev startMember.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      threadTok ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      etcdstart.bootPremiseR N ps bootLog ctxs dir token name Uok id ∗ etcdstart.commonPremises ∗
      context.isClosedchanInit ∗
      netHttpOk γn id ∗
      -- (hub step 8, E4) the member's restart bundle with its peer address: what its stop gave back
      etcdstart.memberRestartRes name ⟨some peerAddr, none⟩ γn γ ρ id }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (s : Loc) (pl : GoInterface) (ρ' : ReqNames)
        (E₀' : apply.AEnv GF), ⌜restartNames ρ ρ'⌝ ∗
        etcdstart.memberUp s ρ' E₀' lg γn id ∗ memberStop m s pl γ id peerAddr γn ρ' (name ++ go!".etcd")) }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
