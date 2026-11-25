/-
`build(name, peer, client, cluster, lg)` (`examples/etcd/restart/restart3.go`; restart3 C2,
2026-11-15): `etcdstart.BuildServer` at `restart3`'s token and snapshot settings
(`SnapCount = SnapCatchUp = 1`). Lean-first (no Rocq counterpart).

**`spec`, a first build:** `etcdstart.BuildServer.spec`'s at those arguments (lease mode `none`): an
error with the thread token, or the member built (`etcdstart.memberBuilt`, its peer address not yet
served) and its data directory.

**`specRestart`, a build after a stop:** `etcdstart.BuildServer.specRestart`'s: from the stopped
member's restart bundle without addresses (its peer address stays served by its `raftSwap`, D-R3-4),
the member built at new names that agree with the stopped ones where the cluster sees them
(`restartNames`).
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
abbrev build.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  etcdstart.addrFits peerAddr → etcdstart.addrFits client →
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  -- (wal-fsfix, 2026-11-20, the user's decision) the member's name at most 200 bytes, so that its data
  -- directory fits (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  name.length ≤ 200 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      zapLoggerOk lg ∗ threadTok ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      etcdstart.bootPremise N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗ etcdstart.memberBoot γ ctxs ρ E₀ Φs id ∗ netHttpOk γn id ∗
      etcdstart.memberFreshRes name {} γn }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.build))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ etcdstart.memberBuilt s ρ E₀ lg γn id N false ∗
          srvDataDir s (memberDataDir name)) }}

/-- See the file header (`specRestart`). -/
abbrev build.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  etcdstart.addrFits peerAddr → etcdstart.addrFits client →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      zapLoggerOk lg ∗ threadTok ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      etcdstart.bootPremiseR N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗ etcdstart.memberRestartRes name {} γn γ ρ id ∗ netHttpOk γn id ∗
      etcdstart.memberRestartFacts γ ρ id ∗ ⌜EtcdVerifyOff⌝ }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.build))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ ∃ (ρ' : ReqNames) (E₀' : apply.AEnv GF),
          ⌜restartNames ρ ρ'⌝ ∗ etcdstart.memberBuiltR s ρ' E₀' lg γn id N false ∗
          srvDataDir s (memberDataDir name)) }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
