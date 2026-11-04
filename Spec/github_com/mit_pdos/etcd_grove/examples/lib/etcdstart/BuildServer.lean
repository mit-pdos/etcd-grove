/-
`BuildServer(name, peer, client, cluster, token, snapCount, catchUp, lg)`
(`examples/lib/etcdstart/etcdstart.go`; 2026-11-02, the restart plan's R2a): member `name` of a new cluster
with token `token` built, serving nothing -- `newServer` with the auto-compactor off -- for an
example that keeps its listeners (`examples/etcd/restart`). Lean-first (no Rocq counterpart).

**The triple:** `newServer.spec`'s at retention `0` (a first start: `bootstrap`'s contract describes
a new cluster's first start), at any snapshot settings.

**`specStop`** (DRAFT, R2b): `spec`'s, with the server's data directory recorded (`srvDataDir`,
the name's `.etcd`) and what it keeps for the stop (`srvStopKeep`), from which `Start` gives the
right to stop it (`etcdstart.Start_builtS_spec`;
R2b-2, 2026-11-02: until then the right itself, `srvStopRight`, `NewServer`'s to give; `start`
makes the channels it names).

**`specRestart`** (DRAFT, R2c and R2d): member `id` started again on the data directory its last
stop left (`srvDiskImage`, at the stopped incarnation's names `ρ`), `bootstrap`'s restart contract
(`bootPremiseR`) in place of a first start's: the member built at its image's starting index
(`memberBuiltR`) at new names `ρ'` that agree with `ρ` where the cluster sees them
(`restartNames`) and a new stand-in environment `E₀'`, with its data directory recorded, from
which `Start` gives the right to stop it again (R2b-2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev BuildServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (2026-11-02, the backend-auth-split stage, Q8) the initial cluster's names valid UTF-8,
  -- `bootPremise`'s condition
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id (m := lm) ∗
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6) the member's WAL directory fresh: a first start
      walDirFresh (config.walDirOf (name ++ go!".etcd") go!"") }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false (m := lm)) }}

/-- See the file header (`specStop`). -/
abbrev BuildServer.specStop : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id (m := lm) ∗
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6) the member's WAL directory fresh: a first start
      walDirFresh (config.walDirOf (name ++ go!".etcd") go!"") }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false (m := lm) ∗
          srvDataDir s (name ++ go!".etcd") ∗ srvStopKeep s) }}

/-- See the file header (`specRestart`). -/
abbrev BuildServer.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
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
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremiseR N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      srvDiskImage γ ρ id (name ++ go!".etcd") ∗ netHttpOk γn id }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ ∃ (ρ' : ReqNames) (E₀' : apply.AEnv GF),
          ⌜restartNames ρ ρ'⌝ ∗ memberBuiltR s ρ' E₀' lg γn id N false ∗ srvDataDir s (name ++ go!".etcd") ∗ srvStopKeep s) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
