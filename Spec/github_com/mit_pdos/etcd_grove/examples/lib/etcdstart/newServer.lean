/-
`newServer(name, peer, client, cluster, token, retention, snapCount, catchUp, lg)` (`examples/lib/etcdstart/common.go`; 2026-10-22, D33):
member `name` of a new cluster with token `token` built -- its configuration (as putget's, putget3's
and their followers' were) and `etcdserver.NewServer`. Lean-first (no Rocq counterpart).

**The triple:** given the member's ghost state (`memberBoot`, `alloc1`'s or `alloc3`'s) and the
network's HTTP side for it (`netHttpOk`), its URLs read-only (the peer URL slice `[http://peerAddr]`, the initial cluster's map `M` with
each member's peer URL slice, its initial URLs by name `iu`), `bootstrap`'s contract for it
(`bootPremise`, whose URLs predicate `Uok` the configuration's URLs meet) and the premises the
members share: an error, or the server built (`memberBuilt`).

The snapshot settings (`snapCount`, `catchUp`) are any: `NewServer`'s spec has no premise on
them since 2026-10-30 (snapshots allowed).
**The pure premises:** the logic's thread bound and the time-receipt
bounds; the server's raft names of the cluster (its peers `ps`, static, its bootstrap log), the log
shorter than `2 ^ 60`, the network's payload the server's and its directory `dir`; the logger not
`nil`; the auto-compactor off (the retention zero), in either compaction mode `cmp` (compaction
mode with every compaction a client's: Kubernetes' deployment); the named effect premises of the server's
construction.

(Until 2026-11-05 also `specCompact`, the auto-compactor on in revision mode: proved, used by no
proof and not linked; deleted by hub step 7, Q2: `newServerMode.spec` covers it.)

**`specRestart`** (restart S7.4, 2026-11-14): `newServerMode.specRestart` without the mode (revision
mode, the retention `0`): the member started again on its stopped data directory, built at new names.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Perennial.ProgramLogic.Bounds
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor

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
abbrev newServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool)
    (lm : lease.Mode),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  addrFits peerAddr → addrFits client →
  -- (2026-11-02, the backend-auth-split stage, Q8) the initial cluster's names valid UTF-8,
  -- `bootPremise`'s condition
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  -- (wal-fsfix, 2026-11-20, the user's decision) the member's name at most 200 bytes, so that its data
  -- directory fits (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  name.length ≤ 200 →
  retention = W64 0 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its start bundle) the
      -- member's WAL directory fresh: a first start
      memberFreshRes name {} γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #retention))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false (m := lm) ∗
          leaseTTLRowR s ps ∗
          -- (R2c-5) the data directory, the name's `.etcd`, with no dedicated WAL directory
          -- (`srvDataDir`, the slot's: `srvStop.dataDir`), which a stop request carries
          srvDataDir s (memberDataDir name)) }}

/-- **`spec` with `bootstrap`'s contract borrowing a frame `R`** (2026-11-27, restartN's first boots): the
member's `bootPremiseF R` in place of `bootPremise`, `R` in the precondition and given back in the post, on every
path (`NewServer.specGAtA`'s frame). -/
abbrev newServer.specF : Prop :=
  ∀ (N : Nat) (name peerAddr client token : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool)
    (lm : lease.Mode)
    (R : IProp GF),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  addrFits peerAddr → addrFits client →
  -- (2026-11-02, the backend-auth-split stage, Q8) the initial cluster's names valid UTF-8,
  -- `bootPremise`'s condition
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  -- (wal-fsfix, 2026-11-20, the user's decision) the member's name at most 200 bytes, so that its data
  -- directory fits (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  name.length ≤ 200 →
  retention = W64 0 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ R ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremiseF R N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its start bundle) the
      -- member's WAL directory fresh: a first start
      memberFreshRes name {} γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #retention))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err); R ∗ (
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false (m := lm) ∗
          leaseTTLRowR s ps ∗
          -- (R2c-5) the data directory, the name's `.etcd`, with no dedicated WAL directory
          -- (`srvDataDir`, the slot's: `srvStop.dataDir`), which a stop request carries
          srvDataDir s (memberDataDir name))) }}

/-- **`specAt`** (F7 step 2): `spec` with the member's lessor at the caller's name `γl`
(`newServerMode.specAt`'s): the slot's half in the pre, `memberBuiltL` in the post. -/
abbrev newServer.specAt : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool)
    (lm : lease.Mode) (γl : GName),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  addrFits peerAddr → addrFits client →
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  name.length ≤ 200 →
  retention = W64 0 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ (ghostMapAuth γl (1 : Qp).half (∅ : GMap Bool lease.LessorGV) ∗ lease.lessorSlot γl) ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      netHttpOk γn id ∗
      memberFreshRes name {} γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #retention))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuiltL s ρ E₀ lg γn id N false lm γl ∗
          leaseTTLRowR s ps ∗
          srvDataDir s (memberDataDir name)) }}


/-- See the file header (`specRestart`). -/
abbrev newServer.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  addrFits peerAddr → addrFits client →
  retention = W64 0 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremiseR N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗
      memberRestartRes name {} γn γ ρ id ∗ netHttpOk γn id ∗
      memberRestartFacts γ ρ id ∗ ⌜EtcdVerifyOff⌝ }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #retention))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ ∃ (ρ' : ReqNames) (E₀' : apply.AEnv GF),
          ⌜restartNames ρ ρ'⌝ ∗ memberBuiltR s ρ' E₀' lg γn id N false ∗
          srvDataDir s (memberDataDir name)) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
