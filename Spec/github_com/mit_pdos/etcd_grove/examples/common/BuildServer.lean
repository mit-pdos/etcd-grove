/-
`BuildServer(name, peer, client, cluster, token, snapCount, catchUp, lg)`
(`examples/common/common.go`; 2026-11-02, the restart plan's R2a): member `name` of a new cluster
with token `token` built, serving nothing -- `newServer` with the auto-compactor off -- for an
example that keeps its listeners (`examples/restart3`). Lean-first (no Rocq counterpart).

**The triple:** `newServer.spec`'s at retention `0` (a first start: `bootstrap`'s contract describes
a new cluster's first start), at any snapshot settings.

**`specStop`** (DRAFT, R2b): `spec`'s, with the right to stop the server once started
(`srvStopRight`, `NewServer`'s to give).

**`specRestart`** (DRAFT, R2c and R2d): member `id` started again on the data directory its last
stop left (`srvDiskImage`): `bootstrap`'s restart contract (`bootPremiseR`) and the restart's boot
bundle (`srvRestartBoot`) in place of a first start's, the member built at its image's starting
index (`memberBuiltR`), with the right to stop it again.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Restart
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev BuildServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ memberBuilt s ρ E₀ lg γn id N false) }}

/-- See the file header (`specStop`). -/
abbrev BuildServer.specStop : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ memberBuilt s ρ E₀ lg γn id N false ∗ srvStopRight s γ id) }}

/-- See the file header (`specRestart`). -/
abbrev BuildServer.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremiseR N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      srvDiskImage γ id ∗ srvRestartBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.BuildServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ memberBuiltR s ρ E₀ lg γn id N false ∗ srvStopRight s γ id) }}

end spec

end common
end EtcdGrove
end Perennial
