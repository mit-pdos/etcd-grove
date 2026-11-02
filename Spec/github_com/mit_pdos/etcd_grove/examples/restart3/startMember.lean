/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/restart3/restart3.go`; the
restart plan's R2a, 2026-11-02; DRAFT): member `name` of `restart3`'s cluster built
(`common.BuildServer` at the snapshot settings), its raft handler served on a listener at
`peerAddr`, and the server started. Lean-first (no Rocq counterpart).

**`spec`, a first start:** `common.StartMember`'s, but the server built by `BuildServer.specStop`
and the peer listener registered closable: an error (with the thread token), or the started member
(`common.memberUp`) and a stoppable member's record (`memberStop`).

**`specRestart`, a start after a stop** (R2c, R2d): the same, from the data directory the stop left
(`srvDiskImage`), `bootstrap`'s restart contract (`common.bootPremiseR`) and the restart's boot
bundle (`srvRestartBoot`), the peer address and its protocol's right as the stop gave them back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Defs

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
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[common.httpURL peerAddr], [common.httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      netAddrFree (GF := GF) peerAddr ∗ threadTok ∗
      peer ↦*□ [common.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      common.bootPremise N ps bootLog ctxs dir token name Uok id ∗ common.commonPremises ∗
      context.isClosedchanInit ∗
      common.memberBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id ∗ http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (s : Loc) (pl : GoInterface),
        common.memberUp s ρ E₀ lg γn id ∗ memberStop m s pl γ id peerAddr γn) }}

/-- See the file header (`specRestart`). -/
abbrev startMember.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[common.httpURL peerAddr], [common.httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      netAddrFree (GF := GF) peerAddr ∗ threadTok ∗
      peer ↦*□ [common.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      common.bootPremiseR N ps bootLog ctxs dir token name Uok id ∗ common.commonPremises ∗
      context.isClosedchanInit ∗
      srvDiskImage γ id ∗ srvRestartBoot γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id ∗ http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (s : Loc) (pl : GoInterface),
        common.memberUp s ρ E₀ lg γn id ∗ memberStop m s pl γ id peerAddr γn) }}

end spec

end restart3
end EtcdGrove
end Perennial
