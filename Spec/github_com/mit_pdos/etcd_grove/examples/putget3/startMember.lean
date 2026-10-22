/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/putget3/putget3.go`; D21 stage
M5, 2026-10-19): one member of putget3's cluster started -- the server (configured as putget's),
its raft handler served on a listener at its peer address, the server started. Lean-first (no Rocq
counterpart).

**The triple:** given the member's ghost state (`memberBoot`, `putget3_alloc`'s) and network slot,
the right to listen on its peer address (`netAddrFree`, D19d), a thread token (`Start` forks the
server's goroutines; it comes back in `srvGoRes`), its URLs read-only (the peer URL slice, the
initial cluster's map with its three slices), `bootstrap`'s contract for it (`bootPremise`) and the
premises it shares with the other members: an error with the thread token, or the server started,
with what serving it to a client needs (`memberUp`: the server's request and read views, its
goroutine resources, the serving resources `NewServer` left).

**The pure premises:** putget's (`Main.spec`'s): the thread and time-receipt bounds, the named
effect and workload premises; the cluster's raft names (static, no-snapshot mode, the policy
`ccOk ps`), its bootstrap log shorter than `2 ^ 60`, the network's payload the server's and its
directory `dir`, with `http://peerAddr` one of the member's peer URLs there (`http.Serve`'s
premise); the logger not `nil`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- **A member started** (the success of `startMember`): the server `s` started with its request
names `ρ` (the wait registry's `γw`) at an apply environment `E` agreeing with the stand-in `E₀`,
auth off, built from a configuration `cfg` with the logger `lg`, no tracer options and no
progress-notify interval; what
`Start` returns (the request and read views, the `GoAttach` resources with the thread token, a
`lgMu` reader slot, the read loop's readers) and what `NewServer` left for serving
(`srvServeBuilt`'s resources, two of its `lgMu` slots spent on `Start`). -/
def memberUp (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ cfg.WatchProgressNotifyInterval' ∗
    srvBemuReader s ∗
    ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
    ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
    ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
    ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
    ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s))

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (sl₁ sl₂ sl₃ : GoSlice)
    (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString) (id : w64)
    (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.reCfg = GMap.listToSet ps → γ.reDyn = none → γ.reCCOk = ccOk ps → γ.reBoot = bootLog →
  γ.reNoSnap = true → γ.reNoXfer = true → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ bud → γn.dir = dir → go!"http://" ++ peerAddr ∈ dir id →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.putget3 ∗
      netAddrFree (GF := GF) peerAddr ∗ threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗
      cluster ↦$□ GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅)) ∗
      sl₁ ↦*□ initURLs3 name₁ ∗ sl₂ ↦*□ initURLs3 name₂ ∗ sl₃ ↦*□ initURLs3 name₃ ∗
      bootPremise N ps bootLog dir name peerAddr client id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot putgetWorkload γ bud bootLog ρ E₀ Φs id ∗ netSlot γn id }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.putget3.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg) }}

end spec

end putget3
end EtcdGrove
end Perennial
