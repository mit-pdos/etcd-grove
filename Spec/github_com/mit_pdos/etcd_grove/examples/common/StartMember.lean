/-
`StartMember(name, peer, peerAddr, client, cluster, token, lg)` (`examples/common/common.go`;
2026-10-22, D33): member `name` of a new cluster started -- `NewMember` (the server, its raft
handler served on a listener at its peer address), then `s.Start()`; putget3's and linkv3's
`startMember`. Lean-first (no Rocq counterpart).

**The triple:** `NewMember`'s, plus a thread token (`Start` forks the server's goroutines; it comes
back in `srvGoRes`): an error with the thread token, or the server started (`memberUp`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev StartMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString) (id : w64)
    (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.reCfg = GMap.listToSet ps → γ.reDyn = none → γ.reCCOk = ccOk ps → γ.reBoot = bootLog →
  γ.reNoSnap = true → γ.reNoXfer = true → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ bud → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      netAddrFree (GF := GF) peerAddr ∗ threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ bud bootLog ρ E₀ Φs id ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it and the right to serve its peer address with the raft protocol
      netHttpOk γn id ∗ http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}
    (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.StartMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id) }}

end spec

end common
end EtcdGrove
end Perennial
