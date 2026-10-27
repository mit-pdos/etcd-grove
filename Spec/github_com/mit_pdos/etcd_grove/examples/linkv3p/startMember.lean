/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/linkv3p/linkv3p.go`; the
partition plan's S3a, 2026-10-20): one member of linkv3p's cluster started and served --
putget3's `startMember` (the examples' shared `common.StartMember`,
`Spec/.../common/StartMember.lean`, whose header explains the triple) with linkv3p's cluster token,
member names and URLs (`linkv3p.bootPremise`, `linkv3p.initURLs3`),
plus a listener at the member's client address (before `Start`) and, after `Start`, etcd's gRPC
server (`v3rpc.Server(s, nil, nil)`) served on it (what linkv3's `Main` did for its first member
only). Its success is `memberServed` (`Defs.lean`): the member's views, its thread token
(`srvGoRes`), its place in the network and etcd's `Put`/`Range` at its client address. The
premises are putget3's plus the right to listen at the client address and v3rpc's method sets
(`v3rpc.Server`'s). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL ccOk commonPremises)
open common (memberBoot)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (sl₁ sl₂ sl₃ : GoSlice)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  -- (W4 of `notes/watch-cut-plan.md`) the members' workload, granting no lease
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = ps → γ.dyn = false → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) peerAddr ∗ netAddrFree (GF := GF) client ∗ threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗
      cluster ↦$□ GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅)) ∗
      sl₁ ↦*□ initURLs3 name₁ ∗ sl₂ ↦*□ initURLs3 name₂ ∗ sl₃ ↦*□ initURLs3 name₃ ∗
      bootPremise N ps bootLog ctxs dir name peerAddr client id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it and the right to serve its peer address with the raft protocol
      netHttpOk γn id ∗ http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ memberServed γn s id ρ E₀ client) }}

end spec

end linkv3p
end EtcdGrove
end Perennial
