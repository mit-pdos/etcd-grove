/-
`newServer(name, peer, client, cluster, token, lg)` (`examples/common/common.go`; 2026-10-22, D33):
member `name` of a new cluster with token `token` built -- its configuration (as putget's, putget3's
and their followers' were) and `etcdserver.NewServer`. Lean-first (no Rocq counterpart).

**The triple:** given the member's ghost state (`memberBoot`, `alloc1`'s or `alloc3`'s) and the
network's HTTP side for it (`netHttpOk`), its URLs read-only (the peer URL slice `[http://peerAddr]`, the initial cluster's map `M` with
each member's peer URL slice, its initial URLs by name `iu`), `bootstrap`'s contract for it
(`bootPremise`, whose URLs predicate `Uok` the configuration's URLs meet) and the premises the
members share: an error, or the server built (`memberBuilt`).

**The pure premises:** the logic's thread bound and the time-receipt
bounds; the server's raft names of the cluster (its peers `ps`, static, its bootstrap log), the log
shorter than `2 ^ 60`, the network's payload the server's and its directory `dir`; the logger not
`nil`; the named effect premises of the server's construction.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev newServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = ps → γ.dyn = false → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.newServer))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ memberBuilt s ρ E₀ lg γn id N false) }}

end spec

end common
end EtcdGrove
end Perennial
