/-
`newServerMode(name, peer, client, cluster, token, mode, retention, snapCount, catchUp, lg)`
(`examples/common/common.go`; periodic mode, 2026-11-02): `newServer` with the auto-compactor's mode
a parameter -- member `name` of a new cluster with token `token` built, its configuration and
`etcdserver.NewServer`. Lean-first (no Rocq counterpart).

**The triple:** `newServer`'s (`Spec/.../common/newServer.lean`), in the compaction mode `cmp`: off
(the retention zero), or on in revision mode (a positive retention, the cluster's retention at most
it) or in periodic mode (a period of at least 10ns, the cluster's retention `0`), as `NewServer`'s
premise; on, at `N + N` write tokens and the boot bundle in compaction mode (`memberBoot … true`).
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
abbrev newServerMode.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token mode : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (2026-11-02, the backend-auth-split stage, Q8) the initial cluster's names valid UTF-8,
  -- `bootPremise`'s condition
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  lg ≠ null →
  -- the compactor: on in revision mode at a positive retention at least the cluster's, or in
  -- periodic mode at a period of at least 10ns and the cluster's retention `0`; or off
  (if cmp then
      (mode = go!"revision" ∧ 0 < sint.Z retention ∧ (ρ.rd.kv.cret : Int) ≤ sint.Z retention) ∨
        (mode = go!"periodic" ∧ 10 ≤ sint.Z retention ∧ ρ.rd.kv.cret = 0)
    else retention = W64 0) →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      -- on, at `N + N` write tokens: `N` more, the compaction's write-back stock
      bootPremise (if cmp then N + N else N) ps bootLog ctxs dir token name Uok id ∗
      commonPremises ∗ context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp ∗
      netHttpOk γn id }}
    (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.newServerMode))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #mode))
      (Val #retention)) (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false) }}

end spec

end common
end EtcdGrove
end Perennial
