/-
`StartServer(name, peerAddr, clientAddr, lg)` (`examples/common/common.go`; 2026-10-22, D33): the one
member of a new cluster started -- its peer URL slice, `newServer` (with the cluster's map
`{name ↦ peer}` and the token `name`), `s.Start()`; what putget's, linkv's, linkvtxn's, watchkv's
and cachekv's `Main`s did up to `Start`. Lean-first (no Rocq counterpart).

**The triple:** given the member's ghost state (`memberBoot`, `alloc1`'s) and the network's HTTP side (`netHttpOk`), a thread
token (`Start` forks the server's goroutines; it comes back in `srvGoRes`), `bootstrap`'s contract
for it (`bootPremise` at the one-member cluster `[id]`, the token `name` and the URLs `urls1`) and
the premises the members share: an error with the thread token, or the server started
(`memberUp`).

**The pure premises:** `newServer`'s at the one-member cluster.
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
abbrev StartServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString) (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = [id] → γ.dyn = false → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      threadTok ∗
      bootPremise N [id] bootLog ctxs dir name name (urls1 name peerAddr client) id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id }}
    (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.StartServer))
      (Val #name)) (Val #peerAddr)) (Val #client)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id) }}

end spec

end common
end EtcdGrove
end Perennial
