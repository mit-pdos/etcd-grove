/-
`newMember(s, name, peer, peerAddr, client)` and `restartMember(m, cluster, lg)`
(`examples/etcd/restart/restart3.go`; restart3 C2/C3, 2026-11-15, D-R3-4). Lean-first (no Rocq
counterpart).

**`newMember.spec`:** of a member built (`etcdstart.memberBuilt`, its peer address not yet served:
`httpProcSlots` copies of its raft handler's resource), the right to listen on its peer address and to
serve it with the raft protocol of the network `γn` (the fresh bundle's peer part,
`etcdstart.memberFreshRes_peer`), the address the member's (`netRh γn`'s owner), and the main thread's
token: an error with the token (`net.Listen` failed), or the member started (`etcdstart.memberUp`) and
its record (`memberRec`: its peer handler `raftSwap`, served on the address for the rest of the run,
holding the first incarnation's handler; its name, peer URLs and client address).

**`restartMember.spec`:** of a stopped member's record, its restart bundle without addresses (the stop's,
`etcdstart.memberRestartRes`), the cluster's persistent facts at its stopped names
(`etcdstart.memberRestartFacts`), `ETCD_VERIFY` off and `bootstrap`'s restart contract: an error with the
token, or the member started again (`etcdstart.memberUp`) at new names `ρ'` that agree with the stopped
ones where the cluster sees them (`restartNames`), its peer handler swapped to the new incarnation's
raft handler (`raftSwap.set`) before it starts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev newMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (s : Loc) (name peerAddr client : GoString)
    (peer : GoSlice) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  (netRh γn).owner peerAddr = id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      threadTok ∗ etcdstart.memberBuilt s ρ E₀ lg γn id N false ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗
      http.httpAddrFree peerAddr ∗ http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.newMember))
      (Val #s)) (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ γS : SwNames, etcdstart.memberUp s ρ E₀ lg γn id ∗
          memberRec m γS γn name peerAddr client) }}

/-- See the file header (`restartMember`). -/
abbrev restartMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (m : Loc) (γS : SwNames)
    (name peerAddr client : GoString) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  etcdstart.addrFits peerAddr → etcdstart.addrFits client →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      zapLoggerOk lg ∗ threadTok ∗ memberRec m γS γn name peerAddr client ∗
      cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      etcdstart.bootPremiseR N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗ etcdstart.memberRestartRes name {} γn γ ρ id ∗ netHttpOk γn id ∗
      etcdstart.memberRestartFacts γ ρ id ∗ envVerifyOff }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.restartMember))
      (Val #m)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ (ρ' : ReqNames) (E₀' : apply.AEnv GF), ⌜restartNames ρ ρ'⌝ ∗
          etcdstart.memberUp s ρ' E₀' lg γn id) }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
