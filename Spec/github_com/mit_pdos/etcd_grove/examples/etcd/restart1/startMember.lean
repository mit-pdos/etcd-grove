/-
`startMember(lg)` (`examples/etcd/restart1/restart1.go`; restart S7.5, 2026-11-14): the member built
(`etcdstart.BuildServer` at the snapshot settings, its peer URL `http://peerAddr`, the initial cluster
`{restart1: peer}`) and started. Lean-first (no Rocq counterpart).

**`spec`, a first start:** `etcdstart.StartServer`'s, over `BuildServer.spec` and `Start`: an error
(with the thread token), or the started member (`etcdstart.memberUp`) and its server's data
directory (`srvDataDir`, which its stop takes).

**`specRestart`, a start after a stop:** the same, from the data directory the stop left
(`etcdstart.memberRestartRes`, at the stopped incarnation's names `ρ`), the cluster's persistent facts
at `ρ` (`etcdstart.memberRestartFacts`), `ETCD_VERIFY` off and `bootstrap`'s restart contract
(`etcdstart.bootPremiseR`): the member started at new names `ρ'` that agree with `ρ` where the
cluster sees them (`restartNames`). (restart3 A1, 2026-11-15: `BuildServer.specRestart` has no
restart-only rows any more; until then the proof discharged them for the one member,
`srvRestartRows_single`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (lg : Loc) (bootLog : List EntryM)
    (ctxs : List (List w8)) (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir id → netDirOk (dir id) →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      zapLoggerOk lg ∗ threadTok ∗
      etcdstart.bootPremise N [id] bootLog ctxs (dir id) name name urlsOk id ∗
      context.isClosedchanInit ∗
      etcdstart.memberBoot γ ctxs ρ E₀ Φs id ∗ netHttpOk γn id ∗
      etcdstart.memberFreshRes name {} γn }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.startMember)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ etcdstart.memberUp s ρ E₀ lg γn id ∗
        srvDataDir s (memberDataDir name)) }}

/-- See the file header (`specRestart`). -/
abbrev startMember.specRestart : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (lg : Loc) (bootLog : List EntryM)
    (ctxs : List (List w8)) (id : w64) (γ : SrvRaft) (ρ : ReqNames) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir id → netDirOk (dir id) →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      zapLoggerOk lg ∗ threadTok ∗
      etcdstart.bootPremiseR N [id] bootLog ctxs (dir id) name name urlsOk id ∗
      context.isClosedchanInit ∗ netHttpOk γn id ∗
      etcdstart.memberRestartRes name {} γn γ ρ id ∗
      etcdstart.memberRestartFacts γ ρ id ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.startMember)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (ρ' : ReqNames) (E₀' : apply.AEnv GF), ⌜restartNames ρ ρ'⌝ ∗
        etcdstart.memberUp s ρ' E₀' lg γn id ∗ srvDataDir s (memberDataDir name)) }}

end spec

end etcd_restart1
end EtcdGrove
end Perennial
