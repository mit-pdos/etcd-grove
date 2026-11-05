/-
`(*EtcdServer).run()` (`server.go`), translated with its body: the apply loop over the raft
wrapper's `applyc`, with the FIFO scheduler, the ready handler and the shutdown. Lean-first (the
request path's unit 4c, 2026-10-13); see `InvRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.run()`**, the server's apply loop (a goroutine body: `start`'s `go s.run()`), in both auth
modes (the auth component's stage 2, 2026-11-04; until then `spec` with auth off and `specOn` with
auth on, now `specOff`/`specOn`, `ModeSpecs.lean`'s corollaries): with what `isServerRunC` lists in
the component `C`, the environment's (with auth on, the receipts' bound, `acReceiptOk`), it starts
the raft wrapper's loop, then receives each batch of committed entries raft hands it (`applyc`) and
schedules its `applyAll` on a FIFO scheduler, the apply thread's resources flowing from job to job.
Its two exits, `errorc` and `stop`, are never taken in the runs covered (D19m: nothing is sent on
either, `srvRunFieldsAt`'s bags with predicate `False`), so it never returns. The write budget is
the receipt-backed `srvWTPool E` (D19b), from which `apply` takes one token per entry. -/
abbrev EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C⌝ ∗
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

/-- (DRAFT, R2b-2, 2026-11-02; `notes/restart-plan.md`, "R2b: the stop") **`run` of a server that
may be stopped**: `spec`'s, with stop requests on `stop` (`HardStop` sends one, `srvStopReq`: the
evidence that the bootstrap log was applied, `srvBootApplied`, R2b-2 review F2; and, R2c-2, the
stop's scope, `srvStop.scope`, and the data directory `dd`, `srvDataDir`) and `done`'s close
announcing the image of member `γn.id`'s data directory `dd` at the request names `ρ`, escrowed for
the stop right's claim `c` (`srvDoneInv`); with what the shutdown
needs besides (`srvShutdownPre`: the stop's slot, `srvStop.keep`, at the configuration `cfg` and
the transport key `γk` of the raft environment's `ST`). On a stop request `run` returns and its deferred shutdown runs:
`close(stopping)`, `cancel()`, `sched.Stop()` (the pending `applyAll` jobs run, the last one's post
`applyRes` at the log handed to the apply thread), `s.wg.Wait()`, `s.r.stop()`
(`raftNode.stop.specStop`), `Cleanup()` (the backend closed), and `close(done)` with the image in the
escrow (R2b-3: assembled from those posts).

Scope (R2b-2 review): a first start only (`isServerRun`'s `HEr`: `ai₀ = 0`, `γn.pre = []`; a
restarted member's `run` is R2d's, so `Start_builtR_spec`'s right waits for it); the `errorc` path
stays closed (its bag's `False`): were it opened (`stopWithDelay`, the transport's errors), the
shutdown would have to fill the escrow without a stop request's evidence; (2026-11-05) no compactor
(`v.compactor` nil: the census of the store's readers counts the compactor's among the slot's,
`srvStop.census_readers`; with one, the compactor's run holds it). One spec per function
(R2b-2 review F4): when R2b-2's proof is done, this replaces `spec` (whose callers never stop the
server), as `Start.spec` gives the right and `raftNode.stop.specStop` replaces `raftNode.stop.spec`;
the draft keeps both meanwhile. (The auth component's stage 2, 2026-11-04) Over the component `C`,
as the merged `spec`, so that it replaces it in both auth modes. -/
abbrev EtcdServer.run.specStop : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (dd : GoString) (c : GName)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γk : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C⌝ ∗
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) ∗
      srvShutdownPre s cfg E γn γk ∗
      -- (2026-11-05, R2b-3d stage 5d) the raft environment's transport stop right is the one
      -- keyed by the slot's `γk` (`srvErM`'s, as `NewServer` builds it). (R2c-2) The scope (auth
      -- off, no compaction mode, hence no compactor) is the stop request's (`srvStop.scope`); (R2c-1)
      -- the boot log's facts the image's configuration needs are `srvRaftLogInv`'s.
      ⌜Er.ST = srvTrStopK γk⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
