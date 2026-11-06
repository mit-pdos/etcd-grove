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
modes (the auth component's stage 2, 2026-11-04): with what `isServerRunC` lists in the component
`C`, the environment's (with auth on, the receipts' bound, `acReceiptOk`), it starts the raft
wrapper's loop, then receives each batch of committed entries raft hands it (`applyc`) and
schedules its `applyAll` on a FIFO scheduler, the apply thread's resources flowing from job to job.
The write budget is the receipt-backed `srvWTPool E` (D19b), from which `apply` takes one token per
entry. Its exit `errorc` is never taken in the runs covered (D19m: nothing is sent on it,
`srvRunFieldsAt`'s bag with predicate `False`). On `stop` it receives stop requests (`srvStopReq`,
what `HardStop` sends: the evidence that the bootstrap log was applied, `srvBootApplied`; the stop's
scope, `srvStop.scope`; the data directory `dd`, `srvDataDir`; the store's readers of the serving
stocks); on one it returns and its deferred shutdown runs: `close(stopping)`, `cancel()`,
`sched.Stop()` (the pending `applyAll` jobs run, the last one's post `applyRes` at the log handed to
the apply thread), `s.wg.Wait()`, `s.r.stop()` (`raftNode.stop.specStop`, with the stop's slot that
`isServerRunC` carries, `srvStop.slot`), `Cleanup()` (the backend closed), and `close(done)`, which
announces the image of member `γn.id`'s data directory `dd` at the request names `ρ`, escrowed for
the stop right's claim `c` (`srvDoneInv`).

One spec (R2c-4, the R2b-2 review's F4; until then `spec`, whose callers never stopped the server,
with `done` announcing `True` and no request ever sent, and the draft `specStop`, with the shutdown's
resources and the scope as premises). Scope: a first start (`isServerRun`'s `HEr`: `ai₀ = 0`,
`γn.pre = []`; a restarted member's `run` is R2d's); the `errorc` path stays closed. -/
abbrev EtcdServer.run.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (dd : GoString) (c : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C⌝ ∗
      isServerRunC C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
