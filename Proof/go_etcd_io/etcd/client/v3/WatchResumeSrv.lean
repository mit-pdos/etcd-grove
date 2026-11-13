/-
**A response's resume fact from the server's facts** (D25, `notes/decisions.md`): what `run`
proves of each response it dispatches (`resumeF`, `InvWatch.lean`): since D47 no fact
(`resumeF_holds`); strict M1, 2026-11-06: no server fact either (mvcc's `relLb`, `respRev` gone). Lean-first, no Rocq counterpart.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchResume
public import Proof.go_etcd_io.etcd.client.v3.WatchContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The resume fact of an event-less response** (no fact since D47: `resumeF_holds`; strict M1:
no server fact, mvcc's `notifiedLb` gone). -/
theorem resumeF_evless (V : WEnv GF) (P : WsPrm GF) (r : RespModel) : ⊢ resumeF (GF := GF) V P r :=
  resumeF_holds V P r

/-- **The resume fact of a response with events, delivered** (no fact since D47: `resumeF_holds`;
strict M1: no server fact, mvcc's `evLog` gone). -/
theorem resumeF_delivered (V : WEnv GF) (P : WsPrm GF) (r : RespModel) :
    ⊢ resumeF (GF := GF) V P r :=
  resumeF_holds V P r

end lemmas

end client
end EtcdGrove
end Perennial
