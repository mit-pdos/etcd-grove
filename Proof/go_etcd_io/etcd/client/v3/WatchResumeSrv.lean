/-
**A response's resume fact from the server's facts** (D25, `notes/decisions.md`): what `run`
proves of each response it dispatches (`resumeF`, `InvWatch.lean`): a create from just past the
response's position is a start-read one, from the released length mvcc's deliveries carry
(`mvcc.relLb`, an event's revision) or the notified log an event-less response's revision is the
last of (`mvcc.respRev`). Lean-first, no Rocq counterpart.
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

/-- **An event-less mvcc response's revision is a notified log's last** (`mvcc.respRev`, kept by
the stream's facts `mvccOk`). -/
theorem mvccOk_revLb (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : v3rpc.WatchRespM)
    (ρ : mvcc.RespM) (hsrc : m.src = some ρ) (hev : ρ.evs = []) :
    v3rpc.mvccOk (GF := GF) γs γ j m ⊢
      ∃ L : mvcc.Log, mvcc.notifiedLb γ L ∗ ⌜sint.Z m.hdr.revision + 1 = (L.length : Int)⌝ := by
  iunfold v3rpc.mvccOk
  iintro ⟨%r, %rs, %L, %Hm, -, -, -, -, #Hcov, -⟩
  have hr : r = ρ := by
    have := congrArg v3rpc.WatchRespM.src Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [hsrc] at this; exact (Option.some.inj this).symm
  subst hr
  iunfold v3rpc.mvccCov at Hcov
  icases Hcov with ⟨%γc, %pre, %γo, %γa, -, -, -, -, #Hrc, -⟩
  ihave #Hlb := mvcc.respCov_rev _ _ _ _ $$ Hrc
  iunfold mvcc.revLbOf at Hlb
  icases Hlb with (%H | ⟨%L', #HL', %HL'⟩)
  · exact absurd hev H
  iexists L'
  iframe HL'
  ipureintro; rw [Hm.2.1]; exact HL'

/-- **The resume fact of an event-less response** (no fact since D47: `resumeF_holds`). -/
theorem resumeF_evless (V : WEnv GF) (P : WsPrm GF) (r : RespModel) (L : mvcc.Log) :
    mvcc.notifiedLb V.R.γ L ⊢ resumeF V P r := by
  iintro -
  iapply resumeF_holds

/-- **The resume fact of a response with events, delivered** (no fact since D47: `resumeF_holds`). -/
theorem resumeF_delivered (V : WEnv GF) (P : WsPrm GF) (r : RespModel) (L : mvcc.Log) :
    mvcc.evLog V.R.γ.st L ⊢ resumeF V P r := by
  iintro -
  iapply resumeF_holds

end lemmas

end client
end EtcdGrove
end Perennial
