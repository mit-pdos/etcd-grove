/-
**The watch laws of mvcc's API** (stage 2 of the mvcc API proof, the watch chain:
`notes/mvcc-api-risk.md`, M1; 2026-11-04), over the sealed definitions (`Api.lean`, over
`Api/StreamGhost.lean`). Lean-first (no Rocq counterpart).

- `wsRecv_ok.law_holds`: `wsRecv_ok.law`, a plain entailment (`wsRecv_okI`);
- `wsSentLb_zero.law_holds`;
- the watch conjuncts of `persistent.law` (as instances) and of `excl.law`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance isMvccWatchStream_persistent (ws : GoInterface) (γ : MvccName) (ι : WsName) :
    Persistent (isMvccWatchStream (GF := GF) ws γ ι) := by
  unfold isMvccWatchStream; infer_instance

instance wsSentLb_persistent (ι : WsName) (n : Nat) : Persistent (wsSentLb (GF := GF) ι n) := by
  unfold wsSentLb; exact wsSentLbI_persistent (GF := GF) (ι : WsAbs) n

instance mvccState_timeless (γ : MvccName) (σ : MvccState) :
    Timeless (mvccState (GF := GF) γ σ) := by
  unfold mvccState; infer_instance

instance wsState_timeless (ι : WsName) (S : StreamState) : Timeless (wsState (GF := GF) ι S) := by
  unfold wsState; exact wsStateI_timeless (GF := GF) (ι : WsAbs) S

instance wsRecv_timeless (ι : WsName) (rs : List WResp) : Timeless (wsRecv (GF := GF) ι rs) := by
  unfold wsRecv; exact wsRecvI_timeless (GF := GF) (ι : WsAbs) rs

theorem mvccState_excl (γ : MvccName) (σ σ' : MvccState) :
    mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False := by
  unfold mvccState; exact mvccStateI_excl _ σ σ'

theorem wsState_excl (ι : WsName) (S S' : StreamState) :
    wsState (GF := GF) ι S ∗ wsState ι S' ⊢ False := by
  unfold wsState; exact wsStateI_excl _ S S'

theorem wsRecv_excl (ι : WsName) (rs rs' : List WResp) :
    wsRecv (GF := GF) ι rs ∗ wsRecv ι rs' ⊢ False := by
  unfold wsRecv; exact wsRecvI_excl _ rs rs'

/-- **`wsRecv_ok.law`**: a plain entailment, no invariant opened. -/
theorem wsRecv_ok.law_holds : wsRecv_ok.law (GF := GF) := by
  intro ws γ ι rs S σ
  unfold isMvccWatchStream wsRecv wsState mvccState
  iintro ⟨⟨%hst, -⟩, Hr, Hs, Hm⟩
  have hst' : (ι : WsAbs).st = (γ : StoreNames).api := hst
  rw [← hst']
  iapply wsRecv_okI ι rs S σ $$ [$Hr $Hs $Hm]

/-- **`wsSentLb_zero.law`.** -/
theorem wsSentLb_zero.law_holds : wsSentLb_zero.law (GF := GF) := by
  intro ι
  unfold wsSentLb
  exact wsSentLbI_zero ι

end laws

end api
end mvcc
end EtcdGrove
end Perennial
