/-
**The client's restore update is the store's ghost step** (`KV.Restore.contract`, 2026-11-06).
Lean-first (no Rocq counterpart).

`store.Restore`'s takeover fires its caller's `restoreCb` with `s.revMu`'s slot and the writer's part
of the API's view at the committed log; `restoreCb_of_au` makes it from the contract's atomic update
(at the state `σ'` the image holds) and the open token's quarter of the compaction authority: the
view, the compaction authority and the notified log's authority move to `σ'`, which is committed.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.OFE Iris.CMRA Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The client's restore update is the store's ghost step** (`restoreCb`, at the store's current
names `γ0.withPhys p`): at the state `σ` the update opens at, the committed log `L` is `σ.log` and
the compaction revision `σ.crev` (the view's agreement), nothing pending (the writer's part at
`none`); the view (the client's half, `s.revMu`'s and the writer's quarters), the compaction
authority (the client's half, `s.revMu`'s and the open token's quarters, `c0` theirs) and the
notified log's authority move to `σ'` (its log extends `σ.log`, its compaction revision is at least
`σ.crev`: the update's premise), which is committed with its receipt. Returned: the open token's
quarter at `σ'.crev` and the client's `Q`. -/
theorem mvcc.restoreCb_of_au (γ0 : mvcc.StoreNames) (p : mvcc.PhysNames) (σ' : mvcc.api.MvccState)
    (hp : σ'.pending = none) (hreach : mvcc.api.MvccReachable σ') (c0 : Int) (hc0 : -1 ≤ c0)
    (Q : mvcc.api.MvccState → IProp GF) :
    mvcc.api.crevAuth γ0.api (1 : Qp).half.half c0 ∗ ⧖ (mvcc.logCh σ'.log) ∗
      iprop(AU <{ ∃∃ (σ : mvcc.api.MvccState), mvcc.api.mvccStateI γ0.api σ ∗
            ⌜σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev⌝ }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
        <{ mvcc.api.mvccStateI γ0.api σ' ∗ ⧖ (mvcc.logCh σ'.log), COMM Q σ }>) ⊢
    mvcc.restoreCb (γ0.withPhys p) σ'.log σ'.crev
      iprop(mvcc.api.crevAuth γ0.api (1 : Qp).half.half σ'.crev ∗ ∃ σ : mvcc.api.MvccState, Q σ) := by
  generalize hγ : (γ0.withPhys p) = γ
  have hapi : γ.api = γ0.api := by rw [← hγ]; rfl
  rw [← hapi]
  iintro ⟨Hcr, #Hrc', Hau⟩
  iunfold mvcc.restoreCb
  iintro %L %c %cy ⟨HX, HYa, HYp⟩
  rw [show ((⊤ : CoPset) \ ↑(nroot .@ "mvcc" : Namespace)) = ⊤ \ ↑mvcc.api.mvccN from rfl]
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, ⟨Hσ, %Hpre⟩, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold mvcc.api.mvccStateI at Hσ
  icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach, #Hrcm⟩
  iunfold mvcc.slotX at HX
  iunfold mvcc.api.revMuAbs at HX
  icases HX with ⟨HXa, HXc⟩
  -- the agreements: the committed log and compaction revision are the state's, nothing pending
  ihave %Hag := mvcc.api.absPart_agree γ.api _ _ _ _ _ _ $$ [Ha HXa]
  · iframe Ha HXa
  obtain ⟨hlog, hcrev⟩ := Hag
  ihave %Hag2 := mvcc.api.absPart_agree γ.api _ _ _ _ _ _ $$ [Ha HYa]
  · iframe Ha HYa
  obtain ⟨-, hcy⟩ := Hag2
  ihave %Hpn := mvcc.api.pndPart_agree γ.api _ _ _ _ $$ [Hp HYp]
  · iframe Hp HYp
  have hσc := mvcc.api.reach_crev σ Hreach
  iunfold mvcc.api.crevAuth at Hcc Hcr
  iunfold monoNatAuthOwn at Hcc Hcr
  icombine Hcc Hcr gives %Hvalid
  obtain ⟨-, hv2⟩ := (Iris.MonoNat.auth_dfrac_op_valid _ _ _ _).mp Hvalid
  have Hc0 := congrArg MaxNat.toNat hv2
  have hc0 : c0 = σ.crev := by simp only [mvcc.api.crevN] at Hc0; omega
  ihave Hcc : mvcc.api.crevAuth γ.api (1 : Qp).half σ.crev $$ [Hcc]
  · iunfold mvcc.api.crevAuth; iunfold monoNatAuthOwn; iexact Hcc
  ihave Hcr : mvcc.api.crevAuth γ.api (1 : Qp).half.half c0 $$ [Hcr]
  · iunfold mvcc.api.crevAuth; iunfold monoNatAuthOwn; iexact Hcr
  subst hlog hcrev hc0
  subst hcy
  -- the view: the writer's and the lock's quarters joined, then updated with the client's half
  have hq := (mvcc.api.absPart_fractional (GF := GF) γ.api σ.log σ.crev).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hq
  ihave HXY := hq.2 $$ [HXa HYa]
  · iframe HXa HYa
  imod mvcc.api.absPart_update γ.api (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1) σ.log σ.log
    σ'.log σ.crev σ.crev σ'.crev $$ [Ha HXY] with ⟨Ha, HXY⟩
  · iframe Ha HXY
  have hq' := (mvcc.api.absPart_fractional (GF := GF) γ.api σ'.log σ'.crev).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hq'
  icases hq'.1 $$ HXY with ⟨HXa, HYa⟩
  -- the authority: the client's half, the lock's quarter and the open token's quarter, raised
  have hc := (mvcc.api.crevAuth_fractional (GF := GF) γ.api σ.crev).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hc
  have hc2 := (mvcc.api.crevAuth_fractional (GF := GF) γ.api σ.crev).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hc2
  ihave Hc1 := hc.2 $$ [HXc Hcr]
  · iframe HXc Hcr
  ihave Hc1 := hc2.2 $$ [Hcc Hc1]
  · iframe Hcc Hc1
  imod mvcc.api.crevAuth_update γ.api σ.crev σ'.crev Hpre.2 $$ Hc1 with ⟨Hc1, -⟩
  have hc' := (mvcc.api.crevAuth_fractional (GF := GF) γ.api σ'.crev).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hc'
  have hc'' := (mvcc.api.crevAuth_fractional (GF := GF) γ.api σ'.crev).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hc''
  icases hc'.1 $$ Hc1 with ⟨Hcc, Hc1⟩
  icases hc''.1 $$ Hc1 with ⟨HXc, Hcr⟩
  -- the notified log: the state's log (nothing pending), extended to the restored one
  have hnl : σ.notifiedLog = σ.log := by
    unfold mvcc.api.MvccState.notifiedLog; rw [Hpn]
  have hnl' : σ'.notifiedLog = σ'.log := by
    unfold mvcc.api.MvccState.notifiedLog; rw [hp]
  iunfold mvcc.api.nlAuth at Hnl
  rw [hnl]
  imod monoListAuthOwn_update σ'.log Hpre.1 $$ Hnl with ⟨Hnl, #Hnlb⟩
  -- the commit at `σ'`
  imod Hcommit $$ [Ha Hp Hcc Hnl] with HQ
  · iunfold mvcc.api.mvccStateI
    rw [hp, ← Hpn, hnl']
    iunfold mvcc.api.nlAuth
    iframe Ha Hp Hcc Hnl
    iframe Hrc'
    ipureintro; exact hreach
  imodintro
  iframe HYa HYp Hcr
  isplitr
  · ipureintro; exact Hpre.1
  isplitl [HXa HXc]
  · iunfold mvcc.slotX; iunfold mvcc.api.revMuAbs; iframe HXa HXc
  isplitr
  · iunfold mvcc.api.nlLb; iexact Hnlb
  iexists σ; iexact HQ

end core

end EtcdGrove
end Perennial
