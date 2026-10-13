/-
The batch lock's ghost state across a commit (`unsafeCommit`): the payment (`payIn`) spent,
the counters reset (`commit_bgOk`), the lock's share of the free state rebuilt
(`commit_ghost`). Lean-first (no Rocq counterpart); see `InvBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The batch lock's share of the free state after a commit from `st` (the hook ran into
`st'`), paid by `payIn`: the new committed data `C'`, write transaction `tx'`. -/
theorem commit_ghost (γ : BNames) (P : BParams) (st st' : BSess) (C' : Data) (tx' : Loc)
    (m u n w u0 : Nat)
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [])
    (hp0 : st.cnt.p0 = sint.nat st.pend) (hs : hookStep P st st') (hst : sessWf P st)
    (hb' : bgOk P st' false n w u0) :
    payIn (GF := GF) γ st false m u ∗ ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗
      ghostVar γ.used (1 : Qp).half u0 ∗ dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C', st'.R.reset)) ∗
      ghostVar γ.rvs (1 : Qp).half (((C', st'.R.reset) : RView), false) ⊢
    |==> ∃ cnt' : BCnt, batchGhostAt γ P (commitSt st' C' tx' cnt') true ∗ payOut γ false m := by
  iintro ⟨Hpay, Ha, Hm, Hu, Ho, Hv, Hr⟩
  have hR := hs.2.1
  have hcnt := hs.2.2.2.2.2.2.2.2
  have hb'0 := hb'
  obtain ⟨hb1, hb2, hb3, -⟩ := hb'0
  rw [hcnt, hR] at hb1
  rw [hcnt] at hb3
  unfold payIn payOut
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hm0 : m = 0
  · rw [if_pos hm0, if_neg (fun h : True ∧ m = 1 => by omega)]
    unfold wbTok
    icombine Ha Hpay gives %Hle
    imod ownTokAuth_sub 1 γ.wb n $$ Ha Hpay with Ha
    imodintro
    iexists ⟨st.cnt.k + 1, st.cnt.c + 1, 0, 0⟩
    isplitl [Hv Hr Ha Hm Hu Ho]
    · unfold batchGhostAt
      simp only [commitSt_C, commitSt_R]
      iframe Hv
      iexists n - 1, w, u0
      iframe Hr Ha Hm Hu Ho
      ipureintro
      have hb4 : uint.Z st.R.ver + ((n - 1 : Nat) : Int) + ((st.cnt.k + 1 : Nat) : Int) < 2 ^ 40 := by
        omega
      refine (commit_bgOk (k' := st.cnt.k + 1) hW hp0 hs hst hb' (n - 1) w u0
        hb4 hb2 ?_)
      split at hb3 <;> split <;> omega
    · itrivial
  by_cases hm1 : m = 1
  · rw [if_neg hm0, if_pos hm1, if_pos ⟨trivial, hm1⟩]
    icases Hpay with ⟨Hru, #Hlb⟩
    icombine Hu Hru gives % ⟨_, Hueq⟩
    subst Hueq
    ihave %Hlw := monoNatLbOwn_valid γ.wbc 1 w (u0 + 1) $$ Hm Hlb
    imod ghostVar_update_halves w γ.used u0 u0 $$ Hu Hru with ⟨Hu, Hru⟩
    imodintro
    iexists ⟨st.cnt.k, st.cnt.c + 1, 0, 0⟩
    isplitl [Hv Hr Ha Hm Hu Ho]
    · unfold batchGhostAt
      simp only [commitSt_C, commitSt_R]
      iframe Hv
      iexists n, w, w
      iframe Hr Ha Hm Hu Ho
      ipureintro
      refine (commit_bgOk (k' := st.cnt.k) hW hp0 hs hst hb' n w w
        hb1 (Nat.le_refl _) ?_)
      have : u0 ≠ w := by omega
      simp only [this, ↓reduceIte] at hb3
      simp only [↓reduceIte]
      omega
    · iexists w
      iexact Hru
  · rw [if_neg hm0, if_neg hm1, if_neg (fun h : True ∧ m = 1 => hm1 h.2)]
    icases Hpay with %Hc0
    imodintro
    iexists ⟨st.cnt.k, st.cnt.c + 1, 0, 0⟩
    isplitl [Hv Hr Ha Hm Hu Ho]
    · unfold batchGhostAt
      simp only [commitSt_C, commitSt_R]
      iframe Hv
      iexists n, w, u0
      iframe Hr Ha Hm Hu Ho
      ipureintro
      refine (commit_bgOk (k' := st.cnt.k) hW hp0 hs hst hb' n w u0
        hb1 hb2 ?_)
      rw [Hc0]
      split <;> omega
    · itrivial

end lemmas

end backend
end EtcdGrove
end Perennial
