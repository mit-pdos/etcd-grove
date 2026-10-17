/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Unlock.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Unlock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__IsOwner
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

/-- `Unlock`'s transaction (etcd-io/etcd#22115): if `key` still has create revision `rev`
(`IsOwner()`), delete it. -/
def unlockTxn (key : GoString) (rev : w64) : TxnModel :=
  { cmps := [compareM (cmpKeyM .create key) .eq (.num rev)],
    thenOps := [.delete (opDeleteModel key [])], elseOps := [] }

theorem unlock_deleteOp_txnOpOf (key : GoString) :
    txnOpOf (opDeleteModel key []) = some (.delete (opDeleteModel key [])) := by
  simp [opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem unlockTxn_under (pfx key : GoString) (rev : w64) (hk : pfx <+: key) :
    (unlockTxn key rev).Under pfx := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [unlockTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [unlockTxn, List.mem_singleton] at hop
    subst hop
    show KeyRangeUnder pfx (opDeleteModel key []).key (opDeleteModel key []).base.rangeEnd
    rw [(deleteOp_fields key).1, (deleteOp_fields key).2]
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp [unlockTxn] at hop

/-- The guard on a sorted state: it holds iff `key` is there with create revision `rev`, for
`rev ≠ 0` (a missing key compares as create revision `0`). -/
theorem unlock_guard_iff (pfx key : GoString) (rev : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hrev : rev ≠ W64 0) :
    cmpHolds s (compareM (cmpKeyM .create key) .eq (.num rev)) = true ↔ HasKeyAt key rev s := by
  constructor
  · intro h
    by_cases hex : ∃ w ∈ s, w.key = key
    · obtain ⟨w, hw, hk⟩ := hex
      have hf := filter_key_single s hwf.1 key (fun v => inRange key [] v.key)
        (fun v => by simp [inRange]) w hw hk
      simp [cmpHolds, compareM, cmpKeyM, hf, cmpKv, int64Cmp, cmpSign, CmpOp.holds] at h
      refine ⟨w, hw, hk, ?_⟩
      revert h
      by_cases h1 : sint.Z w.createRev < sint.Z rev <;> by_cases h2 : w.createRev = rev <;>
        simp [h1, h2]
    · have hf : s.filter (fun v => inRange key [] v.key) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv hin
        simp [inRange] at hin
        exact hex ⟨v, hv, hin⟩
      exfalso
      have h2 : (W64 0) ≠ rev := fun e => hrev e.symm
      simp only [cmpHolds, compareM, cmpKeyM, hf, ite_true] at h
      simp only [cmpKv, zeroKv, int64Cmp, cmpSign, CmpOp.holds, h2, decide_false] at h
      repeat' split at h
      all_goals simp_all
  · rintro ⟨w, hw, hk, hc⟩
    have hf := filter_key_single s hwf.1 key (fun v => inRange key [] v.key)
      (fun v => by simp [inRange]) w hw hk
    simp [cmpHolds, compareM, cmpKeyM, hf, cmpKv, int64Cmp, cmpSign, CmpOp.holds, hc]

/-- **The fence** (etcd-io/etcd#22115), about the transaction `Unlock` commits: on a state (sorted)
where `key` is a later incarnation `(key, c')`, `c' ≠ c`, the fenced delete's guard fails and the
state is left unchanged. -/
theorem unlockTxn_keeps_later (pfx key : GoString) (c c' r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hc0 : c ≠ W64 0) (hne : c' ≠ c) (hk : HasKeyAt key c' s) :
    runTxn r s (unlockTxn key c) = (false, s, []) := by
  have hn : ¬ HasKeyAt key c s := fun h => hne (hasKeyAt_unique key c' c s hwf.1 hk h)
  have hok : cmpHolds s (compareM (cmpKeyM .create key) .eq (.num c)) = false := by
    cases h : cmpHolds s (compareM (cmpKeyM .create key) .eq (.num c))
    · rfl
    · exact absurd ((unlock_guard_iff pfx key c s hwf hc0).1 h) hn
  simp [runTxn, unlockTxn, TxnModel.branch, hok, runOps]

/-- **The old, unfenced delete** (`Delete(myKey)`, a one-operation transaction) removes every
incarnation of `key`, a later one included. -/
theorem deleteTxn_drops_key (key : GoString) (r : w64) (s : List EtcdKv) :
    ∀ v ∈ (runTxn r s (deleteTxn (opDeleteModel key []))).2.1, v.key ≠ key := by
  obtain ⟨hk, he⟩ := deleteOp_fields key
  intro v hv
  simp only [runTxn, deleteTxn, TxnModel.branch, List.all_nil, ite_true, runOps, applyTxnOp,
    hk, he] at hv
  simp [inRange] at hv
  exact hv.2

/-- When the guard holds, the transaction deletes exactly `key` (whose incarnation is then
`(key, rev)`). -/
theorem unlockTxn_deletes (pfx key : GoString) (rev r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hrev : rev ≠ W64 0) (hhas : HasKeyAt key rev s) :
    runTxn r s (unlockTxn key rev) =
      (true, s.filter (fun v => !decide (v.key = key)),
        [.delete (rangeIn s (opDeleteModel key [])).length]) := by
  obtain ⟨hk, he⟩ := deleteOp_fields key
  have hok := (unlock_guard_iff pfx key rev s hwf hrev).2 hhas
  simp [runTxn, unlockTxn, TxnModel.branch, hok, runOps, applyTxnOp, hk, he, inRange]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-- After `Unlock`'s committed transaction, the incarnation `(key, rev)` is gone at `r`. -/
theorem unlockTxn_unlocked (pfx key : GoString) (rev r : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf pfx s) (hrev : rev ≠ W64 0) :
    txnStates (GF := GF) pfx r s (runTxn r s (unlockTxn key rev)).2.1
        (txnWrote (runTxn r s (unlockTxn key rev)).2.2) ⊢
      unlockedAt pfx key rev r := by
  unfold unlockedAt
  by_cases hhas : HasKeyAt key rev s
  · rw [unlockTxn_deletes pfx key rev r s hwf hrev hhas]
    unfold txnStates
    split
    · iintro ⟨-, #H1⟩
      iexists _
      iframe H1
      ipureintro
      rintro ⟨v, hv, hk, -⟩
      simp only [List.mem_filter] at hv
      simp [hk] at hv
    · iintro #H
      iexists s
      iframe H
      ipureintro
      rename_i hw
      exfalso
      obtain ⟨w, hw', hwk, -⟩ := hhas
      have hm : w ∈ rangeIn s (opDeleteModel key []) :=
        (rangeIn_key key (opDeleteModel key []) s (deleteOp_fields key).1 (deleteOp_fields key).2 w).2 ⟨hw', hwk⟩
      have hlen := Nat.pos_iff_ne_zero.1 (List.length_pos_of_mem hm)
      apply hw
      simpa [txnWrote, TxnOpResult.wrote] using hlen
  · have hok : cmpHolds s (compareM (cmpKeyM .create key) .eq (.num rev)) = false := by
      cases h : cmpHolds s (compareM (cmpKeyM .create key) .eq (.num rev))
      · rfl
      · exact absurd ((unlock_guard_iff pfx key rev s hwf hrev).1 h) hhas
    have e : runTxn r s (unlockTxn key rev) = (false, s, []) := by
      simp [runTxn, unlockTxn, TxnModel.branch, hok, runOps]
    rw [e]
    unfold txnStates
    simp only [txnWrote, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iexists s
    iframe H
    ipureintro; exact hhas

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.Unlock.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hIO : Mutex.IsOwner.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG)) :
    Mutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx st ctx cs lo
  wp_start as ⟨#Hm, Hst, #Hctx, #Hlo⟩
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmpfx, %Hpfx, #Hsess, #Hcl⟩
  ihave Hci : (concurrencyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, ⟨%eL, #HeL⟩, -⟩
  unfold mutexState
  icases Hst with ⟨Hk, Hrv, Hh⟩
  wp_auto
  wp_if_destruct
  · -- myKey == ""
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    left; simpa using Hif
  wp_if_destruct
  · -- myRev <= 0
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    right; left; simpa using Hif
  wp_if_destruct
  · -- myKey == "\x00"
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    right; right; simpa using Hif
  rename_i Hk0 Hr0
  have Hnk : ¬ st.noKey := by
    unfold MutexSt.noKey
    have : sint.Z (W64 0) = 0 := by decide
    rw [this] at Hr0
    rintro (h | h | h)
    · exact Hk0 h
    · exact Hr0 h
    · exact Hif h
  have Hrev0 : st.rev ≠ W64 0 := by
    intro h; apply Hr0; rw [h]; decide
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply strings.wp_HasPrefix st.key pfx $$ [$Hstr]
  wp_if_destruct
  · wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
    ihave #Hcl' := Hcl
    iunfold isEtcdMutexClient at Hcl'
    icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, -, -, -, #HTxn, -, -⟩
    ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
    · iPkgInit
    ihave #Hnil := optsAt_nil (GF := GF)
    wp_apply hDel st.key slice.nil [] $$ [$Hcv $Hnil] as %opD #HopD
    · ipureintro; exact deleteOp_not_panics st.key
    (try wp_auto)
    wp_apply wp_slice_literal (l := [opD])
    isplitr
    · ipureintro; rfl
    iintro %slT ⟨HslT, -⟩
    ipersist HslT
    (try wp_auto)
    wp_apply hIO m st $$ [$Hpkg Hk Hrv Hh] as %c1 ⟨Hst, #Hc1⟩
    · unfold mutexState; iframe
    (try wp_auto)
    wp_apply wp_slice_literal (l := [c1])
    isplitr
    · ipureintro; rfl
    iintro %slC ⟨HslC, -⟩
    ipersist HslC
    (try wp_auto)
    iunfold isEtcdTxnKV at HTxn
    wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
    iunfold txnBuilderSpec at HBs
    icases HBs with ⟨#HIf, #HThen, -, #HCommit, -⟩
    wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .create st.key) .eq (.num st.rev)] : List CmpModel) [$HB]
    · isplitl
      · unfold cmpsAt
        iexists [c1]
        iframe HslC
        isplitr
        · ipureintro; rfl
        imodintro
        iintro %i %c %mm %Hc %Hmm
        rcases i with _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
        · simp at Hc
      · ipureintro; simp [TxnBuild.empty]
    inext
    iintro HB
    (try wp_auto)
    wp_apply_raw HThen $$ %_ %_ %([opDeleteModel st.key []] : List OpFull) %([.delete (opDeleteModel st.key [])] : List TxnOp) [$HB]
    · isplitl
      · unfold opsAt
        iexists [opD]
        iframe HslT
        isplitr
        · ipureintro; rfl
        imodintro
        iintro %i %v %o %Hv %Ho
        rcases i with _ | i
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopD
        · simp at Hv
      · ipureintro
        refine ⟨?_, rfl, rfl⟩
        simp only [List.map_cons, List.map_nil, unlock_deleteOp_txnOpOf]
    inext
    iintro HB
    (try wp_auto)
    ihave HB := B_conv B _ ({ model := unlockTxn st.key st.rev, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
    wp_apply HCommit $$ %({ model := unlockTxn st.key st.rev, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
    · ipureintro; exact unlockTxn_under pfx st.key st.rev Hif
    iunfold txnCommitResultTok at Hres
    icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts, -⟩)
    · obtain ⟨g, rfl⟩ : ∃ g, err = GoInterface.ok g := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok g => exact ⟨g, rfl⟩
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact Hne
      iunfold mutexState at Hst
      iexact Hst
    subst Heq
    ihave #Hun := unlockTxn_unlocked pfx st.key st.rev r s0 Hrr.2.2.2 Hrev0 $$ Hts
    unfold mutexState
    icases Hst with ⟨Hk, Hrv, Hh⟩
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    unfold MutexSt.released
    iframe
    iframe Hr Hun
    ipureintro
    exact ⟨Hnk, Hif, Hrr.1 rfl⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply fmt.wp_Errorf _ _ _ ?wf $$ [$Hsl] as %e -
  case wf =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .cons_string _ _ (.cons_string _ _ .nil)
  iapply HΦ
  iright; iright
  iframe
  ipureintro; simp

end proof

end concurrency
end EtcdGrove
end Perennial
