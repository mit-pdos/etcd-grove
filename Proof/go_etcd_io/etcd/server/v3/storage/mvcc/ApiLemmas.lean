/-
mvcc's candidate API's implementation, the lemmas its proofs share (`notes/mvcc-api-proof-plan.md`,
stage P5): the hook of the API's `mvccHook`, and the commit update a plain store's `End` runs, made
of the caller's two atomic updates (the notification, then the bump, both at the bump).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The API's hook is the store's** (`hookOk`: what today's `Write` and `End` take). -/
theorem mvccHook_hookOk (γ : MvccName) (P : IProp GF) (f : GoFunc) :
    mvccHook (GF := GF) γ P f ⊢ hookOk γ.st P #f := by
  unfold mvccHook mvccBackendIs mvccBackendIsI
  iintro ⟨%BP, %b, ⟨%d, %W, %Hd, -, #HP⟩, #Hf, %Hnn⟩
  obtain ⟨hkb, -, -⟩ := Hd
  have hB : mvccBackend γ = d.γB := by unfold mvccBackend; rw [hkb]
  iapply hookOk_of_init γ.st P #f d hkb f Hnn
  iunfold hookInit
  rw [hkb]
  iframe HP
  rw [← hB]
  iexact Hf

/-- The notified history of a state with nothing pending is its log. -/
theorem notifiedLog_none (σ : MvccState) (h : σ.pending = none) : σ.notifiedLog = σ.log := by
  unfold MvccState.notifiedLog; rw [h]

/-- A notification of nothing new (already pending) changes nothing. -/
theorem notify_pending (σ : MvccState) (pend : List Change) (hne : pend ≠ [])
    (h : σ.pending = some pend) : σ.notify pend = σ := by
  cases σ with
  | mk log crev pending =>
    simp only [MvccState.notify] at h ⊢
    subst h
    simp [hne]

/-- **The next log's key is free** in a certificate map of a history `L`: its entries are `L`'s
prefixes, shorter. -/
theorem certMapOk_fresh (M : GMap w64 Log) (L : Log) (pend : List Change) (h : certMapOk M L)
    (hlen : (L ++ [pend]).length < 2 ^ 63) :
    M.lookup (W64 ((L ++ [pend]).length : Int)) = none := by
  cases hM : M.lookup (W64 ((L ++ [pend]).length : Int)) with
  | none => rfl
  | some l =>
    exfalso
    obtain ⟨-, hk, hpre⟩ := h _ l hM
    have hl := hpre.length_le
    simp only [List.length_append, List.length_singleton] at hlen
    have hk' : W64 ((L.length + 1 : Nat) : Int) = W64 ((l.length : Nat) : Int) := by
      rw [← hk]; simp
    have := W64_inj_of_lt (a := L.length + 1) (b := l.length) (by omega) (by omega) hk'
    omega

/-- **The next log's certificate** keeps the map the notified history's. -/
theorem certMapOk_insert (M : GMap w64 Log) (L : Log) (pend : List Change) (h : certMapOk M L) :
    certMapOk (M.insert (W64 ((L ++ [pend]).length : Int)) (L ++ [pend])) (L ++ [pend]) := by
  intro n l hl
  rcases (GMap.lookup_insert_Some M _ n _ l).1 hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
  · exact ⟨by simp, rfl, List.prefix_refl _⟩
  · obtain ⟨a, b, c⟩ := h n l hl'
    exact ⟨a, b, c.trans (List.prefix_append _ _)⟩

/-- The caller's two commit updates (`End`'s, the candidate API's). -/
def commitAU (γ : MvccName) (pend : List Change) (Q : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvccState γ (σ.notify pend), COMM
        AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
          <{ mvccState γ σ'.commitPending, COMM Q }> }>)

/-- **The second update, at the notified state**: the bump, the abstract committed log advanced
(its three parts: the client's, `s.revMu`'s and the writer's), nothing pending. -/
theorem commit_second (γ : MvccName) (habs : γ.st.absQ = true) (hw : γ.watched = false) (ilog : Log)
    (pend : List Change)
    (hne : pend ≠ []) (Q : IProp GF) (hlen : (ilog ++ [pend]).length + 3 ≤ 2 ^ 63) :
    idxCert γ.st.idx (ilog ++ [pend]) ∗
    iprop(AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ σ'.commitPending, COMM Q }>) ∗
    ghostVar γ.st.abs (1 : Qp).half.half ilog ∗ ghostVar γ.st.abs (1 : Qp).half.half ilog ∗
    ghostVar γ.st.pnd (1 : Qp).half (some pend) ={⊤}=∗
      ghostVar γ.st.abs (1 : Qp).half.half (ilog ++ [pend]) ∗
      ghostVar γ.st.abs (1 : Qp).half.half (ilog ++ [pend]) ∗
      ghostVar γ.st.pnd (1 : Qp).half (none : Option (List Change)) ∗ Q := by
  iintro ⟨#Hc', Hau, Ha1, Ha2, Hp⟩
  ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤) (by simp) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hσ, Hucl⟩
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Hga, Hgp, Hgc, #Hgi, ⟨%M, HM, %HMok⟩, #Hpe, Hwl, %Hreach⟩
  ihave %Hl := ghostVar_agree γ.st.abs _ _ _ _ $$ Ha1 Hga
  ihave %Hpp := ghostVar_agree γ.st.pnd _ _ _ _ $$ Hp Hgp
  -- the abstract committed log, all of it, advanced
  ihave Ha12 : ghostVar γ.st.abs (1 : Qp).half ilog $$ [Ha1 Ha2]
  · have h := (ghostVar_fractional (GF := GF) γ.st.abs ilog).fractional (1 : Qp).half.half
      (1 : Qp).half.half
    rw [Qp.half_add_half] at h
    iapply h.2; iframe Ha1 Ha2
  subst Hl
  imod ghostVar_update_halves (σ.log ++ [pend]) γ.st.abs _ _ $$ Ha12 Hga with ⟨Ha12, Hga⟩
  imod ghostVar_update_halves (none : Option (List Change)) γ.st.pnd _ _ $$ Hp Hgp with ⟨Hp, Hgp⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  have hσ : σ.commitPending = { σ with log := σ.log ++ [pend], pending := none } := by
    unfold MvccState.commitPending; rw [← Hpp]; simp [commitLog, hne]
  imod Hcommit $$ [Hga Hgp Hgc HM Hwl] with HQ
  · iunfold mvccState
    iunfold mvccStateI
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    iframe Hwl
    rw [hσ]
    simp only
    iframe Hga Hgp Hgc Hc'
    isplitl [HM]
    · iexists M; iframe HM; ipureintro
      have : σ.notifiedLog = σ.log ++ [pend] := by
        unfold MvccState.notifiedLog; rw [← Hpp]
      unfold MvccState.notifiedLog; simp only; rw [← this]; exact HMok
    isplitr
    · iintro !> %x %hx; cases hx
    ipureintro
    refine ⟨?_, hlen⟩
    rw [← hσ]; exact MvccReachable.commit σ Hreach.1
  imodintro
  have h := (ghostVar_fractional (GF := GF) γ.st.abs (σ.log ++ [pend])).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  icases h.1 $$ Ha12 with ⟨Ha1, Ha2⟩
  iframe Ha1 Ha2 Hp HQ

/-- **The commit update of a plain store's `End`** (`absCommit`, from the caller's two updates):
both run at the bump. The first notifies (the pending revision's ghost, the client's half and the
writer's, at `some pend`; the next log's certificate in the client's map), unless the commit is
already notified (then it changes nothing); the second advances the abstract committed log
(`commit_second`). -/
theorem absCommit_of_au (γ : MvccName) (habs : γ.st.absQ = true) (hw : γ.watched = false) (ilog : Log)
    (pend : List Change)
    (hne : pend ≠ []) (Q : IProp GF) :
    commitAU γ pend Q ⊢ absCommit γ.st ilog pend Q := by
  iintro Hau
  unfold absCommit
  rw [if_neg hne]
  iintro %p %Hp %Hlen #Hc' ⟨HaR, Hwr⟩
  iunfold wrAt at Hwr
  icases Hwr with ⟨HaW, HpW⟩
  simp only [wrAt, absAt, pndAt, habs, ↓reduceIte]
  ihave #Hc'0 := Hc'
  iunfold idxCert at Hc'0
  icases Hc'0 with ⟨-, %Hwf, -, -⟩
  iunfold commitAU at Hau
  ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤) (by simp) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hσ, Hucl⟩
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Hga, Hgp, Hgc, #Hgi, ⟨%M, HM, %HMok⟩, #Hpe, Hwl, %Hreach⟩
  ihave %Hl := ghostVar_agree γ.st.abs _ _ _ _ $$ HaR Hga
  ihave %Hpp := ghostVar_agree γ.st.pnd _ _ _ _ $$ HpW Hgp
  subst Hl
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  rcases Hp with rfl | rfl
  · -- not yet notified: the notification, the next log certified
    have hpn : σ.pending = none := Hpp.symm
    have hok : certMapOk M σ.log := by rw [← notifiedLog_none σ hpn]; exact HMok
    have hkey := certMapOk_fresh M σ.log pend hok (by omega)
    imod ghost_map_insert_persist (W64 ((σ.log ++ [pend]).length : Int)) (σ.log ++ [pend]) hkey
      $$ HM with ⟨HM, #Hel⟩
    ihave #Hcok : certOk γ.st (σ.log ++ [pend]) $$ []
    · iunfold certOk; iright; ileft; iexact Hel
    imod ghostVar_update_halves (some pend) γ.st.pnd _ _ $$ HpW Hgp with ⟨HpW, Hgp⟩
    imod Hcommit $$ [Hga Hgp Hgc HM Hwl] with Hau2
    · iunfold mvccState
      iunfold mvccStateI
      simp only [MvccState.notify, if_neg hne]
      iframe Hwl
      iframe Hga Hgp Hgc Hgi
      isplitl [HM]
      · iexists _; iframe HM; ipureintro
        unfold MvccState.notifiedLog; simp only
        exact certMapOk_insert M σ.log pend hok
      isplitr
      · iintro !> %x %hx; cases hx; iexact Hcok
      ipureintro
      refine ⟨?_, Hreach.2⟩
      have hσ : ({ σ with pending := some pend } : MvccState) = σ.notify pend := by
        simp [MvccState.notify, hne]
      rw [hσ]
      exact MvccReachable.notify σ pend Hreach.1 hpn (LogWf.of_wf' Hwf.1 (by simp))
    ihave Hcs := commit_second γ habs hw σ.log pend hne Q Hlen
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down, tforall_cons, tforall_nil] at Hcs
    imod Hcs $$ [$Hc' $Hau2 $HaR $HaW $HpW] with ⟨Ha1, Ha2, Hp, HQ⟩
    imodintro
    iframe Ha1 Ha2 Hp HQ Hcok
  · -- already notified: the notification changes nothing
    ihave #Hcok := Hpe $$ %pend %Hpp.symm
    have hσ := notify_pending σ pend hne Hpp.symm
    isimp only [hσ] at Hcommit
    imod Hcommit $$ [Hga Hgp Hgc HM Hwl] with Hau2
    · iunfold mvccState
      iunfold mvccStateI
      iframe Hwl
      iframe Hga Hgp Hgc Hgi Hpe
      isplitl [HM]
      · iexists M; iframe HM; ipureintro; exact HMok
      ipureintro; exact Hreach
    ihave Hcs := commit_second γ habs hw σ.log pend hne Q Hlen
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down, tforall_cons, tforall_nil] at Hcs
    imod Hcs $$ [$Hc' $Hau2 $HaR $HaW $HpW] with ⟨Ha1, Ha2, Hp, HQ⟩
    imodintro
    iframe Ha1 Ha2 Hp HQ Hcok

/-- **A commit of nothing**: the caller's two updates, at the state (nothing pending: the writer's
half says so), change nothing. -/
theorem commitAU_nil (γ : MvccName) (habs : γ.st.absQ = true) (Q : IProp GF) :
    commitAU γ [] Q ∗ pndAt γ.st (1 : Qp).half none ={⊤}=∗ Q ∗ pndAt γ.st (1 : Qp).half none := by
  iintro ⟨Hau, HpW⟩
  simp only [pndAt, habs, ↓reduceIte]
  iunfold commitAU at Hau
  ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤) (by simp) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hσ, Hucl⟩
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Hga, Hgp, Hgc, #Hgi, HM, #Hpe, Hwl, %Hreach⟩
  ihave %Hpp := ghostVar_agree γ.st.pnd _ _ _ _ $$ HpW Hgp
  have hσ : σ.notify [] = σ := by
    cases σ with
    | mk log crev pending => simp only at Hpp; subst Hpp; simp [MvccState.notify]
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down, hσ] at Hcommit
  imod Hcommit $$ [Hga Hgp Hgc HM Hwl] with Hau2
  · iunfold mvccState
    iunfold mvccStateI
    iframe Hwl
    iframe Hga Hgp Hgc HM Hgi Hpe
    ipureintro; exact Hreach
  ihave Hau2 := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤) (by simp) $$ Hau2
  ihave Hacc := aupd_aacc $$ Hau2
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ', Hσ, Hucl⟩
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Hga, Hgp, Hgc, #Hgi, HM, #Hpe, Hwl, %Hreach⟩
  ihave %Hpp := ghostVar_agree γ.st.pnd _ _ _ _ $$ HpW Hgp
  have hσ : σ'.commitPending = σ' := by
    cases σ' with
    | mk log crev pending =>
      simp only at Hpp; subst Hpp; simp [MvccState.commitPending, commitLog]
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down, hσ] at Hcommit
  imod Hcommit $$ [Hga Hgp Hgc HM Hwl] with HQ
  · iunfold mvccState
    iunfold mvccStateI
    iframe Hwl
    iframe Hga Hgp Hgc HM Hgi Hpe
    ipureintro; exact Hreach
  imodintro
  iframe HQ HpW

/-- **A store's read transaction**, as `mvccTxn` holds it. -/
theorem mvccTxn_read_eq (mw : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) :
    mvccTxn (GF := GF) (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.read σ) ⊣⊢
      ∃ s : Loc, ⌜1 ≤ σ.log.length⌝ ∗ isMvccI s γ ∗
        isTxnRead mw s γ.st trace σ.log (W64 (σ.rev : Int)) σ.crev ∗ mvccLoan γ := by
  unfold mvccTxn mvccTxnI
  constructor
  · iintro ⟨%s, %Hl, #Hs, Hl', (⟨%mw', %Ht, Hr⟩ | ⟨%trw, %Ht, -⟩)⟩
    · simp only [interface_mkOk_inj, _root_.true_and] at Ht
      have hmw : mw' = mw := (GoGlobalContext.intoVal_inj_loc Ht).symm
      subst hmw
      iexists s
      iframe Hs Hr Hl'
      ipureintro; exact Hl
    · simp [interface_mkOk_inj, metricsTxnWrite.ty, txnReadWrite.ty] at Ht
  · iintro ⟨%s, %Hl, #Hs, Hr, Hl'⟩
    iexists s
    iframe Hs Hl'
    isplitr
    · ipureintro; exact Hl
    ileft
    iexists mw
    iframe Hr
    ipureintro; rfl

/-- **A store's read-only write transaction** (`NewReadOnlyTxnWrite`'s), as `mvccTxn` holds it. -/
theorem mvccTxn_ro_eq (trw : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) :
    mvccTxn (GF := GF) (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) γ trace (.read σ) ⊣⊢
      ∃ s : Loc, ⌜1 ≤ σ.log.length⌝ ∗ isMvccI s γ ∗
        isRoTxnWrite trw s γ.st trace σ.log (W64 (σ.rev : Int)) σ.crev ∗
        mvccLoan γ := by
  unfold mvccTxn mvccTxnI
  constructor
  · iintro ⟨%s, %Hl, #Hs, Hl', (⟨%mw, %Ht, -⟩ | ⟨%trw', %Ht, Hr⟩)⟩
    · simp [interface_mkOk_inj, metricsTxnWrite.ty, txnReadWrite.ty] at Ht
    · simp only [interface_mkOk_inj, _root_.true_and] at Ht
      have hmw : trw' = trw := (GoGlobalContext.intoVal_inj_loc Ht).symm
      subst hmw
      iexists s
      iframe Hs Hr Hl'
      ipureintro; exact Hl
  · iintro ⟨%s, %Hl, #Hs, Hr, Hl'⟩
    iexists s
    iframe Hs Hl'
    isplitr
    · ipureintro; exact Hl
    iright
    iexists trw
    iframe Hr
    ipureintro; rfl

/-- **A store's write transaction**, as `mvccTxn` holds it. -/
theorem mvccTxn_write_eq (mw : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Change) :
    mvccTxn (GF := GF) (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace
        (.write σ pend) ⊣⊢
      ∃ (s : Loc) (puts deletes putSize : w64),
        ⌜σ.pending = none ∧ 1 ≤ σ.log.length ∧ (γ.st.cm = false → σ.crev = -1)⌝ ∗ isMvccI s γ ∗
        isTxnWrite mw s γ.st trace σ.log pend puts deletes putSize σ.crev ∗
        mvccLoan γ := by
  unfold mvccTxn mvccTxnI
  constructor
  · iintro ⟨%mw', %s, %puts, %deletes, %putSize, %Hpl, #Hs, Hr, Hl', (%Ht | ⟨%tw, ⟨%Ht, -⟩, -⟩)⟩
    · simp only [interface_mkOk_inj, _root_.true_and] at Ht
      have hmw : mw' = mw := (GoGlobalContext.intoVal_inj_loc Ht).symm
      subst hmw
      iexists s, puts, deletes, putSize
      iframe Hs Hr Hl'
      ipureintro; exact Hpl
    · simp [interface_mkOk_inj, metricsTxnWrite.ty, watchableStoreTxnWrite.ty] at Ht
  · iintro ⟨%s, %puts, %deletes, %putSize, %Hpl, #Hs, Hr, Hl'⟩
    iexists mw, s, puts, deletes, putSize
    iframe Hs Hr Hl'
    isplitr
    · ipureintro; exact Hpl
    ileft; ipureintro; rfl

/-- **A store that does not compact has its compaction revision at `-1`** (`wsFrozenM`'s frozen
part, opened before the caller's update). -/
theorem crev_frozen_pre (γs : StoreNames) (q : Qp) (c : Int) (hc : -1 ≤ c) :
    wsFrozenM (GF := GF) γs ∗ crevUB γs.idx q c ={⊤}=∗ crevUB γs.idx q c ∗ ⌜γs.cm = false → c = -1⌝ := by
  iintro ⟨#Hfz, Hcu⟩
  cases hcm : γs.cm
  · iunfold wsFrozenM at Hfz
    isimp only [hcm, Bool.false_eq_true, ↓reduceIte] at Hfz
    imod crevFrozen_agree γs q c hc $$ Hfz Hcu with ⟨Hcu, %Hc1⟩
    imodintro; iframe Hcu; ipureintro; intro _; exact Hc1
  · imodintro; iframe Hcu; ipureintro; intro h; cases h

/-- **The client's compaction revision agrees** with a part of its authority: by the half the client
holds, or frozen at `-1`. -/
theorem crev_client_agree (γs : StoreNames) (q : Qp) (c σc : Int) (hc : -1 ≤ c) (hσ : -1 ≤ σc)
    (hfr : γs.cm = false → c = -1) :
    (if γs.cm then crevUB (GF := GF) γs.idx (1 : Qp).half σc else iprop(⌜σc = -1⌝)) ∗ crevUB γs.idx q c ⊢
      (if γs.cm then crevUB γs.idx (1 : Qp).half σc else iprop(⌜σc = -1⌝)) ∗ crevUB γs.idx q c ∗
        ⌜c = σc⌝ := by
  iintro ⟨Hg, Hcu⟩
  cases hcm : γs.cm
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hg with %Hg
    iframe Hcu
    ipureintro; exact ⟨Hg, by rw [hfr hcm, Hg]⟩
  · simp only [eq_self_iff_true, ite_true, ↓reduceIte]
    have hag : crevUB (GF := GF) γs.idx q c ∗ crevUB γs.idx (1 : Qp).half σc ⊢ ⌜c = σc⌝ := by
      iintro ⟨H1, H2⟩; iapply crevUB_agree γs.idx _ _ c σc hc hσ $$ H1 H2
    icases persistent_entails_right hag $$ [$Hcu $Hg] with ⟨%Hcc, Hcu, Hg⟩
    iframe Hg Hcu
    ipureintro; exact Hcc

/-- **A write transaction's compaction revision**, of a store that does not compact: `-1`. -/
theorem txn_crev_fact (γs : StoreNames) (mw s : Loc) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (crev : Int) :
    wsFrozenM (GF := GF) γs ∗ isTxnWrite mw s γs trace ilog pend puts deletes putSize crev ={⊤}=∗
      isTxnWrite mw s γs trace ilog pend puts deletes putSize crev ∗ ⌜γs.cm = false → crev = -1⌝ := by
  iintro ⟨#Hfz, Htx⟩
  cases hcm : γs.cm
  · iunfold wsFrozenM at Hfz
    isimp only [hcm, Bool.false_eq_true, ↓reduceIte] at Hfz
    imod isTxnWrite_frozenOf mw s γs trace ilog pend puts deletes putSize crev iprop(True) false
      $$ [$Hfz $Htx] with ⟨Htx, %Hc1⟩
    imodintro; iframe Htx; ipureintro; intro _; exact Hc1
  · imodintro; iframe Htx; ipureintro; intro h; cases h

end lemmas

end mvcc
end EtcdGrove
end Perennial
