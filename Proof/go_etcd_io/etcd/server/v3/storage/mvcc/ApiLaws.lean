/-
**mvcc's candidate API's laws** (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, its "laws"
section), proved of its implementation (`ApiImpl.lean`), those its definitions support so far
(`notes/mvcc-api-proof-plan.md`). Each `<law>_proof` proves `<law>.law`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The state is exclusive: it holds the certificate map's whole authority. -/
theorem mvccState_excl_proof : mvccState_excl.law (GF := GF) := by
  intro γ σ σ'
  iintro ⟨H1, H2⟩
  iunfold mvccState at H1
  iunfold mvccStateI at H1
  iunfold mvccState at H2
  iunfold mvccStateI at H2
  icases H1 with ⟨-, -, -, -, ⟨%M1, HM1, -⟩, -⟩
  icases H2 with ⟨-, -, -, -, ⟨%M2, HM2, -⟩, -⟩
  ihave %Hv := ghostMapAuth_valid_2 γ.st.cok _ _ _ _ $$ HM1 HM2
  exfalso
  have h1 : (1 : Rat) + (1 : Qp).val ≤ 1 := Hv.1
  have := (1 : Qp).2
  grind

/-- Every state is reachable, its revisions fit (the state's own facts). -/
theorem mvccState_reachable_proof : mvccState_reachable.law (GF := GF) := by
  intro s γ σ
  iintro ⟨-, H⟩
  iunfold mvccState at H
  iunfold mvccStateI at H
  icases H with ⟨-, -, -, -, -, -, -, %Hr⟩
  ipureintro; exact Hr

/-- A write transaction pins the state (here always to its own: the writer's halves of the abstract
log and the pending revision agree with the client's, its compaction revision with the client's). -/
theorem mvccTxn_write_agree_proof : mvccTxn_write_agree.law (GF := GF) := by
  intro t γ trace σ pend σ'
  iintro ⟨Ht, Hs⟩
  iunfold mvccTxn at Ht
  iunfold mvccTxnI at Ht
  icases Ht with ⟨%mw, %s, %puts, %deletes, %putSize, %Hpl, #Hmv, Htx, -, -⟩
  obtain ⟨hp, -, hc⟩ := Hpl
  ihave #Hmv1 := Hmv
  iunfold isMvccI at Hmv1
  icases Hmv1 with ⟨-, %Hf, -⟩
  obtain ⟨habs, -⟩ := Hf
  iunfold mvccState at Hs
  iunfold mvccStateI at Hs
  icases Hs with ⟨Hga, Hgp, Hgc, -, -, -, -, %Hreach⟩
  icases isTxnWrite_wrAt mw s γ.st trace σ.log pend puts deletes putSize σ.crev iprop(True) false
    $$ Htx with ⟨Hwr, Htx⟩
  iunfold wrAt at Hwr
  icases Hwr with ⟨HaW, HpW⟩
  isimp only [absAt, habs, ↓reduceIte] at HaW
  isimp only [pndAt, habs, ↓reduceIte] at HpW
  ihave %Hl := ghostVar_agree γ.st.abs _ _ _ _ $$ HaW Hga
  ihave %Hp := ghostVar_agree γ.st.pnd _ _ _ _ $$ HpW Hgp
  have hcr : -1 ≤ σ'.crev := Hreach.1.crev_ge
  have hfin : σ.crev = σ'.crev → σ.pending = none ∧ (σ' = σ ∨ σ' = σ.notify pend) := by
    intro h
    refine ⟨hp, Or.inl ?_⟩
    cases σ with
    | mk l c p =>
      cases σ' with
      | mk l' c' p' =>
        simp only at Hl Hp h hp ⊢
        subst Hl h hp
        rw [← Hp]
  ihave Htx := Htx $$ [HaW HpW]
  · simp only [wrAt, absAt, pndAt, habs, ↓reduceIte]; iframe HaW HpW
  cases hcm : γ.st.cm
  · isimp only [hcm, Bool.false_eq_true, ↓reduceIte] at Hgc
    icases Hgc with %Hgc
    ipureintro; exact hfin (by rw [hc hcm, Hgc])
  · isimp only [hcm, ↓reduceIte] at Hgc
    ihave %Hcc := isTxnWrite_crev mw s γ.st trace σ.log pend puts deletes putSize σ.crev iprop(True)
      false _ σ'.crev hcr $$ [$Htx $Hgc]
    ipureintro; exact hfin Hcc

/-- The watchable store's write transaction is over a store's: its fields' persistent points-to,
the store's transaction, and the wrapper back from it (the watchable store, persistent, over the
transaction's store, which the names pin). -/
theorem mvccTxn_unwrap_proof : mvccTxn_unwrap.law (GF := GF) := by
  intro tw γ trace σ pend
  iintro Ht
  iunfold mvccTxn at Ht
  iunfold mvccTxnI at Ht
  icases Ht with ⟨%mw, %s, %puts, %deletes, %putSize, %Hpl, #Hmv, Htx, Hloan,
    (%Ht | ⟨%tw', ⟨%Ht, %hw⟩, #Htw, #Hws⟩)⟩
  · exfalso
    simp [interface_mkOk_inj, metricsTxnWrite.ty, watchableStoreTxnWrite.ty] at Ht
  simp only [interface_mkOk_inj, _root_.true_and] at Ht
  have htw : tw' = tw := (GoGlobalContext.intoVal_inj_loc Ht).symm
  subst htw
  ihave %Hsl := isMvccI_loc s γ $$ Hmv
  iexists mw
  ihave #Htw1 := Htw
  iStructNamed Htw1
  iframe TxnWrite
  isplitl [Htx Hloan]
  · iapply (mvccTxn_write_eq mw γ trace σ pend).2
    iexists s, puts, deletes, putSize
    iframe Hmv Htx Hloan
    ipureintro; exact Hpl
  iintro %σ' %pend' Ht'
  icases (mvccTxn_write_eq mw γ trace σ' pend').1 $$ Ht' with
    ⟨%s', %puts', %deletes', %putSize', %Hpl', #Hmv', Htx', Hloan'⟩
  ihave %Hsl' := isMvccI_loc s' γ $$ Hmv'
  have hs : s' = s := Hsl'.symm.trans Hsl
  subst hs
  iunfold mvccTxn
  iunfold mvccTxnI
  iexists mw, s', puts', deletes', putSize'
  iframe Hmv' Htx' Hloan'
  isplitr
  · ipureintro; exact Hpl'
  iright
  iexists tw'
  iframe Htw Hws
  ipureintro; exact ⟨rfl, hw⟩

/-- The range deleter is the watchable store's `Write` (`rdCode`, at its candidate
`watchableStore.Write.specC`). -/
theorem mvccDeleter_spec_proof (hW : watchableStore.Write.specC (GF := GF) (hG := hG)) :
    mvccDeleter_spec.law (GF := GF) := by
  intro rd γ P Pre Q f
  iintro #Hd
  iunfold mvccDeleter at Hd
  iunfold mvccDeleterI at Hd
  cases hw : γ.watched with
  | false =>
    isimp only [hw, Bool.false_eq_true, ↓reduceIte] at Hd
    icases Hd with %Hd
    exact Hd.elim
  | true =>
  isimp only [hw, ↓reduceIte] at Hd
  icases Hd with ⟨#Hrd, #Hwm, #Hpkg⟩
  iunfold rdCode at Hrd
  icases Hrd with ⟨%Hnn, #Hrd⟩
  ihave #Hc := Hrd $$ %(iprop(threadTok ∗ mvccHook γ P f ∗ Pre ∗ hookRun P f Pre Q))
    %(fun tr tw => iprop((∃ σ : MvccState, mvccTxn
      (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw) γ tr (.write σ [])) ∗ Q)) []
  · iintro %tr !> %Φ' ⟨⟨Htt, #Hh, HPre, Hrun⟩, %Htr, Htrc⟩ HΦ'
    iapply (hW γ.wl γ tr true P Pre Q f) $$ %Φ' [Htt Hh HPre Hrun Htrc] HΦ'
    iframe Hpkg Htt Hh HPre Hrun Htrc
    isplitr
    · iunfold isWatchableMvcc; iexact Hwm
    ipureintro; exact Htr
  iintro !> %Φ Hpre HΦ
  iapply Hc $$ %Φ Hpre
  inext
  iintro %tw ⟨%tr, ⟨%σ, Htx⟩, HQ⟩
  iapply HΦ
  iframe HQ
  iexists tr, σ
  iframe Htx
  ipureintro
  simp only [mvccWatched, hw, ↓reduceIte]
  exact ⟨tw, rfl⟩

/-- The watchable store's store. -/
theorem isWatchableMvcc_store_proof : isWatchableMvcc_store.law (GF := GF) := by
  intro ws γ
  iintro H
  iunfold isWatchableMvcc at H
  iunfold isWatchableMvccI at H
  icases H with ⟨%Hw, %st, #Hws, #Hm⟩
  isplitr
  · ipureintro; exact Hw.1
  iexists st
  ihave #Hws1 := Hws
  iunfold isWatchableStore at Hws1
  iNamed Hws1
  iframe Hst
  iunfold isMvcc; iexact Hm

/-- A store without watchers has them taken care of. -/
theorem mvccWatchersOk_unwatched_proof : mvccWatchersOk_unwatched.law (GF := GF) := by
  intro γ op hw
  iunfold mvccWatchersOk
  iunfold mvccWatchersOkI
  simp only [show γ.watched = false from hw, Bool.false_eq_true, ↓reduceIte]
  itrivial

/-- A commit of nothing needs no notification. -/
theorem mvccWatchersOk_nil_proof : mvccWatchersOk_nil.law (GF := GF) := by
  intro γ σ
  iunfold mvccWatchersOk
  iunfold mvccWatchersOkI
  split
  · ipureintro; rfl
  · itrivial

end laws

end mvcc
end EtcdGrove
end Perennial
