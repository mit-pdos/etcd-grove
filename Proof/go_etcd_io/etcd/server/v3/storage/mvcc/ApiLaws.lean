/-
**mvcc's candidate API's laws** (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, its "laws"
section), proved of its implementation (`ApiImpl.lean`), those its definitions support so far
(`notes/mvcc-api-proof-plan.md`). Each `<law>_proof` proves `<law>.law`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas

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
