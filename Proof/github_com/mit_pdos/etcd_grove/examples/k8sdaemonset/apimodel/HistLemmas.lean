/-
**The state's history and the operations' linearization points** (lemmas). The clients' half of
the history (`apiState`) and the lock invariant's agree; a write appends a later well-formed
state to both; a linearization point fires the caller's fancy update (`au_read`, `au_write`,
`au_noop`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode

section pure
variable [FfiSyntax]

theorem histOk_snoc {L : List St} {σ σ' : St} (h : histOk (L ++ [σ])) (hle : St.le σ σ')
    (hwf : σ'.wf) : histOk ((L ++ [σ]) ++ [σ']) := by
  obtain ⟨hw, hp⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw x hx
    · simp at hx; subst hx; exact hwf
  · rw [List.pairwise_append]
    refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    rcases List.mem_append.mp ha with ha | ha
    · have : St.le a σ := (List.pairwise_append.mp hp).2.2 a ha σ (by simp)
      exact St.le_trans this hle
    · simp at ha; subst ha; exact hle

theorem histOk_last_wf {L : List St} {σ : St} (h : histOk (L ++ [σ])) : σ.wf := h.1 σ (by simp)

end pure

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The two halves of the history agree. -/
theorem hist_agree (γ : ApiNames) (H1 H2 : List St) (σ1 σ2 : St) :
    monoListAuthOwn (GF := GF) γ.hist (1 : Qp).half (H1 ++ [σ1]) ∗
      monoListAuthOwn γ.hist (1 : Qp).half (H2 ++ [σ2]) ⊢ ⌜H1 = H2 ∧ σ1 = σ2⌝ := by
  iintro ⟨Ha, Hb⟩
  ihave %h := monoListAuthOwn_agree γ.hist _ _ _ _ $$ Ha Hb
  ipureintro
  have := List.append_inj' h.2 rfl
  exact ⟨this.1, by simpa using this.2⟩

theorem monoList_halves {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l ⊣⊢
      monoListAuthOwn γ 1 l := by
  have h := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact ⟨h.2, h.1⟩

/-- **A write's ghost update**: both halves take a later well-formed state. -/
theorem hist_update (γ : ApiNames) (H : List St) (σ σ' : St) (hok : histOk (H ++ [σ]))
    (hle : St.le σ σ') (hwf : σ'.wf) :
    ⊢ monoListAuthOwn (GF := GF) γ.hist (1 : Qp).half (H ++ [σ]) -∗
      monoListAuthOwn γ.hist (1 : Qp).half (H ++ [σ]) ==∗
      monoListAuthOwn γ.hist (1 : Qp).half ((H ++ [σ]) ++ [σ']) ∗
      monoListAuthOwn γ.hist (1 : Qp).half ((H ++ [σ]) ++ [σ']) ∗
      ⌜histOk ((H ++ [σ]) ++ [σ'])⌝ := by
  iintro Ha Hb
  ihave Hf := (monoList_halves (GF := GF) γ.hist (H ++ [σ])).1 $$ [$Ha $Hb]
  imod (monoListAuthOwn_update_app (GF := GF) (γ := γ.hist) (l := H ++ [σ]) [σ']) $$ Hf with ⟨Hf, -⟩
  ihave ⟨Ha, Hb⟩ := (monoList_halves (GF := GF) γ.hist ((H ++ [σ]) ++ [σ'])).2 $$ Hf
  imodintro
  iframe
  ipureintro
  exact histOk_snoc hok hle hwf

/-- A state of the history is a past state. -/
theorem pastSt_of_auth (γ : ApiNames) (q : Qp) (H : List St) (σ : St) (hok : histOk (H ++ [σ])) :
    monoListAuthOwn (GF := GF) γ.hist q (H ++ [σ]) ⊢ pastSt γ σ := by
  iintro Ha
  ihave #Hlb := monoListLbOwn_get γ.hist q _ $$ Ha
  unfold pastSt
  iexists (H ++ [σ])
  iframe #
  ipureintro
  exact ⟨by simp, histOk_last_wf hok⟩

/-- **A read's linearization point**: the caller's update fires at the state `σ` the lock
invariant holds. -/
theorem au_read (γ : ApiNames) (H : List St) (σ : St) (K : St → IProp GF) :
    monoListAuthOwn (GF := GF) γ.hist (1 : Qp).half (H ++ [σ]) ∗
      (|={⊤ \ ∅, ∅}=> ∃ σ', apiState γ σ' ∗ (apiState γ σ' -∗ |={∅, ⊤ \ ∅}=> K σ')) ⊢
      |={⊤}=> monoListAuthOwn γ.hist (1 : Qp).half (H ++ [σ]) ∗ K σ := by
  iintro ⟨Ha, HAU⟩
  rw [show (⊤ : CoPset) \ ∅ = ⊤ from by simp]
  imod HAU with ⟨%σ', Hst, Hcl⟩
  iunfold apiState at Hst
  icases Hst with ⟨%H', Hb, %Hok'⟩
  ihave %Hag := hist_agree γ H H' σ σ' $$ [$Ha $Hb]
  obtain ⟨-, Heq⟩ := Hag
  subst Heq
  imod Hcl $$ [Hb] with HK
  · iunfold apiState; iexists H'; iframe; ipureintro; exact Hok'
  imodintro
  iframe

/-- **A write's linearization point**: the caller's update fires from the state `σ` the lock
invariant holds to a later well-formed `σ'`, with the outcome `oc` it allows. -/
theorem au_write {O : Type} (γ : ApiNames) (H : List St) (σ σ' : St) (oc : O)
    (R : St → O → St → Prop) (K : St → St → O → IProp GF) (hok : histOk (H ++ [σ]))
    (hle : St.le σ σ') (hwf : σ'.wf) (hR : R σ oc σ') :
    monoListAuthOwn (GF := GF) γ.hist (1 : Qp).half (H ++ [σ]) ∗
      (|={⊤ \ ∅, ∅}=> ∃ σ0, apiState γ σ0 ∗
        (∀ σ1 o, apiState γ σ1 ∗ ⌜R σ0 o σ1⌝ -∗ |={∅, ⊤ \ ∅}=> K σ0 σ1 o)) ⊢
      |={⊤}=> monoListAuthOwn γ.hist (1 : Qp).half ((H ++ [σ]) ++ [σ']) ∗
        ⌜histOk ((H ++ [σ]) ++ [σ'])⌝ ∗ K σ σ' oc := by
  iintro ⟨Ha, HAU⟩
  rw [show (⊤ : CoPset) \ ∅ = ⊤ from by simp]
  imod HAU with ⟨%σ0, Hst, Hcl⟩
  iunfold apiState at Hst
  icases Hst with ⟨%H', Hb, %Hok'⟩
  ihave %Hag := hist_agree γ H H' σ σ0 $$ [$Ha $Hb]
  obtain ⟨HH, Heq⟩ := Hag
  subst Heq HH
  imod (hist_update γ H σ σ' hok hle hwf) $$ Ha Hb with ⟨Ha, Hb, %Hok2⟩
  imod Hcl $$ %σ' %oc [Hb] with HK
  · isplitl
    · iunfold apiState; iexists (H ++ [σ]); iframe; ipureintro; exact Hok2
    · ipureintro; exact hR
  imodintro
  iframe
  ipureintro; exact Hok2

/-- **A write with no effect** (`σ' = σ`), at the state the lock invariant holds. -/
theorem au_write_noop {O : Type} (γ : ApiNames) (H : List St) (σ : St) (oc : O)
    (R : St → O → St → Prop) (K : St → St → O → IProp GF) (hR : R σ oc σ) :
    monoListAuthOwn (GF := GF) γ.hist (1 : Qp).half (H ++ [σ]) ∗
      (|={⊤ \ ∅, ∅}=> ∃ σ0, apiState γ σ0 ∗
        (∀ σ1 o, apiState γ σ1 ∗ ⌜R σ0 o σ1⌝ -∗ |={∅, ⊤ \ ∅}=> K σ0 σ1 o)) ⊢
      |={⊤}=> monoListAuthOwn γ.hist (1 : Qp).half (H ++ [σ]) ∗ K σ σ oc := by
  iintro ⟨Ha, HAU⟩
  rw [show (⊤ : CoPset) \ ∅ = ⊤ from by simp]
  imod HAU with ⟨%σ0, Hst, Hcl⟩
  iunfold apiState at Hst
  icases Hst with ⟨%H', Hb, %Hok'⟩
  ihave %Hag := hist_agree γ H H' σ σ0 $$ [$Ha $Hb]
  obtain ⟨HH, Heq⟩ := Hag
  subst Heq HH
  imod Hcl $$ %σ %oc [Hb] with HK
  · isplitl
    · iunfold apiState; iexists H; iframe; ipureintro; exact Hok'
    · ipureintro; exact hR
  imodintro
  iframe

/-- **A failure without effect, before the lock** (`σ' = σ`, whatever `σ`): the update fires
with an outcome the relation allows at every state. -/
theorem au_fail {O : Type} (γ : ApiNames) (oc : O) (R : St → O → St → Prop)
    (K : St → St → O → IProp GF) (hR : ∀ σ, R σ oc σ) :
    (|={⊤ \ ∅, ∅}=> ∃ σ0, apiState γ σ0 ∗
        (∀ σ1 o, apiState γ σ1 ∗ ⌜R σ0 o σ1⌝ -∗ |={∅, ⊤ \ ∅}=> K σ0 σ1 o)) ⊢
      |={⊤}=> ∃ σ, K σ σ oc := by
  iintro HAU
  rw [show (⊤ : CoPset) \ ∅ = ⊤ from by simp]
  imod HAU with ⟨%σ0, Hst, Hcl⟩
  imod Hcl $$ %σ0 %oc [Hst] with HK
  · iframe; ipureintro; exact hR σ0
  imodintro
  iexists σ0
  iframe

/-- **A read that fails before the lock**: the update fires at whatever state. -/
theorem au_read_any (γ : ApiNames) (K : St → IProp GF) :
    (|={⊤ \ ∅, ∅}=> ∃ σ', apiState γ σ' ∗ (apiState γ σ' -∗ |={∅, ⊤ \ ∅}=> K σ')) ⊢
      |={⊤}=> ∃ σ, K σ := by
  iintro HAU
  rw [show (⊤ : CoPset) \ ∅ = ⊤ from by simp]
  imod HAU with ⟨%σ0, Hst, Hcl⟩
  imod Hcl $$ Hst with HK
  imodintro
  iexists σ0
  iframe

end lemmas

end apimodel
end EtcdGrove
end Perennial
