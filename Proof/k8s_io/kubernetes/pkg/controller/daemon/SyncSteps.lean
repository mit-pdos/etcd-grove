/-
**The sync path's short atomic steps** (Lean-first; the autoverify run, track B, Stage 3's glue).

* `apiState_past_le`: a past API state is before the current one.
* `s1Res_peek`: S1's invariant's content, read: its API state (the mirror's half, given back) and
  `s1Ok` of it.
* `s1_scene`: inside the two invariants, the current API state `σ` is well formed, after a past
  state `σp` the caller holds, and has the scenario's facts (`sceneOk`): what the glue proofs use
  to learn of the objects they read from caches (`podOf`, `crOf`, `dsWf` of a cached version's
  stored DaemonSet).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Trade
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Writes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer consistency workqueue

section pure
variable [GooseExts]

/-- A state of a history is before its last. -/
theorem histOk_le_last {H : List St} {σ σp : St} (hok : histOk (H ++ [σ]))
    (hm : σp ∈ H ++ [σ]) : St.le σp σ := by
  rcases List.mem_append.mp hm with h | h
  · exact (List.pairwise_append.mp hok.2).2.2 σp h σ (by simp)
  · simp only [List.mem_singleton] at h
    subst h
    exact St.le_refl _

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The daemon package's fact** (`daemonInit`): its variables, read-only for good. -/
theorem daemon_pkgFact :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ⊢
      _root_.Perennial.k8s_io.kubernetes.daemonInit := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon

/-- **A past state is before the current one**, which is well formed. -/
theorem apiState_past_le (γa : ApiNames) (σ σp : St) :
    ⊢ pastSt (GF := GF) γa σp -∗ apiState γa σ -∗ apiState γa σ ∗ ⌜St.le σp σ ∧ σ.wf⌝ := by
  iintro #Hp Hst
  iunfold apiState at Hst
  icases Hst with ⟨%H, Ha, %Hok⟩
  ihave #Hp2 := Hp
  iunfold pastSt at Hp2
  icases Hp2 with ⟨%H', #Hlb, %hp⟩
  ihave %hv := mono_list_auth_lb_valid γa.hist _ _ _ $$ Ha Hlb
  isplitl [Ha]
  · iunfold apiState; iexists H; iframe; ipureintro; exact Hok
  ipureintro
  exact ⟨histOk_le_last Hok (hv.2.subset hp.1), histOk_last_wf Hok⟩

/-- **S1's invariant's content, read**: its API state's mirror half (to give back) and `s1Ok`. -/
theorem s1Res_peek (γ : S1Names) (c : DscComp) :
    s1Res (GF := GF) γ c ⊢ ∃ σ, apiMirror γ σ ∗ (apiMirror γ σ -∗ s1Res γ c) ∗
      ⌜∃ M Lm C Ld, s1Ok σ M Lm C Ld⌝ := by
  iintro Hres
  iunfold s1Res at Hres
  icases Hres with ⟨%σ, %M, %Lm, %C, %D, %Ld, Hm, Hcs, Hta, %HD, Hlb, Hents, Hca, Hcl, #HLd,
    %Hok⟩
  iexists σ
  iframe Hm
  isplitl [Hcs Hta Hlb Hents Hca Hcl]
  · iintro Hm
    iunfold s1Res
    iexists σ, M, Lm, C, D, Ld
    iframe
    iframe #
    ipureintro
    exact ⟨HD, Hok⟩
  ipureintro
  exact ⟨M, Lm, C, Ld, Hok⟩

/-- **The scenario now**: the current API state is well formed, after `σp`, with `sceneOk`. -/
theorem s1_scene (γa : ApiNames) (γ : S1Names) (c : DscComp) (σp : St) :
    ⊢ apiInv (GF := GF) γa γ -∗ s1Inv γ c -∗ pastSt γa σp -∗
      |={⊤}=> ⌜∃ σ, sceneOk σ ∧ σ.wf ∧ St.le σp σ⌝ := by
  iintro #Hapi #Hs1 #Hp
  iunfold apiInv at Hapi
  iinv Hapi with >Hres1 Hclose1
  icases Hres1 with ⟨%σ, Hst, Hm1⟩
  iunfold s1Inv at Hs1
  iinv Hs1 with >Hres Hclose2
  · unfold s1N apiN; solve_ndisj
  ihave ⟨%σ', Hm, Hback, %Hok⟩ := s1Res_peek γ c $$ Hres
  iunfold apiMirror at Hm
  ihave %he := ghostVar_agree γ.mirror σ _ σ' _ $$ Hm1 Hm
  subst he
  ihave ⟨Hst, %hle⟩ := apiState_past_le γa σ σp $$ Hp Hst
  imod Hclose2 $$ [Hm Hback] with -
  · inext; iapply Hback; iunfold apiMirror; iexact Hm
  imod Hclose1 $$ [Hst Hm1] with -
  · inext; iexists σ; iframe
  imodintro
  ipureintro
  obtain ⟨M, Lm, C, Ld, h⟩ := Hok
  exact ⟨σ, h.scene, hle.2, hle.1⟩

end lemmas

end dsctl
end EtcdGrove
end Perennial
