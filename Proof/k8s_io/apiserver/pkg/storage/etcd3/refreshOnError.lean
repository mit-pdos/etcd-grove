/-
Lean-first (no Rocq counterpart).

The proof of `refreshOnError` for a current state: the first branch.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem refreshOnError.wp_proof : refreshOnError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ c st s err f x key ign R
  wp_start as ⟨Hs, Hf⟩
  iunfold ownStateX at Hs
  icases Hs with ⟨%m, %dsl, %Hst, Hst, #Hdsl, Hm⟩
  cases hcur : s.current with
  | true =>
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    isplitr
    · ipureintro; exact ⟨trivial, trivial⟩
    iunfold ownStateX
    rw [hcur]
    iexists m, dsl
    iframe Hst Hdsl Hm
    ipureintro; exact Hst
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hf with ⟨#Hget, Hmk⟩
    wp_auto
    wp_bind
    iunfold getStateOk at Hget
    iapply Hget $$ Hmk
    inext
    iintro %st' %e0 Hr
    wp_auto
    icases Hr with (#Hu | ⟨%σ, #HR, %hv, Hst'⟩)
    · ihave %hne := unkErr_ne c e0 $$ Hu
      cases e0 with
      | nil => exact absurd rfl hne
      | ok ii =>
        wp_auto
        iapply HΦ
        ileft
        iexact Hu
    · iunfold stAt at Hst'
      cases hf : mvcc.findKey key σ.kvs with
      | none =>
        cases ign with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hst' with ⟨%hst', He⟩
          iunfold storageErrIs at He
          icases He with ⟨%l, %hl, #Hl⟩
          have hne : e0 ≠ GoInterface.nil := by rw [hl]; exact fun h => by cases h
          subst hl
          wp_auto
          iapply HΦ
          iright
          iexists σ, _
          iframe HR
          isplitr
          · ipureintro; exact hv
          isplitl
          · iunfold stAt
            simp only [hf, Bool.false_eq_true, ↓reduceIte]
            isplitr
            · ipureintro; trivial
            iunfold storageErrIs
            iexists l
            iframe Hl
            ipureintro; rfl
          ipureintro
          simp only [hne, false_and, ↓reduceIte]
        | true =>
          simp only [↓reduceIte]
          icases Hst' with ⟨%he0, Hz⟩
          subst he0
          wp_auto
          iunfold ownState at Hz
          icases Hz with ⟨%x', %m', %dsl', %hnn, Hst2, Hobj, #Hdsl', Hm'⟩
          wp_auto
          have hmod : kubernetes.modAt key σ = W64 0 := by simp [kubernetes.modAt, hf]
          by_cases hr : s.rev = W64 0
          · rw [decide_eq_true hr]
            wp_auto
            iapply HΦ
            iright
            iexists σ, GoInterface.nil
            iframe HR
            isplitr
            · ipureintro; exact hv
            isplitl
            · iunfold stAt
              simp only [hf, ↓reduceIte]
              isplitr
              · ipureintro; trivial
              iunfold ownState
              iexists x', m', dsl'
              iframe Hst2 Hobj Hdsl' Hm'
              ipureintro; exact hnn
            ipureintro
            simp [hmod, hr]
          · rw [decide_eq_false hr]
            wp_auto
            iapply HΦ
            iright
            iexists σ, GoInterface.nil
            iframe HR
            isplitr
            · ipureintro; exact hv
            isplitl
            · iunfold stAt
              simp only [hf, ↓reduceIte]
              isplitr
              · ipureintro; trivial
              iunfold ownState
              iexists x', m', dsl'
              iframe Hst2 Hobj Hdsl' Hm'
              ipureintro; exact hnn
            ipureintro
            have : ¬ (kubernetes.modAt key σ = s.rev) := by rw [hmod]; exact fun h => hr h.symm
            simp [this]
      | some kv =>
        icases Hst' with ⟨%he0, %s', Hz, %hs'⟩
        subst he0
        wp_auto
        iunfold ownState at Hz
        icases Hz with ⟨%x', %m', %dsl', %hnn, Hst2, Hobj, #Hdsl', Hm'⟩
        wp_auto
        have hmod : kubernetes.modAt key σ = s'.rev := by simp [kubernetes.modAt, hf, hs'.1]
        by_cases hr : s.rev = s'.rev
        · rw [decide_eq_true hr]
          wp_auto
          iapply HΦ
          iright
          iexists σ, GoInterface.nil
          iframe HR
          isplitr
          · ipureintro; exact hv
          isplitl
          · iunfold stAt
            simp only [hf]
            isplitr
            · ipureintro; trivial
            iexists s'
            isplitl
            · iunfold ownState
              iexists x', m', dsl'
              iframe Hst2 Hobj Hdsl' Hm'
              ipureintro; exact hnn
            ipureintro; exact hs'
          ipureintro
          simp [hmod, hr]
        · rw [decide_eq_false hr]
          wp_auto
          iapply HΦ
          iright
          iexists σ, GoInterface.nil
          iframe HR
          isplitr
          · ipureintro; exact hv
          isplitl
          · iunfold stAt
            simp only [hf]
            isplitr
            · ipureintro; trivial
            iexists s'
            isplitl
            · iunfold ownState
              iexists x', m', dsl'
              iframe Hst2 Hobj Hdsl' Hm'
              ipureintro; exact hnn
            ipureintro; exact hs'
          ipureintro
          have : ¬ (kubernetes.modAt key σ = s.rev) := by rw [hmod]; exact fun h => hr h.symm
          simp [this]

end proof

end k8s
end EtcdGrove
end Perennial
