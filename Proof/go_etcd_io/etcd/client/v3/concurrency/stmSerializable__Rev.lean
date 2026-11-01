/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stmSerializable__Rev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Rev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stmSerializable.Rev.wp_proof (hGet : stmSerializable.Get.spec (GF := GF) (hG := hG))
    (hRev : stm.Rev.spec (GF := GF) (hG := hG)) :
    stmSerializable.Rev.spec (GF := GF) (hG := hG) := by
  intro lvl p pfx st k
  wp_start as ⟨Hst, %Hsp, %Hc⟩
  obtain ⟨Hser, Hpk⟩ := Hsp
  ihave ⟨Hst, %Hsz⟩ := stmState_sizeOk lvl pfx p st $$ Hst
  wp_auto
  wp_apply wp_slice_literal (l := [k])
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hksl, -⟩
  ipersist Hksl
  wp_auto
  wp_apply hGet lvl p pfx st _ [k] $$ [$Hpkg $Hst $Hksl] as %r Hr
  · ipureintro; refine ⟨⟨Hser, ?_⟩, Hc⟩; simpa using Hpk
  iunfold stmRet at Hr
  icases Hr with (⟨%v, %Hrv, %st1, Hst, %Hgp⟩ | %Hab)
  rotate_left
  · obtain ⟨err, Hne, rfl⟩ := Hab
    unfold stmAbort
    wp_auto
    iapply HΦ
    iapply stmRet_abort _ Hne
  subst Hrv
  wp_auto
  unfold stmState
  simp only [stmBase, Hser, ↓reduceIte]
  icases Hst with ⟨#Henv, Hrs, Hws, ⟨%gs, Hopts, %Hgs⟩, #Hcf, ⟨%pre, Hpre, %HpreOk⟩, -⟩
  have Hgs' : ReadOptsOk gs := by
    unfold GetOptsOk at Hgs
    rw [Hser] at Hgs
    simp only [↓reduceIte] at Hgs
    rcases Hgs with h | ⟨S, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨S, h⟩)
  wp_apply hRev (structFieldRef stmSerializable go!"stm" p) pfx st1.reads gs k $$ [$Hpkg $Henv $Hrs $Hopts] as %r' Hr
  · ipureintro; exact ⟨Hgs', Hpk, Hc.2.1 k (List.mem_singleton_self _)⟩
  iunfold stmRet at Hr
  icases Hr with (⟨%r, %Hr', %reads', Hrs, Hopts, %Hrv⟩ | %Hab)
  rotate_left
  · obtain ⟨err, Hne, rfl⟩ := Hab
    unfold stmAbort
    wp_auto
    iapply HΦ
    iapply stmRet_abort _ Hne
  subst Hr'
  wp_auto
  obtain ⟨Hgw, Hgg, -, -, Hgv⟩ := Hgp
  obtain ⟨Hrg, e, Hre, Hr⟩ := Hrv
  have Hgrow : ReadsGrow st.reads reads' [k] := by
    refine ⟨fun k' e' h => Hrg.1 k' e' (Hgg.1 k' e' h), fun k' h => ?_⟩
    rcases Hrg.2 k' h with h' | h'
    · exact Hgg.2 k' h'
    · exact Or.inr h'
  have Hsz' := STMSizeOk_reads Hsz Hc Hgrow
  rw [← Hgw] at Hsz'
  iapply HΦ
  iapply stmRet_ret
  iexists ({ reads := reads', writes := st1.writes, n := st.n + 1 } : STMSt)
  iframe Henv Hrs Hws Hcf
  isplitl [Hopts Hpre]
  · isplitl [Hopts]
    · iexists gs; iframe Hopts; ipureintro; exact Hgs
    isplitl [Hpre]
    rotate_left
    · ipureintro; exact Hsz'
    iexists pre; iframe Hpre; ipureintro
    intro k' hr hp
    by_cases hk : k' = k
    · subst hk
      rcases Hgv (by simp) with ⟨k'', hk'', hw | ⟨hnw, e1, he1, -⟩⟩
      · simp only [List.mem_singleton] at hk''; subst hk''
        obtain ⟨w, hw, -⟩ := hw
        show (st1.writes !! k'').isSome
        rw [Hgw, hw]; rfl
      · simp only [List.mem_singleton] at hk''; subst hk''
        exact HpreOk k'' (by rw [he1]; rfl) hp
    · rcases Hrg.2 k' hr with h | h
      · exact HpreOk k' h hp
      · simp at h; exact absurd h hk
  ipureintro
  exact ⟨Hgw, Hgrow, rfl, e, Hre, Hr⟩

end proof

end concurrency
end EtcdGrove
end Perennial
