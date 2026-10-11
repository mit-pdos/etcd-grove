/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__fetch
public import Spec.go_etcd_io.etcd.client.v3.concurrency.respToValue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.Get.wp_proof (hWG : writeSet.get.spec (GF := GF) (hG := hG))
    (hF : stm.fetch.spec (GF := GF) (hG := hG)) (hRV : respToValue.spec (GF := GF) (hG := hG)) :
    stm.Get.spec (GF := GF) (hG := hG) := by
  intro b pfx st gs ksl ks
  wp_start as ⟨#Henv, Hrs, Hws, Hopts, %Hgs, #Hks, %Hpk⟩
  unfold stmWsetOwn
  icases Hws with ⟨%m, %wsMap, Hf, Hm, #Hat⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply hWG m (DFrac.own 1) pfx wsMap st.writes ksl ks $$ [$Hpkg $Hm $Hat $Hks] as %p ⟨Hm, Hp⟩
  icases Hp with (⟨%Hpn, %Hnw⟩ | ⟨%k, %w, %sp, %Hw, Hp⟩)
  · obtain ⟨rfl, -⟩ := Hpn
    wp_auto
    wp_apply hF b pfx st.reads gs ksl ks $$ [$Hpkg $Henv $Hrs $Hopts $Hks] as %r Hr
    · ipureintro; exact ⟨Hgs, Hpk⟩
    iunfold stmRet at Hr
    icases Hr with (⟨%p, %Hrp, %reads', Hrs, Hopts, %Hgrow, Hp⟩ | %Hab)
    rotate_left
    · obtain ⟨err, Hne, rfl⟩ := Hab
      unfold stmAbort
      wp_auto
      iapply HΦ
      iapply stmRet_abort _ Hne
    subst Hrp
    icases Hp with (%Hnil | ⟨%k, %e, %e', %Hke, #He⟩)
    · obtain ⟨rfl, rfl⟩ := Hnil
      wp_apply hRV null [] $$ [$Hpkg]
      · ileft; ipureintro; exact ⟨rfl, rfl⟩
      iapply HΦ
      iapply stmRet_ret
      iexists reads'
      iframe Hrs Hopts
      isplitl [Hf Hm]
      · iexists m, wsMap
        iframe Hf Hm Hat
      ipureintro
      exact ⟨rfl, Hgrow, fun _ => rfl, fun h => absurd rfl h⟩
    · wp_apply hRV p e.value $$ [$Hpkg]
      · iright; iexists pfx, k, e; iframe He; ipureintro; rfl
      iapply HΦ
      iapply stmRet_ret
      iexists reads'
      iframe Hrs Hopts
      isplitl [Hf Hm]
      · iexists m, wsMap
        iframe Hf Hm Hat
      ipureintro
      obtain ⟨Hk, Hre, Hkv⟩ := Hke
      exact ⟨rfl, Hgrow, fun h => by simp [h] at Hk,
        fun _ => ⟨k, Hk, Or.inr ⟨Hnw k Hk, e', Hre, by simp [ReadM.value, Hkv]⟩⟩⟩
  · ihave %Hpnn := typedPointsto_not_null $$ Hp
    rw [decide_eq_false Hpnn]
    iStructNamed Hp
    wp_auto
    obtain ⟨Hk, Hwk, Hv⟩ := Hw
    iapply HΦ
    iapply stmRet_ret
    iexists st.reads
    iframe Hrs Hopts
    isplitl [Hf Hm]
    · iexists m, wsMap
      iframe Hf Hm Hat
    ipureintro
    refine ⟨rfl, ⟨fun _ _ h => h, fun k' h => Or.inl h⟩, fun h => by simp [h] at Hk, fun _ => ?_⟩
    exact ⟨k, Hk, Or.inl ⟨w, Hwk, Hv⟩⟩

end proof

end concurrency
end EtcdGrove
end Perennial
