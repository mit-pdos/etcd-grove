/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__Rev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__fetch

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.Rev.wp_proof (hF : stm.fetch.spec (GF := GF) (hG := hG)) :
    stm.Rev.spec (GF := GF) (hG := hG) := by
  intro b pfx reads gs k
  wp_start as ⟨#Henv, Hrs, Hopts, %Hgs, %Hpk⟩
  wp_auto
  wp_apply wp_slice_literal (l := [k])
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hksl, -⟩
  ipersist Hksl
  wp_auto
  wp_apply hF b pfx reads gs _ [k] $$ [$Hpkg $Henv $Hrs $Hopts $Hksl] as %r Hr
  · ipureintro; refine ⟨Hgs, ?_⟩; simpa using Hpk
  iunfold stmRet at Hr
  icases Hr with (⟨%p, %Hrp, %reads', Hrs, Hopts, %Hgrow, Hp⟩ | %Hab)
  rotate_left
  · obtain ⟨err, Hne, rfl⟩ := Hab
    unfold stmAbort
    wp_auto
    iapply HΦ
    iapply stmRet_abort _ Hne
  subst Hrp
  wp_auto
  icases Hp with (%Hnil | ⟨%k', %e, %e', %Hke, #He⟩)
  · simp at Hnil
  obtain ⟨Hk', Hre, Hkv⟩ := Hke
  simp only [List.mem_singleton] at Hk'
  subst Hk'
  unfold readRespAt
  icases He with ⟨%Hpn, -, -, %sl, %ps, #Hsl, #Hps, #Hkvs⟩
  ihave %Hlen := ownSlice_len $$ Hps
  iunfold kvPtrsAt at Hkvs
  icases Hkvs with ⟨%Hl, #Hkv⟩
  rw [decide_eq_false Hpn]
  wp_auto
  rcases Hek : e.kv with _ | w
  all_goals simp only [Hek, Option.toList] at Hl ⊢
  · have Hlen0 : sl.len = W64 0 := by
      have : ps.length = 0 := by simpa using Hl
      rw [this] at Hlen; word
    rw [Hlen0]
    wp_auto
    iapply HΦ
    iapply stmRet_ret
    iexists reads'
    iframe Hrs Hopts
    ipureintro
    exact ⟨Hgrow, e', Hre, by simp [ReadM.modRev, Hkv, Hek]⟩
  · obtain ⟨kp, rfl⟩ : ∃ kp, ps = [kp] := by
      match ps, Hl with
      | [kp], _ => exact ⟨kp, rfl⟩
    have Hlen1 : sl.len ≠ W64 0 := by
      intro h; rw [h] at Hlen; simp at Hlen; revert Hlen; decide
    rw [decide_eq_false Hlen1]
    wp_auto
    ihave #Hw := Hkv $$ %0 %kp %w %rfl %rfl
    iunfold kvValAt at Hw
    icases Hw with ⟨%keySl, %valSl, -, -, -, #Hmr, -, -, -, -⟩
    have h0 : sint.Z (W64 0) = 0 := by decide
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
      rw [h0]; obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_singleton, sint.nat] at h1; simp only [sint.Z] at h2 ⊢; omega))]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) [kp] _ kp (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; rfl
    iapply HΦ
    iapply stmRet_ret
    iexists reads'
    iframe Hrs Hopts
    ipureintro
    exact ⟨Hgrow, e', Hre, by simp [ReadM.modRev, Hkv, Hek]⟩

end proof

end concurrency
end EtcdGrove
end Perennial
