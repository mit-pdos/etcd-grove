/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): over mvcc's API (`Txn.Rev`/`Txn.FirstRev` at the transaction's dynamic
type, `shapes.law`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG)) :
    txn.checkRange.spec (GF := GF) (hG := hG) := by
  intro t γ trace σ req o
  have hrz : (σ.log.length + 3 ≤ 2 ^ 63) → sint.Z (W64 (σ.rev : Int)) = (σ.rev : Int) := by
    intro h; unfold mvcc.api.MvccState.rev; word
  generalize hR : (W64 (σ.rev : Int) : w64) = rev at hrz ⊢
  wp_start as ⟨Htx, %Hreach, #Hr⟩
  icases txn.mvccTxn_shape hsh t γ trace (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
  obtain ⟨ty, v, rfl, hRev, hFirst, -⟩ := Hsh
  have hcr := txn.reach_crev σ Hreach.1
  have hlen := Hreach.2
  have hrz := hrz hlen
  have hRev' := hRev γ trace (.read σ)
  simp only [mvcc.api.MTxn.state] at hRev'
  rw [hR] at hRev'
  ihave #Hmp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hmp
  icases Hinit with ⟨-, ⟨%ec, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rv, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho, -⟩
  have hrv : o.base.rev = rv := by subst Ho; rfl
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Htx
    iunfold txn.checkRangeErr
    ileft; ipureintro
    exact ⟨rfl, Or.inl (by simp_all)⟩
  · skip
    have hne : ¬ rv = W64 0 := by simpa using Hif
    wp_apply hRev' $$ [$Htx] as Htx
    (try wp_auto)
    wp_if_destruct
    · skip
      have hlt : sint.Z rev < sint.Z rv := by simpa using Hif
      iapply HΦ
      iframe Htx
      iunfold txn.checkRangeErr
      iright; ileft
      isplitr
      · ipureintro; rw [hrv]; exact ⟨hne, hlt⟩
      iexists ef; iframe Hfut; ipureintro; rfl
    · skip
      have hle : ¬ sint.Z rev < sint.Z rv := by simpa using Hif
      have hm1 : sint.Z (W64 σ.crev) = σ.crev := by
        have : (σ.rev : Int) < 2 ^ 63 := by unfold mvcc.api.MvccState.rev; omega
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      wp_apply (hFirst γ trace (.read σ)) $$ [$Htx] as Htx
      wp_if_destruct
      · skip
        have hc : sint.Z rv < sint.Z (W64 σ.crev) := by simpa using Hif
        iapply HΦ
        iframe Htx
        iunfold txn.checkRangeErr
        iright; iright
        isplitr
        · ipureintro; rw [hrv]
          exact ⟨hne, by omega, by omega⟩
        iexists ec; iframe Hcomp; ipureintro; rfl
      · skip
        have hge : ¬ sint.Z rv < sint.Z (W64 σ.crev) := by simpa using Hif
        iapply HΦ
        iframe Htx
        iunfold txn.checkRangeErr
        ileft; ipureintro
        refine ⟨rfl, Or.inr ⟨by rw [hrv]; omega, by rw [hrv]; omega⟩⟩

end proof

end EtcdGrove
end Perennial
