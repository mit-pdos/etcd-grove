/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkAndGetPrevKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkAndGetPrevKV.wp_proof
    (hGet : txn.getPrevKV.spec (GF := GF) (hG := hG)) :
    txn.checkAndGetPrevKV.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ kind p o
  wp_start as ⟨%Htr, Htx, #Hp⟩
  ihave Hti : (txn.txnInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hti with ⟨-, ⟨%eK, #HeK⟩⟩
  wp_auto
  wp_apply (hGet trace mw s γ kind p o) $$ [$Htx $Hp] as %r ⟨Htx, Hr⟩
  · ipureintro; exact Htr
  iunfold txn.putRequestIs at Hp
  icases Hp with ⟨%Hpnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl,
    #Hpk, #Hiv, #Hil, -, %Ho⟩
  have hN : txn.needsPrev o = (iv || il) := by subst Ho; rfl
  have hR : txn.readsPrev o = ((iv || il) || pk) := by subst Ho; rfl
  have hK : o.key = k := by subst Ho; rfl
  rw [hN, hR, hK]
  cases hb : (iv || il)
  · -- no ignore flag: the answer
    have h2 : iv = false ∧ il = false := by cases iv <;> cases il <;> simp_all
    obtain ⟨rfl, rfl⟩ := h2
    wp_auto
    iapply HΦ
    iframe Htx
    ileft
    isplitl []
    · ipureintro; rfl
    isplitl []
    · ipureintro; intro h; cases h
    iexact Hr
  · -- an ignore flag: the key's key-value must be there
    simp only [Bool.true_or, ↓reduceIte]
    iunfold txn.prevKvIs at Hr
    icases Hr with ⟨%Hrn, %kvs, %ps, HK, Hps, Hm⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hps
    cases iv <;> cases il <;> simp only [Bool.false_or, Bool.or_false, Bool.false_eq_true] at hb <;>
      (try wp_auto)
    all_goals
      rw [decide_eq_false Hrn]
      wp_auto
      cases hf : mvcc.findKey k (txn.kindState kind) with
      | none =>
        icases Hm with %Hps0
        subst Hps0
        have hl : kvs.len = W64 0 := by
          rw [← mvcc.W64_sint_nat kvs.len Hlen.2, ← Hlen.1]; rfl
        rw [hl, decide_eq_true (rfl : (W64 0 : w64) = W64 0)]
        wp_auto
        iapply HΦ
        iframe Htx
        iright
        isplitl []
        · ipureintro; simp
        iunfold txn.errVarIs
        iexists eK
        iframe HeK
        ipureintro; rfl
      | some kv =>
        icases Hm with ⟨%pk, %Hps1, Hpk⟩
        subst Hps1
        have hl : kvs.len ≠ W64 0 := by
          intro h
          have := Hlen.1
          rw [h] at this
          have h0 : sint.nat (W64 0 : w64) = 0 := by decide
          rw [h0] at this
          simp at this
        rw [decide_eq_false hl]
        wp_auto
        iapply HΦ
        iframe Htx
        ileft
        isplitl []
        · ipureintro; rfl
        isplitl []
        · ipureintro; intro _; rfl
        iunfold txn.prevKvIs
        rw [hf]
        isplitl []
        · ipureintro; exact Hrn
        iexists kvs, [pk]
        iframe HK Hps
        iexists pk
        iframe Hpk
        ipureintro; rfl

end proof

end EtcdGrove
end Perennial
