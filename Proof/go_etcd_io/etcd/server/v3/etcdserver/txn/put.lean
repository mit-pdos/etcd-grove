/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

set_option hygiene false in
/-- The previous key-value found (`PrevKv`, or an ignore flag, with a key that exists): its
singleton slice and its `kvIs`, kept as `#Hkv0` for the answer (seven of the cases). -/
local macro "put_prev_found" : tactic => `(tactic| (
    iunfold txn.prevKvIs at Hprev
    icases Hprev with ⟨%Hpn, %kvs, %ps, HK, Hps, Hm⟩
    rw [hf]
    icases Hm with ⟨%pk', %Hps1, Hpk⟩
    subst Hps1
    ihave %Hlen := ownSlice_len _ _ _ $$ Hps
    have hlen1 : sint.Z kvs.len = 1 := by
      have h1 := Hlen.1; have h2 := Hlen.2
      simp only [List.length_singleton] at h1
      unfold sint.nat at h1; unfold sint.Z at *; omega
    have hbnd : 0 ≤ sint.Z (W64 0 : w64) ∧ sint.Z (W64 0 : w64) < sint.Z kvs.len := by
      rw [hb0, hlen1]; decide
    have hl0 : kvs.len ≠ W64 0 := by
      intro h; rw [h, hb0] at hlen1; exact absurd hlen1 (by decide)
    ipersist Hps
    ihave %Hpkn := txn.kvPtrIs_not_null true pk' kv $$ Hpk
    imod txn.kvPtrIs_kvIs pk' kv $$ Hpk with #Hkv
    ihave #Hkv0 := Hkv
    iunfold txn.kvIs at Hkv
    icases Hkv with ⟨%keySl, %valSl, #HkK, #HkKs, #HkC, #HkM, #HkVer, #HkV, #HkVs, #HkL⟩
  ))

set_option hygiene false in
/-- A read of `rr.KVs[0]`, the previous key-value (once per test that reads it). -/
local macro "put_load_prev" : tactic => `(tactic| (
    simp only [hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index kvs (sint.Z (W64 0 : w64)) [pk'] DFrac.discard pk' (by decide)
      $$ [$(frameH `Hps)] as -
    · ipureintro; rfl
    (try wp_auto)
  ))

set_option hygiene false in
/-- The put of value `v` (slice `vsl`, `#HVS`) with lease `l`, the trace field, and the answer
up to its `PrevKv`, which the caller gives (all ten cases). -/
local macro "put_reply" vsl:term:max v:term:max l:term:max : tactic => `(tactic| (
    wp_bind (App (App (App (Val #(methods tyX _ vX)) _) _) _)
    iapply mvcc.tw_wp3 tyX vX mw go!"Put" (by unfold mvcc.twMethod; simp)
    iframe Hwrap
    wp_apply (hPutM trace mw s γ ilog pend puts deletes putSize ksl $vsl k $v $l L)
      $$ [$(frameH `Htx) $(frameH `Hks) $(frameH `HVS) $(frameH `Hlok)
        $(frameH `Hown)]
      as ⟨Htx, Hown⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    ipersist RHeader
    ipersist HRevision
    ipersist RPrevKv
    icases mvcc.isTxnWrite_trace_acc mw s γ trace _ _ _ _ _ $$ Htx with ⟨⟨%te, Htrc⟩, Hback⟩
    wp_apply (hAdd trace te _ _ _) $$ [$(frameH `Htrc) $(frameH `Hfsl)] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil
    ihave Htx := Hback $$ [Htrc]
    · iexists te; iexact Htrc
    iapply HΦ
    iframe Hown
    isplitl [Htx]
    · iexists _, _; iexact Htx
    isplitr [HClusterId HMemberId HRaftTerm HLeaderId]
    rotate_left
    · iunfold txn.respHdrOwn; iexists _; iframe RHeader
      isplitr; · ipureintro; exact Hhn
      iexists _, _, _, _; iframe
    iunfold txn.putResponseIs
    isplitl []
    · ipureintro; exact Hrn
    iexists _, _
    iframe RHeader HRevision RPrevKv
  ))

set_option linter.unusedSimpArgs false in
theorem txn.put.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hPutM : mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG)) :
    txn.put.spec (GF := GF) (hG := hG) := by
  intro trace ctx cd mw s γ ilog pend puts deletes putSize p o prev L tyX vX crev
  wp_start as ⟨#Hctx, #Hct, Htx, #Hwrap, #Hp, Hprev, %Hneed, #Hlok, Hown⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iunfold txn.putRequestIs at Hp
  icases Hp with ⟨%Hpnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl,
    #Hpk, #Hiv, #Hil, -, %Ho, -⟩
  wp_auto
  wp_apply (hGet ctx (some trace)) $$ [$Hct] as %t ⟨%Ht, %Hteq⟩
  subst t
  (try wp_auto)
  irename «$r0» => Hresp
  irename «$r0» => Hhdr
  ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hresp
  ihave %Hhn := typedPointsto_not_null _ _ _ $$ Hhdr
  iStructNamedPrefix Hresp "R"
  iStructNamedPrefix Hhdr "H"
  generalize hst : txn.pendState ilog pend = st at *
  subst Ho
  simp only [txn.readsPrev, txn.needsPrev, txn.putChangeOf, txn.putValOf, txn.putLeaseOf,
    txn.putOpOf] at Hneed ⊢
  have hb0 : sint.Z (W64 0 : w64) = 0 := by decide
  iunfold txn.leaseOk at Hlok
  cases hf : mvcc.findKey k st with
  | none =>
    -- no previous key-value: no ignore flag
    have hiv : iv = false := by cases iv <;> simp_all
    have hil : il = false := by cases il <;> simp_all
    subst hiv hil
    simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    cases pk
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hprev with %Hpn
      wp_auto
      ihave #HVS := Hvs
      put_reply vsl v lease
      ipureintro; exact ⟨Hhn, rfl⟩
    · -- `PrevKv`: the answer has no key-value
      simp only [↓reduceIte]
      iunfold txn.prevKvIs at Hprev
      icases Hprev with ⟨%Hpn, %kvs, %ps, HK, Hps, Hm⟩
      rw [hf]
      icases Hm with %Hps0
      subst Hps0
      ihave %Hlen := ownSlice_len _ _ _ $$ Hps
      have hl : kvs.len = W64 0 := by
        rw [← mvcc.W64_sint_nat kvs.len Hlen.2, ← Hlen.1]; rfl
      wp_auto
      rw [decide_eq_false Hpn]
      wp_auto
      rw [hl, decide_eq_true (rfl : (W64 0 : w64) = W64 0)]
      (try wp_auto)
      ihave #HVS := Hvs
      put_reply vsl v lease
      ipureintro; exact ⟨Hhn, rfl⟩
  | some kv =>
    simp only [Option.map_some, Option.getD_some]
    cases iv <;> cases il <;> cases pk <;>
      simp only [Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, Bool.false_eq_true,
        ↓reduceIte] at Hneed ⊢
    · -- IgnoreValue false, IgnoreLease false, PrevKv false
      icases Hprev with %Hpn
      wp_auto
      ihave #HVS := Hvs
      put_reply vsl v lease
      ipureintro; exact ⟨Hhn, rfl⟩
    · -- IgnoreValue false, IgnoreLease false, PrevKv true
      put_prev_found
      wp_auto
      rw [decide_eq_false Hpn]
      wp_auto
      rw [decide_eq_false hl0]
      wp_auto
      put_load_prev
      ihave #HVS := Hvs
      put_reply vsl v lease
      isplitl []
      · ipureintro; exact Hhn
      isplitl []
      · ipureintro; exact Hpkn
      iexact Hkv0
    · -- IgnoreValue false, IgnoreLease true, PrevKv false
      put_prev_found
      wp_auto
      put_load_prev
      ihave #HVS := Hvs
      put_reply vsl v kv.lease
      ipureintro; exact ⟨Hhn, rfl⟩
    · -- IgnoreValue false, IgnoreLease true, PrevKv true
      put_prev_found
      wp_auto
      put_load_prev
      rw [decide_eq_false Hpn]
      wp_auto
      rw [decide_eq_false hl0]
      wp_auto
      put_load_prev
      ihave #HVS := Hvs
      put_reply vsl v kv.lease
      isplitl []
      · ipureintro; exact Hhn
      isplitl []
      · ipureintro; exact Hpkn
      iexact Hkv0
    · -- IgnoreValue true, IgnoreLease false, PrevKv false
      put_prev_found
      wp_auto
      put_load_prev
      ihave #HVS := HkVs
      put_reply valSl kv.value lease
      ipureintro; exact ⟨Hhn, rfl⟩
    · -- IgnoreValue true, IgnoreLease false, PrevKv true
      put_prev_found
      wp_auto
      put_load_prev
      rw [decide_eq_false Hpn]
      wp_auto
      rw [decide_eq_false hl0]
      wp_auto
      put_load_prev
      ihave #HVS := HkVs
      put_reply valSl kv.value lease
      isplitl []
      · ipureintro; exact Hhn
      isplitl []
      · ipureintro; exact Hpkn
      iexact Hkv0
    · -- IgnoreValue true, IgnoreLease true, PrevKv false
      put_prev_found
      wp_auto
      put_load_prev
      put_load_prev
      ihave #HVS := HkVs
      put_reply valSl kv.value kv.lease
      ipureintro; exact ⟨Hhn, rfl⟩
    · -- IgnoreValue true, IgnoreLease true, PrevKv true
      put_prev_found
      wp_auto
      put_load_prev
      put_load_prev
      rw [decide_eq_false Hpn]
      wp_auto
      rw [decide_eq_false hl0]
      wp_auto
      put_load_prev
      ihave #HVS := HkVs
      put_reply valSl kv.value kv.lease
      isplitl []
      · ipureintro; exact Hhn
      isplitl []
      · ipureintro; exact Hpkn
      iexact Hkv0

end proof

end EtcdGrove
end Perennial
