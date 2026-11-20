/-
`storage.BackendQuota.Cost`'s proof (`server/storage/quota.go`; etcdstorage, 2026-11-20, until then the
trust boundary, an axiom): a put's cost reads its key's and value's lengths (`costPut`), a
transaction's sums its branches' operations (`costTxn`, `costTxnReq`: a nested transaction
recursively, by induction on the operations' size), a lease grant's is a constant; over the
`RequestOp` getters' specs. `apply.quotaReqOk` holds the read-only fields it reads.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendQuota__Cost
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestPut
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequestTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [storage_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable [pb_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `costPut(r)` of a put request returns. -/
theorem storage.costPut_wp (r : Loc) (o : OpFull) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ txn.putRequestIs r o }}
      (App (Val (@! storage.costPut)) (Val #r))
    {{ (c : w64), RET #c; True }} := by
  wp_start as #Hr
  iunfold txn.putRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %vsl, %k, %v, %l, %pk, %iv, %il, #HK, -, #HV, -⟩
  wp_func_call
  wp_call
  wp_auto
  iapply HΦ
  done

/-- `costTxn(r)` of a transaction request with the fields `cs ts es` returns: by induction on the
size of its operations (a nested transaction's are smaller). -/
theorem storage.costTxn_wp
    (hPut : RequestOp.GetRequestPut.spec (GF := GF) (hG := hG))
    (hTxn : RequestOp.GetRequestTxn.spec (GF := GF) (hG := hG)) :
    ∀ (n : Nat) (r : Loc) (cs : List CmpModel) (ts es : List TxnOp),
      sizeOf ts + sizeOf es < n →
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ ⌜r ≠ null⌝ ∗
          txn.txnFieldsIs r cs ts es }}
        (App (Val (@! storage.costTxn)) (Val #r))
      {{ (c : w64), RET #c; True }} := by
  intro n
  induction n with
  | zero => intro r cs ts es h; omega
  | succ n ih =>
  intro r cs ts es hsz
  -- one operation of a branch (`costTxnReq`, inlined)
  have hreq : ∀ (p : Loc) (op : TxnOp), sizeOf op ≤ sizeOf ts + sizeOf es →
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
          txn.requestOpIs p op }}
        (App (Val (@! storage.costTxnReq)) (Val #p))
      {{ (c : w64), RET #c; True }} := by
    intro p op hop
    wp_start as #Hp
    wp_func_call
    wp_call
    wp_auto
    wp_apply (hPut p op) $$ [$Hp] as %rr Hrr
    icases Hrr with (⟨%o, %Ho, #Hr⟩ | %Hrn)
    · iunfold txn.putRequestIs at Hr
      icases Hr with ⟨%Hnn, -⟩
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hnn
      wp_apply (storage.costPut_wp rr o) $$ [] as %c -
      · iunfold txn.putRequestIs; iframe #; ipureintro; exact Hnn
      wp_auto
      iapply HΦ; done
    · obtain ⟨rfl, -⟩ := Hrn
      wp_auto
      wp_apply (hTxn p op) $$ [$Hp] as %tr Htr
      cases op
      case txn cs' ts' es' =>
        icases Htr with ⟨%Htn, #Hf⟩
        wp_auto
        wp_if_destruct
        · exact absurd rfl Htn
        have hlt : sizeOf ts' + sizeOf es' < n := by
          simp only [TxnOp.txn.sizeOf_spec] at hop; omega
        wp_apply (ih tr cs' ts' es' hlt) $$ [] as %c -
        · iframe #; ipureintro; exact Htn
        wp_auto
        iapply HΦ; done
      all_goals
        icases Htr with %Htn
        subst Htn
        wp_auto
        iapply HΦ; done
  wp_start as ⟨%Hrnn, #Hf⟩
  iunfold txn.txnFieldsIs at Hf
  icases Hf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hfl, #Hfs, #Hfm⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hss
  ihave %Hflen := ownSlice_len _ _ _ $$ Hfs
  wp_func_call
  wp_call
  wp_auto
  -- the success branch
  ihave IH : (∃ (k : w64) (uv : Loc) (acc : w64), "i" ∷ i_ptr ↦ k ∗ "u" ∷ u_ptr ↦ uv ∗
      "acc" ∷ sizeSuccess_ptr ↦ acc ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z ssl.len⌝ : IProp GF)
      $$ [i u sizeSuccess]
  · iexists W64 0, _, _
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hk0, hkl⟩ := Hk
    have hlt : sint.nat k < sps.length := by have := Hslen.1; word
    list_elem sps (sint.nat k) as p
    simp only [show (0 ≤ sint.Z k ∧ sint.Z k < sint.Z ssl.len) from ⟨hk0, Hif⟩, _root_.and_self,
      ite_true]
    wp_apply wp_load_slice_index ssl (sint.Z k) sps DFrac.discard p hk0 $$ [Hss] as -
    · iframe Hss; ipureintro; exact Hp_lookup
    ihave ⟨%op, %Hop, #Hp⟩ := txn.requestOpsIs_elem sps ts (sint.nat k) p Hp_lookup $$ Hsm
    have hle : sizeOf op ≤ sizeOf ts + sizeOf es := by
      have := List.sizeOf_lt_of_mem (List.mem_of_getElem? Hop); omega
    wp_auto
    wp_apply (hreq p op hle) $$ [] as %c -
    · iframe #
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, p, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_auto
  -- the failure branch
  ihave IH : (∃ (k : w64) (uv : Loc) (acc : w64), "i" ∷ i_ptr ↦ k ∗ "u" ∷ u_ptr ↦ uv ∗
      "acc" ∷ sizeFailure_ptr ↦ acc ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z fsl.len⌝ : IProp GF)
      $$ [i u sizeFailure]
  · iexists W64 0, _, _
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hk0, hkl⟩ := Hk
    have hlt : sint.nat k < fps.length := by have := Hflen.1; word
    list_elem fps (sint.nat k) as p
    simp only [show (0 ≤ sint.Z k ∧ sint.Z k < sint.Z fsl.len) from ⟨hk0, Hif⟩, _root_.and_self,
      ite_true]
    wp_apply wp_load_slice_index fsl (sint.Z k) fps DFrac.discard p hk0 $$ [Hfs] as -
    · iframe Hfs; ipureintro; exact Hp_lookup
    ihave ⟨%op, %Hop, #Hp⟩ := txn.requestOpsIs_elem fps es (sint.nat k) p Hp_lookup $$ Hfm
    have hle : sizeOf op ≤ sizeOf ts + sizeOf es := by
      have := List.sizeOf_lt_of_mem (List.mem_of_getElem? Hop); omega
    wp_auto
    wp_apply (hreq p op hle) $$ [] as %c -
    · iframe #
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, p, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_auto
  wp_if_destruct <;> (wp_auto; iapply HΦ; done)

theorem storage.BackendQuota.Cost.wp_proof
    (hPut : RequestOp.GetRequestPut.spec (GF := GF) (hG := hG))
    (hTxn : RequestOp.GetRequestTxn.spec (GF := GF) (hG := hG)) :
    storage.BackendQuota.Cost.spec (GF := GF) (hG := hG) := by
  intro q t r
  wp_start as #Hq
  iunfold apply.quotaReqOk at Hq
  wp_method_call
  wp_call
  wp_auto
  icases Hq with (⟨%Ht, %o, #Hr⟩ | ⟨%Ht, %m, #Hr⟩ | %Ht) <;> subst Ht
  · wp_auto
    wp_apply (storage.costPut_wp r o) $$ [] as %c -
    · iframe #
    wp_auto
    iapply HΦ; done
  · wp_auto
    iunfold txn.txnRequestIs at Hr
    icases Hr with ⟨%Hnn, #Hf⟩
    wp_apply (storage.costTxn_wp hPut hTxn _ r m.cmps m.thenOps m.elseOps (Nat.lt_succ_self _))
      $$ [] as %c -
    · iframe #; ipureintro; exact Hnn
    wp_auto
    iapply HΦ; done
  · wp_auto
    iapply HΦ; done

end proof

end EtcdGrove
end Perennial
