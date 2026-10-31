/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__toRequestOp.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__toRequestOp
public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Proof.go_etcd_io.etcd.client.v3.OpTxnRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.toRequestOp.wp_proof (wp_toRangeRequest : Op.toRangeRequest.spec (GF := GF) (hG := hG))
    (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_GetCompare : Cmp.GetCompare.spec (GF := GF) (hG := hG)) :
    Op.toRequestOp.spec (GF := GF) (hG := hG) := by
  intro opv t
  obtain ⟨n, hn⟩ : ∃ n, sizeOf t = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing opv t with
  | ind n ih =>
  cases t with
  | leaf o =>
    wp_start as ⟨#HatT, %Hlv⟩
    iunfold opTAtC at HatT
    icases HatT with ⟨#Hat, -⟩
    obtain ⟨Ht, Hpv⟩ := Hlv o (by simp [OpT.leaves])
    simp only [OpT.wire]
    ihave #Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨Hat0, #Hkey, %Hf2, #Hval, -⟩
    iunfold opAt at Hat0
    icases Hat0 with ⟨%Hf, #Hend⟩
    unfold OpFields at Hf
    obtain ⟨ht, hko, -, -, hlease, hiv, hil, -⟩ := Hf2
    wp_auto
    rw [ht]
    rcases Ht with h1 | h2 | h3
    · rw [h1]
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      iapply wp_fupd
      wp_apply wp_toRangeRequest opv o $$ [] as %r ⟨%req, Hr, #Hk, #He, %Hreq⟩
      · iframe #; ipureintro; exact h1
      obtain ⟨Hreq, -⟩ := Hreq
      irename «$r0» => Hp
      ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
      ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hr
      iStructNamed Hp
      iStructNamed «$v0»
      iStructNamed Hr
      ipersist Request; ipersist RequestRange; ipersist Key; ipersist RangeEnd; ipersist Limit
      ipersist Revision; ipersist SortOrder; ipersist SortTarget; ipersist Serializable
      ipersist KeysOnly; ipersist CountOnly; ipersist MinModRevision; ipersist MaxModRevision
      ipersist MinCreateRevision; ipersist MaxCreateRevision
      imodintro
      iapply HΦ
      have hlw : leafWire o = .get (rangeWireOf o) := by simp [leafWire, h1]
      rw [hlw]
      unfold reqOpAt rangeReqAt
      isplitl []
      · ipureintro; exact Hpn
      iexists _, r
      iframe #
      isplitl []
      · ipureintro; exact Hrn
      ipureintro
      rw [← Hreq]; rfl
    · rw [h2]
      iapply wp_fupd
      wp_auto
      rename_i rp
      irename «$r0» => Hp
      irename : (rp ↦ (_ : etcdserverpb.PutRequest)) => «$r0»
      ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
      ihave %Hrn := typedPointsto_not_null _ _ _ $$ «$r0»
      iStructNamed Hp
      iStructNamed «$v0»
      iStructNamed «$r0»
      ipersist Request; ipersist RequestPut; ipersist Key; ipersist Value; ipersist Lease
      ipersist PrevKv; ipersist IgnoreValue; ipersist IgnoreLease
      imodintro
      iapply HΦ
      have hlw : leafWire o = txn.putTxnOp (putWireOf o) := by
        simp [leafWire, h2, show (W64 2 = W64 1) = False by decide]
      rw [hlw]
      iapply reqOpAt_put _ _ _ _ (by simpa [putWireOf, txn.putOpOf] using Hpv h2)
      iframe #
      isplitl []
      · ipureintro; exact Hpn
      unfold putReqAt
      isplitl []
      · ipureintro; exact Hrn
      iframe #
      ipureintro
      obtain ⟨-, hpk, -⟩ := Hf
      simp only [putWireOf, hlease, hpk, hiv, hil]
    · rw [h3]
      iapply wp_fupd
      wp_auto
      rename_i rp
      irename «$r0» => Hp
      irename : (rp ↦ (_ : etcdserverpb.DeleteRangeRequest)) => «$r0»
      ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
      ihave %Hrn := typedPointsto_not_null _ _ _ $$ «$r0»
      iStructNamed Hp
      iStructNamed «$v0»
      iStructNamed «$r0»
      ipersist Request; ipersist RequestDeleteRange; ipersist Key; ipersist RangeEnd; ipersist PrevKv
      imodintro
      iapply HΦ
      have hlw : leafWire o = .delete (deleteWireOf o) := by
        simp [leafWire, h3, show (W64 3 = W64 1) = False by decide,
          show (W64 3 = W64 2) = False by decide]
      rw [hlw]
      unfold reqOpAt deleteReqAt
      isplitl []
      · ipureintro; exact Hpn
      iexists _, _
      iframe #
      isplitl []
      · ipureintro; exact Hrn
      iframe #
      ipureintro
      obtain ⟨-, hpk, -⟩ := Hf
      simp only [deleteWireOf, hpk]
  | txn o cs ts es =>
    wp_start as ⟨#Hat, HlvI⟩
    icases HlvI with %Hlv
    ihave #Hat' := Hat
    iunfold opTAtC at Hat'
    icases Hat' with ⟨#Hf, %Ht, -⟩
    iunfold opFullAt at Hf
    icases Hf with ⟨-, -, %Hf2, -, -⟩
    obtain ⟨ht, -⟩ := Hf2
    iapply wp_fupd
    wp_auto
    rw [ht, Ht]
    wp_auto
    have hrec : ∀ t ∈ ts ++ es, ∀ v, Op.toRequestOp.specAt (GF := GF) (hG := hG) v t := by
      intro t htm v
      have hsz : sizeOf t < n := by
        rw [← hn]
        rcases List.mem_append.mp htm with h | h
        · have := List.sizeOf_lt_of_mem h; simp only [OpT.txn.sizeOf_spec]; omega
        · have := List.sizeOf_lt_of_mem h; simp only [OpT.txn.sizeOf_spec]; omega
      exact ih (sizeOf t) hsz v t rfl
    wp_method_call
    wp_auto
    wp_apply (toTxnRequest_core wp_Clone wp_GetCompare opv o cs ts es hrec) $$ [] as %r ⟨%Hrn, #Hr⟩
    · iframe #; ipureintro; exact Hlv
    irename «$r0» => Hp
    ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
    iStructNamed Hp
    iStructNamed «$v0»
    ipersist Request; ipersist RequestTxn
    imodintro
    iapply HΦ
    simp only [OpT.wire]
    iapply (reqOpAt_txn _ _ _ _).2
    isplitl []
    · ipureintro; exact Hpn
    iexists _, r
    iframe #
    ipureintro; exact Hrn

end proof

end EtcdGrove
end Perennial
