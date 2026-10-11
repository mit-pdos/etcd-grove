/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/gatherOps.lean`. Lean-first (no Rocq
counterpart). `gatherOps` is recursive: the proof is by induction on the trees' size (`OpT.sizeL`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherOps
public import Spec.go_etcd_io.etcd.client.v3.Op__IsTxn
public import Spec.go_etcd_io.etcd.client.v3.Op__Txn
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem gatherOps_wp_size
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG)) :
    ∀ (N : Nat) (ts : List OpT), OpT.sizeL ts < N →
    ∀ (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ sl ↦*□ vs ∗ opListAtC true vs ts }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherOps)) (Val #sl))
  {{ (ret : GoSlice), RET #ret; opsOwn ret (OpT.leavesL ts) ∗
      ⌜∀ o ∈ OpT.leavesL ts, o.t ≠ W64 4⌝ }} := by
  intro N
  induction N with
  | zero => intro ts h; omega
  | succ N IH =>
  intro ts hts sl vs
  wp_start as ⟨#Hvs, Hts⟩
  ihave %Hlen := opListAtC_length true vs ts $$ Hts
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  ihave IH' : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (rsl : GoSlice)
      (rvs : List go_etcd_io.etcd.client.v3.Op),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "ret" ∷ ret_ptr ↦ rsl ∗ "#Hrsl" ∷ rsl ↦*□ rvs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op rsl (DFrac.own 1) ∗
      "#Hrel" ∷ listRel opFullAt rvs (OpT.leavesL (ts.take (sint.nat n))) ∗
      "Hrest" ∷ opListAtC true (vs.drop (sint.nat n)) (ts.drop (sint.nat n)) ∗
      "%Ht4" ∷ ⌜∀ o ∈ OpT.leavesL (ts.take (sint.nat n)), o.t ≠ W64 4⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op ret Hts]
  · iexists W64 0, _, slice.nil, []
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero,
      OpT.leavesL]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply listRel_nil
    ipureintro; constructor
    · intro o ho; simp at ho
    · constructor <;> word
  wp_for IH'
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨t, Hti⟩ : ∃ t, ts[sint.nat n]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hsize : t.size ≤ OpT.sizeL ts := OpT.size_le_of_getElem? ts _ t Hti
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) vs DFrac.discard v Hn.1 $$ [Hvs] as -
    · iframe #; ipureintro; exact Hvi
    icases opListAtC_drop true vs ts (sint.nat n) v t Hvi Hti $$ Hrest with ⟨Ht, Hrest⟩
    cases t with
    | leaf o =>
      iunfold opTAtC at Ht
      icases Ht with ⟨#Hat, %Ho4⟩
      wp_apply hIsTxn $$ [$op $Hat] as op
      rw [decide_eq_false Ho4]
      (try wp_auto)
      wp_apply wp_slice_literal (l := [v])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append_persistent rsl rvs _ [v] (DFrac.own 1)) $$ [$Hrsl $Hcap $Hz]
        as %rsl' ⟨#Hrsl', Hcap, -⟩
      wp_for_post
      iframe
      iexists (n + W64 1), v, rsl', rvs ++ [v]
      simp only [named]
      rw [Hn1, OpT.leavesL_take_succ ts _ _ Hti]
      simp only [OpT.leaves]
      iframe
      iframe #
      isplitr
      · iapply listRel_app
        iframe #
        iapply listRel_single
        iexact Hat
      ipureintro
      refine ⟨?_, by constructor <;> word⟩
      intro o' ho'
      rcases List.mem_append.1 ho' with h | h
      · exact Ht4 o' h
      · simp at h; subst h; exact Ho4
    | txn o cs ts' es' =>
      iunfold opTAtC at Ht
      icases Ht with ⟨#Hat, %Ho4, #Hcs, %tvs, %evs, #Htvs, #Hevs, Hcapt, Hts', Hes'⟩
      wp_apply hIsTxn $$ [$op $Hat] as op
      rw [decide_eq_true Ho4]
      (try wp_auto)
      wp_apply hTxn $$ [$op] as op
      (try wp_auto)
      simp only [↓reduceIte]
      wp_apply (wp_slice_append_persistent v.thenOps' tvs v.elseOps' evs DFrac.discard)
        $$ [$Htvs $Hcapt $Hevs] as %ns ⟨#Hns, -, -⟩
      have Hsz : OpT.sizeL (ts' ++ es') < N := by
        rw [OpT.sizeL_append]; simp only [OpT.size] at Hsize; omega
      ihave Hrec := opListAtC_append true tvs evs ts' es' $$ [$Hts' $Hes']
      wp_apply (IH (ts' ++ es') Hsz ns (tvs ++ evs)) $$ [$Hns $Hrec] as %r ⟨Hr, %Hr4⟩
      iunfold opsOwn at Hr
      icases Hr with ⟨%rvs2, #Hr2, -, %Hrl, #Hrr⟩
      (try wp_auto)
      wp_apply (wp_slice_append_persistent rsl rvs r rvs2 DFrac.discard) $$ [$Hrsl $Hcap $Hr2]
        as %rsl' ⟨#Hrsl', Hcap, -⟩
      wp_for_post
      iframe
      iexists (n + W64 1), v, rsl', rvs ++ rvs2
      simp only [named]
      rw [Hn1, OpT.leavesL_take_succ ts _ _ Hti, OpT.leaves_txn]
      iframe
      iframe #
      isplitr
      · iapply listRel_app
        iframe #
        iunfold listRel
        iframe #
        ipureintro; exact Hrl
      ipureintro
      refine ⟨?_, by constructor <;> word⟩
      intro o' ho'
      rcases List.mem_append.1 ho' with h | h
      · exact Ht4 o' h
      · exact Hr4 o' h
  · (try wp_auto)
    have hn : sint.nat n = ts.length := by
      rw [← Hlen]; word
    iapply HΦ
    rw [hn, List.take_length] at Ht4
    rw [hn, List.take_length] 
    iunfold opsOwn
    isplitl
    · iexists rvs
      iframe
      iframe #
      iunfold listRel at Hrel
      iexact Hrel
    ipureintro; exact Ht4

theorem gatherOps.wp_proof
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG)) :
    gatherOps.spec (GF := GF) (hG := hG) := by
  intro sl vs ts
  exact gatherOps_wp_size hIsTxn hTxn (OpT.sizeL ts + 1) ts (Nat.lt_succ_self _) sl vs

end proof

end leasing
end EtcdGrove
end Perennial
