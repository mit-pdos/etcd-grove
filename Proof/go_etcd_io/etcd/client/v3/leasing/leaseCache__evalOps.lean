/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__evalOps.lean`. `evalOps` tests
`resp == nil`: `freshGetResp` says the response is not nil. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__evalOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseKey__get
public import Spec.go_etcd_io.etcd.client.v3.leasing.isBadOp
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEvalLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

omit [AllG GF] package_sem in
/-- A fresh response is not nil. -/
theorem freshGetResp_nn (r : Loc) (hm : HdrM) (more : Bool) (count : w64) (kv : Option EtcdKv) :
    freshGetResp (GF := GF) r hm more count kv ⊢ ⌜r ≠ null⌝ := by
  unfold freshGetResp
  iintro ⟨%H, -⟩
  ipureintro; exact H

theorem leaseCache.evalOps.wp_proof
    (hget : leaseKey.get.spec (GF := GF) (hG := hG))
    (hbad : isBadOp.spec (GF := GF) (hG := hG))
    (hIsGet : Op.IsGet.spec (GF := GF) (hG := hG))
    (hKey : Op.KeyBytes.spec (GF := GF) (hG := hG)) :
    leaseCache.evalOps.spec (GF := GF) (hG := hG) := by
  intro lc st dq sl os
  wp_start as ⟨Hown, %Hwf, #Hops⟩
  unfold opsAt
  icases Hops with ⟨%vs, #Hvs, %Hlen, #Hv⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) sl.len $$ [] as %rsl ⟨Hrsl, Hrcap⟩
  · ipureintro; word
  irename : (i_ptr ↦ W64 0) => cnt
  rename_i iv_ptr
  irename : (iv_ptr ↦ zero_val w64) => iv
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (ivv : w64) (done : List Loc),
      "cnt" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "iv" ∷ iv_ptr ↦ ivv ∗
      "Hrsl" ∷ rsl ↦* (done ++ List.replicate (sint.nat sl.len - sint.nat n) (zero_val Loc)) ∗
      "Hown" ∷ lcOwn lc st dq ∗
      "Hdone" ∷ ([∗list] j ↦ p ∈ done, ∃ (o : OpFull) (e : LeaseEntry),
          ⌜os[j]? = some o ∧ st.entries !! o.key = some e⌝ ∗ respOpFresh p o e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int) ∧ done.length = sint.nat n ∧
        (os.take (sint.nat n)).all (fun o => decide (o.t = W64 1) && !isBadOpM o &&
          (st.entries !! o.key).isSome) = true⌝) $$ [cnt op iv Hrsl Hown]
  · iexists W64 0, _, _, []
    simp only [named]
    iframe
    isplitl []
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    ipureintro; refine ⟨by word, by word, rfl, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, os[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) vs DFrac.discard v Hn.1 $$ [Hvs] as -
    · iframe #; ipureintro; exact Hvi
    ihave #Hat := Hv $$ %(sint.nat n) %v %o %Hvi %Hoi
    wp_apply hIsGet $$ [$op $Hat] as op
    wp_if_destruct
    · wp_apply hbad $$ [$Hat]
      by_cases Hbad : isBadOpM o = true
      · rw [Hbad]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        isplitr
        · ipureintro; exact (leaseEvalOk_false st os _ o Hoi (by rw [Hbad]; simp)).symm
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      rw [Bool.eq_false_iff.mpr Hbad]
      wp_auto
      wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
      wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
      rw [lcOwn_def]
      icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
      wp_auto
      wp_apply wp_entries_lookup st _ o.key Hwf $$ [$Hemap] as Hemap
      cases hk : st.entries !! o.key with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        iframe #
        isplitr
        · ipureintro; exact (leaseEvalOk_false st os _ o Hoi (by simp [hk])).symm
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      | some e =>
        have hli : e.li ≠ null := Hwf.li_ne o.key e hk
        simp only [Option.map_some, Option.getD_some]
        icases (BigSepM.bigSepM_lookup_acc hk).1 $$ Hents with ⟨He, Hents⟩
        rw [entryOwn_def]
        icases He with ⟨%-, Hr, Hrev, Hwc, Hresp, #Hw⟩
        ihave Hlk := (leaseKey_struct e.li e.lk _ hli).1 $$ [Hr Hrev Hwc]
        · simp only [LeaseEntry.lk]; iframe
        rw [decide_eq_false hli]
        wp_auto
        wp_apply hget $$ [$Hlk $Hresp $Hat] as %ret ⟨Hlk, Hresp, Hret⟩
        icases keep_pure (freshGetResp_nn ret _ _ _ _) $$ [$Hret] with ⟨%Hretnn, Hret⟩
        icases (leaseKey_struct e.li e.lk _ hli).2 $$ Hlk with ⟨Hr, Hrev, Hwc⟩
        simp only [LeaseEntry.lk]
        ihave Hents := Hents $$ [Hr Hrev Hwc Hresp]
        · iframe; iframe #; ipureintro; exact hli
        rw [decide_eq_false Hretnn]
        wp_auto
        ihave %Hrlen := ownSlice_len $$ Hrsl
        have Hdl := Hn.2.2.1
        have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rsl.len := by
          refine ⟨Hn.1, ?_⟩
          have h1 := Hrlen.1
          rw [List.length_append, List.length_replicate] at h1
          word
        simp only [Hb2, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index rsl (sint.Z n) _ «$r0_ptr» $$ [$Hrsl] as Hrsl
        · ipureintro
          refine ⟨Hn.1, ?_⟩
          rw [List.length_append, List.length_replicate]
          word
        ihave %Hr0nn := typedPointsto_not_null $$ «$r0»
        iStructNamed «$r0»
        iStructNamed «$v0»
        ihave Hdone := (BigSepL.bigSepL_snoc (PROP := IProp GF)
          (Φ := fun j p => iprop(∃ (o : OpFull) (e : LeaseEntry),
            ⌜os[j]? = some o ∧ st.entries !! o.key = some e⌝ ∗ respOpFresh p o e))
          (l := done) (x := «$r0_ptr»)).2 $$ [Hdone Response ResponseRange Hret]
        · iframe
          iexists o, e
          rw [Hdl]
          unfold respOpFresh
          iframe
          ipureintro
          exact ⟨⟨Hoi, hk⟩, Hr0nn⟩
        wp_for_post
        iframe
        iexists (n + W64 1), v, n, done ++ [«$r0_ptr»]
        simp only [named]
        have hset : (sint.Z n).toNat = done.length := by rw [Hdl]
        rw [hset, set_done_replicate done _ _ _ (by word)]
        have hk1 : sint.nat sl.len - sint.nat n - 1 = sint.nat sl.len - sint.nat (n + W64 1) := by
          word
        rw [hk1]
        iframe
        iframe #
        ipureintro
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        refine ⟨by word, by word, by rw [List.length_append, Hdl, hn1]; rfl, ?_⟩
        rw [hn1, List.take_add_one, Hoi, List.all_append, Hn.2.2.2]
        simp [Hif, Bool.eq_false_iff.mpr Hbad, hk]
    · wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact (leaseEvalOk_false st os _ o Hoi (by rw [decide_eq_false Hif]; rfl)).symm
      ileft; ipureintro; exact ⟨rfl, rfl⟩
  · have hn : sint.nat n = os.length := by rw [← Hlen]; word
    have hok : leaseEvalOk st os = true := by
      have h := Hn.2.2.2; rw [hn, List.take_length] at h; exact h
    have hk0 : sint.nat sl.len - sint.nat n = 0 := by word
    rw [hk0, List.replicate_zero, List.append_nil]
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact hok.symm
    iright
    isplitr
    · ipureintro; rfl
    iexists done
    iframe
    ipureintro; rw [Hn.2.2.1, hn]

end proof

end leasing
end EtcdGrove
end Perennial
