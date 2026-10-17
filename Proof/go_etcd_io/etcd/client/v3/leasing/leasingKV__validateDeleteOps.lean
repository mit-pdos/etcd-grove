/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__validateDeleteOps.lean` (etcd#22118).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__validateDeleteOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__validateDelete

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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.validateDeleteOps.wp_proof
    (hgather : gatherOps.spec (GF := GF) (hG := hG))
    (hval : leasingKV.validateDelete.spec (GF := GF) (hG := hG)) :
    leasingKV.validateDeleteOps.spec (GF := GF) (hG := hG) := by
  intro lkv pfx sl vs ts
  wp_start as ⟨#Hpfx, #Hsl, Hts⟩
  (try wp_auto)
  wp_apply hgather $$ [$Hsl $Hts] as %ret ⟨Hret, -⟩
  unfold opsOwn
  icases Hret with ⟨%rv, #Hrv, -, %Hlen, #Hall⟩
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrv
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "lkv" ∷ lkv_ptr ↦ lkv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (rv.length : Int) ∧
        ∀ j < sint.nat n, ∀ o, (OpT.leavesL ts)[j]? = some o → leaseDelRejected pfx o = false⌝)
      $$ [i op lkv]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; refine ⟨by word, by word, fun j hj => by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < rv.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, rv[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, (OpT.leavesL ts)[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ret.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ret (sint.Z n) rv DFrac.discard v Hn.1 $$ [Hrv] as -
    · iframe #; ipureintro; exact Hvi
    ihave #Hat := Hall $$ %(sint.nat n) %v %o %Hvi %Hoi
    (try wp_auto)
    wp_apply hval $$ [$Hpfx $Hat] as %err %Herr
    cases err with
    | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists (n + W64 1), v
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj o' ho' => ?_⟩
      by_cases hjn : j = sint.nat n
      · subst hjn; rw [Hoi] at ho'; cases ho'; exact Herr.1 rfl
      · exact Hn.2.2 j (by word) o' ho'
    | ok e =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      ipureintro
      refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
      have := h o (List.mem_of_getElem? Hoi)
      exact absurd (Herr.2 this) (by simp)
  · iapply HΦ
    ipureintro
    refine ⟨fun _ o ho => ?_, fun _ => rfl⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
    have hjl : j < rv.length := by
      rw [Hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    exact Hn.2.2 j (by word) o hj

end proof

end leasing
end EtcdGrove
end Perennial
