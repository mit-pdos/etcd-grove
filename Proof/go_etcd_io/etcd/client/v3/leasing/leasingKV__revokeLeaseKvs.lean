/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__revokeLeaseKvs.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeLeaseKvs
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__leaseID
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revoke
public import Spec.strings.TrimPrefix
public import Spec.go_etcd_io.etcd.client.v3.OpGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- `maxCreateRev` of one more key-value. -/
theorem maxCreateRev_snoc (kvs : List EtcdKv) (v : EtcdKv) :
    maxCreateRev (kvs ++ [v]) =
      (if sint.Z (maxCreateRev kvs) < sint.Z v.createRev then v.createRev else maxCreateRev kvs) := by
  unfold maxCreateRev; rw [List.foldl_append]; rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.revokeLeaseKvs.wp_proof
    (hLID : leasingKV.leaseID.spec (GF := GF) (hG := hG))
    (hTP : EtcdGrove.strings.TrimPrefix.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hRev : leasingKV.revoke.spec (GF := GF) (hG := hG)) :
    leasingKV.revokeLeaseKvs.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs sl ps kvs
  wp_start as ⟨#Hlkv, Hrd, #Hsr, #Hctx, #Hcc, #Hsl, #Hkvs⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, -, -, #Hp, -⟩
  iunfold kvPtrsAt at Hkvs
  icases Hkvs with ⟨%Hlk, #Hkv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (kp : Loc),
      "i" ∷ i_ptr ↦ n ∗ "kv" ∷ kv_ptr ↦ kp ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "maxLeaseRev" ∷ maxLeaseRev_ptr ↦ maxCreateRev (kvs.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (kvs.length : Int)⌝) $$ [i kv Hrd maxLeaseRev]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by word
    obtain ⟨p, Hpi⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨v, Hvi⟩ : ∃ v, kvs[sint.nat n]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlk]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hpi
    ihave #Hv := Hkv $$ %(sint.nat n) %p %v %Hpi %Hvi
    iunfold kvValAt at Hv
    icases Hv with ⟨%ksl, %vsl, #HK, #Hks, #HC, -, -, -, -, #HL⟩
    wp_auto
    have Htake : kvs.take (sint.nat n + 1) = kvs.take (sint.nat n) ++ [v] :=
      by rw [List.take_succ, Hvi]; rfl
    wp_join iprop(maxLeaseRev_ptr ↦ maxCreateRev (kvs.take (sint.nat n + 1)))
      with [maxLeaseRev rev] as maxLeaseRev
    · rw [Htake, maxCreateRev_snoc, ite_eq_left (by assumption)]; iexact maxLeaseRev
    · rw [Htake, maxCreateRev_snoc, ite_eq_right (by assumption)]; iexact maxLeaseRev
    wp_apply hLID lkv γ pfx $$ [$Hpkg $Hlkv $Hrd $Hsr] as %id ⟨Hrd, %Hid⟩
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, p
      simp only [named]
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      iframe
      ipureintro; constructor <;> word
    wp_apply wp_bytes_to_string ksl v.key DFrac.discard $$ [$Hks] as -
    wp_apply hTP v.key pfx
    ihave #Hnil : optsAt (GF := GF) slice.nil ([] : List (OpFull → OpFull)) $$ []
    · unfold optsAt
      iexists ([] : List GoFunc)
      isplitl
      · iapply ownSlice_nil
      isplitl
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf
      simp at Hf
    wp_apply hGet (trimPrefixResult v.key pfx) slice.nil [] $$ [$Hnil] as %opv #Hopv
    · ipureintro; simp [opGetPanics, opFold, OpFull.newOp]
    ihave #H0 := etcdReached_zero (GF := GF)
    wp_apply hRev lkv γ pfx ctx cs (trimPrefixResult v.key pfx) opv
        (opGetModel (trimPrefixResult v.key pfx) []) (.get (opGetModel (trimPrefixResult v.key pfx) []))
        (W64 0) $$ [$Hpkg $Hlkv $Hrd $Hctx $Hcc $Hopv $H0]
      as %resp %err ⟨Hrd, -⟩
    · ipureintro
      simp [txnOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero]
    rcases err with e | _
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro; left; simp
    · wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      simp only [named]
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      iframe
      ipureintro; constructor <;> word
  · iapply HΦ
    iframe
    ipureintro; right; refine ⟨rfl, ?_⟩
    rw [List.take_of_length_le (by word)]

end proof

end leasing
end EtcdGrove
end Perennial
