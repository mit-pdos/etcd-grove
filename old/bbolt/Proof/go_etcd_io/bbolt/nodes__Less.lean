module
public import Spec.go_etcd_io.bbolt.nodes__Less
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem nodes.Less.wp_proof (hK : Inode.Key.spec (GF := GF) (hG := hG)) :
    nodes.Less.spec (GF := GF) (hG := hG) := by
  intro s xs dq i j a b av bv qa qb ia ib qia qib ita itb ka kb dka dkb Hi Hj Ha Hb Hia Hib
  wp_start as ⟨Hs, Ha', Hia', Hka, Hb', Hib', Hkb⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hial := ownSlice_len _ _ _ $$ Hia'
  ihave %Hibl := ownSlice_len _ _ _ $$ Hib'
  have hi := (List.getElem?_eq_some_iff.1 Ha).1
  have hj := (List.getElem?_eq_some_iff.1 Hb).1
  have hia := (List.getElem?_eq_some_iff.1 Hia).1
  have hib := (List.getElem?_eq_some_iff.1 Hib).1
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len from ⟨Hi, by word⟩))]
  wp_apply wp_load_slice_index s (sint.Z i) xs dq a Hi $$ [Hs] as Hs
  · iframe; ipureintro; exact Ha
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z av.inodes'.len
    from ⟨by decide, by word⟩))]
  icases ownSlice_elem_acc (sint.Z (W64 0)) ita _ _ ia (by decide) Hia $$ Hia' with ⟨Hita, Hiaback⟩
  wp_apply hK $$ [$Hita] as Hita
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len from ⟨Hj, by word⟩))]
  wp_apply wp_load_slice_index s (sint.Z j) xs dq b Hj $$ [Hs] as Hs
  · iframe; ipureintro; exact Hb
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z bv.inodes'.len
    from ⟨by decide, by word⟩))]
  icases ownSlice_elem_acc (sint.Z (W64 0)) itb _ _ ib (by decide) Hib $$ Hib' with ⟨Hitb, Hibback⟩
  wp_apply hK $$ [$Hitb] as Hitb
  try wp_auto
  wp_apply bytes.wp_Compare _ _ _ _ _ _ $$ [Hka Hkb] as ⟨Hka, Hkb⟩
  · iframe
  try wp_auto
  ihave Hia' := Hiaback $$ Hita
  ihave Hib' := Hibback $$ Hitb
  rw [show (sint.Z (W64 0)).toNat = 0 from rfl, list_set_lookup_self _ _ _ Hia, list_set_lookup_self _ _ _ Hib]
  have Hd : decide (bytes.compareResult ka kb = W64 (-1)) = decide (go.GoStringLt ka kb) :=
    decide_eq_decide.mpr (compareResult_eq_neg1 ka kb)
  rw [Hd]
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
