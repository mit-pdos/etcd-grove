/-
`(*clientv3.lessor).Leases(ctx)` (`client/v3/lease.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseLeases
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse__GetHeader
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

set_option maxHeartbeats 0 in
theorem lessor.Leases.wp_proof
    (wp_retry : retryLeaseClient.LeaseLeases.spec (GF := GF) (hG := hG))
    (wp_GetHeader : LeaseLeasesResponse.GetHeader.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    lessor.Leases.spec (GF := GF) (hG := hG) := by
  intro l addr Spec Q ctx cd
  wp_start as ⟨#Hrem, #Hrpc, #Hpre, #Hctx, #Hce⟩
  iunfold lessorRemoteAt at Hrem
  icases Hrem with ⟨%rlc, %conn, %sl, #Hremote, #Hrlc, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, -⟩
  wp_auto
  wp_apply wp_retry rlc conn addr Spec Q ctx cd _ _ sl vs $$ [«$a1»] as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    isplitl []
    · ipureintro; exact Hcap
    ipureintro; trivial
  iunfold leaseLeasesCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, HQ⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    iunfold leaseLeasesRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %rsl, %ps, #Hh, #Hhdr, #Hls, #Hps, %Hpl, #Hids⟩
    ihave %Hrsl := ownSlice_len $$ Hps
    wp_auto
    wp_apply (wp_slice_make2 (V := go_etcd_io.etcd.client.v3.LeaseStatus) rsl.len) as %lsl ⟨Hlsl, Hlcap⟩
    · ipureintro; word
    ihave %Hlsll := ownSlice_len $$ Hlsl
    simp only [List.length_replicate] at Hlsll
    have Hset : ∀ (j : Nat) (x : w64), j < sint.nat rsl.len → m.ids[j]? = some x →
        ((m.ids.take j).map go_etcd_io.etcd.client.v3.LeaseStatus.mk ++
          List.replicate (sint.nat rsl.len - j) (zero_val go_etcd_io.etcd.client.v3.LeaseStatus)).set j
          (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) =
        (m.ids.take (j + 1)).map go_etcd_io.etcd.client.v3.LeaseStatus.mk ++
          List.replicate (sint.nat rsl.len - (j + 1)) (zero_val go_etcd_io.etcd.client.v3.LeaseStatus) := by
      intro j x hj hx
      have hjl : j < m.ids.length := (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨r, hr⟩ : ∃ r, sint.nat rsl.len - j = r + 1 := ⟨sint.nat rsl.len - j - 1, by omega⟩
      rw [hr, List.take_add_one, hx, List.set_append_right _ _ (by simp; omega)]
      simp [List.replicate_succ, List.length_take, Nat.min_eq_left (Nat.le_of_lt hjl)]
      omega
    try wp_auto
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => iu
    ihave IH : iprop(∃ (k ku : w64),
        "i" ∷ i_ptr ↦ k ∗ "iu" ∷ iu_ptr ↦ ku ∗
        "Hlsl" ∷ lsl ↦* ((m.ids.take (sint.nat k)).map go_etcd_io.etcd.client.v3.LeaseStatus.mk ++
          List.replicate (sint.nat rsl.len - sint.nat k)
            (zero_val go_etcd_io.etcd.client.v3.LeaseStatus)) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rsl.len⌝) $$ [i iu Hlsl]
    · iexists W64 0, _
      simp only [named]
      rw [show sint.nat (W64 0) = 0 by rfl]
      simp only [List.take_zero, List.map_nil, List.nil_append, Nat.sub_zero]
      iframe
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat k < ps.length := by rw [Hrsl.1]; word
      obtain ⟨p, Hpi⟩ : ∃ p, ps[sint.nat k]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rsl.len := ⟨Hk.1, Hif⟩
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rsl (sint.Z k) ps DFrac.discard p Hk.1 $$ [Hps] as -
      · iframe #; ipureintro; exact Hpi
      try wp_auto
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rsl (sint.Z k) ps DFrac.discard p Hk.1 $$ [Hps] as -
      · iframe #; ipureintro; exact Hpi
      ihave ⟨%idk, %Hidk, #Hpid⟩ := BigSepL.bigSepL_lookup (Φ := fun j (q : Loc) => iprop(∃ id : w64,
          ⌜m.ids[j]? = some id⌝ ∗ structFieldRef etcdserverpb.LeaseStatus go!"ID" q ↦□ id)) Hpi $$ Hids
      try wp_auto
      have Hbt : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z lsl.len := ⟨Hk.1, by word⟩
      simp only [Hbt, and_self, ↓reduceIte]
      wp_apply wp_store_slice_index lsl (sint.Z k) _ (go_etcd_io.etcd.client.v3.LeaseStatus.mk idk)
        $$ [$Hlsl] as Hlsl
      · ipureintro; simp only [List.length_append, List.length_replicate, List.length_map,
          List.length_take]
        constructor <;> word
      rw [show (sint.Z k).toNat = sint.nat k by rfl, Hset (sint.nat k) idk (by word) Hidk]
      wp_for_post
      iframe
      iexists k + W64 1, k
      simp only [named]
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
      iframe
      ipureintro; constructor <;> word
    · have Hke : sint.nat k = m.ids.length := by rw [← Hpl, Hrsl.1]; word
      have Hlst : (m.ids.take (sint.nat k)).map go_etcd_io.etcd.client.v3.LeaseStatus.mk ++
          List.replicate (sint.nat rsl.len - sint.nat k) (zero_val go_etcd_io.etcd.client.v3.LeaseStatus)
          = m.ids.map go_etcd_io.etcd.client.v3.LeaseStatus.mk := by
        rw [Hke, List.take_length, show sint.nat rsl.len - m.ids.length = 0 by rw [← Hpl, Hrsl.1]; omega,
          List.replicate_zero, List.append_nil]
      rw [Hlst]
      ihave #Hpkg' : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
      · iPkgInit
      iapply wp_fupd
      wp_apply wp_GetHeader resp h DFrac.discard $$ [] as -
      · iframe #
        ipureintro; exact Hnn
      try wp_auto
      iStructNamed «$r0»
      ipersist ResponseHeader
      ipersist Leases
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists m, h, lsl
      iframe #
      iframe
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ctx cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      iapply HΦ
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, rfl⟩

end proof

end EtcdGrove
end Perennial
