/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__MemberByName.lean`
(claim #34, stage 2, 2026-11-25). Lean-first.

The cluster's mutex locked and unlocked owned (`OwnedMutex.lean`); the members map's range keeps in
`memb` the member named `name` (the loop's invariant: `memb` is `k`'s member once `k`'s key has been
ranged over, nil before). No two members share the name (`memNamesUniq`), so when the range meets
`k`'s member `memb` is still nil and `lg.Panic` is not reached; the answer is `memb.Clone()`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberByName
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member__Clone
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.OwnedMutex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member's name, borrowed. -/
theorem membership.memberAt_name_acc (m : Loc) (q : Qp) (mm : apply.MemberM) :
    membership.memberAt (GF := GF) m q mm ⊢
      membership.mNameAddr m ↦{DFrac.own q} mm.name ∗
      (membership.mNameAddr m ↦{DFrac.own q} mm.name -∗ membership.memberAt m q mm) := by
  unfold membership.memberAt
  iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  iframe Hnm
  iintro Hnm
  isplitr; (ipureintro; exact Hnn)
  iexists pu, cu; iframe

theorem membership.RaftCluster.MemberByName.wp_proof
    (hClone : membership.Member.Clone.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.MemberByName.spec (GF := GF) (hG := hG) := by
  intro c q ms mem name k mm huniq hk hname
  wp_start as ⟨Hmu, Hmem⟩
  iunfold membership.memAt at Hmem
  icases Hmem with ⟨%mp, Hfl, Hmap, %Hdom, Hmems⟩
  -- `k`'s member's location
  obtain ⟨vk, hvk⟩ : ∃ vk, ms !! k = some vk := by
    have hs : (ms !! k).isSome := by rw [Hdom.1 k, hk]; rfl
    exact Option.isSome_iff_exists.1 hs
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock_owned $$ [$Hmu] as Hmu
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(
      ∃ (mb x : Loc),
      "%Hi" ∷ ⌜0 ≤ i ∧ mb = if k ∈ keys.take i.toNat then vk else null⌝ ∗
      "memb" ∷ memb_ptr ↦ mb ∗
      "Hmems" ∷ ([∗map] k ↦ m ∈ ms, membership.memberAt m q ((mem !! k).getD default)) ∗
      "m" ∷ m_ptr ↦ x)) $$ Hmap
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [memb m Hmems]
  · iexists null, zero_val Loc
    simp only [named, Int.toNat_zero, List.take_zero, List.not_mem_nil, ↓reduceIte]
    iframe memb m Hmems
    ipureintro; exact ⟨by omega, rfl⟩
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    obtain ⟨Hi0, Hmb⟩ := Hi
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun (k : w64) (m : Loc) => membership.memberAt (GF := GF) m q
        ((mem !! k).getD default)) Hvv).1 $$ Hmems
      with ⟨Hown, Hmclose⟩
    icases membership.memberAt_name_acc vv q _ $$ Hown with ⟨Hnm, Hnback⟩
    (try wp_auto)
    ihave Hown := Hnback $$ Hnm
    ihave Hmems := Hmclose $$ Hown
    -- the key's member's value
    obtain ⟨mk, hmk⟩ : ∃ mk, mem !! key = some mk := by
      have hs : (mem !! key).isSome := by rw [← Hdom.1 key, Hvv]; rfl
      exact Option.isSome_iff_exists.1 hs
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have hkey_notin : key ∉ keys.take i.toNat := by
      intro hin
      obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hin
      rw [List.getElem_take] at hjk
      have hj' : j < i.toNat := by rw [List.length_take] at hj; omega
      have hilt : i.toNat < keys.length := (List.getElem?_eq_some_iff.1 Hkey).1
      have := (Hknodup.getElem_inj (hi := by omega) (hj := hilt)).1
        (hjk.trans (List.getElem?_eq_some_iff.1 Hkey).2.symm)
      omega
    rw [hmk]
    simp only [Option.getD_some]
    wp_if_destruct
    · -- the names agree: `key` is `k`
      have hkk : key = k := huniq key k mk mm hmk hk (Hif.trans hname.symm)
      subst hkk
      have hvv : vv = vk := by rw [hvk] at Hvv; exact (Option.some.inj Hvv).symm
      subst hvv
      have hmb : mb = null := by rw [Hmb]; simp [hkey_notin]
      subst hmb
      (try wp_auto)
      first | (wp_if_destruct <;> try (exfalso; simp_all; done)) | skip
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists vv, vv
      simp only [named]
      iframe memb Hmems m
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [htake]; simp
    · -- another name: `key` is not `k`
      have hkk : key ≠ k := by
        intro he; subst he; rw [hk] at hmk; cases hmk; exact Hif hname
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists mb, vv
      simp only [named]
      iframe memb Hmems m
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hmb, htake]
      simp [Ne.symm hkk]
  iintro HP Hmap
  iNamed HP
  obtain ⟨-, Hmb⟩ := Hi
  have hkin : k ∈ keys.take (GMap.size ms : Int).toNat := by
    rw [show (GMap.size ms : Int).toNat = keys.length by omega, List.take_of_length_le (Nat.le_refl _)]
    rw [Hkset k, hvk]; rfl
  rw [if_pos hkin] at Hmb
  subst Hmb
  (try wp_auto)
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
    (Φ := fun (k : w64) (m : Loc) => membership.memberAt (GF := GF) m q
      ((mem !! k).getD default)) hvk).1 $$ Hmems
    with ⟨Hown, Hmclose⟩
  rw [hk]
  simp only [Option.getD_some]
  wp_apply hClone vk q mm $$ [Hown] as %mc ⟨Hown, Hmc, -⟩
  ihave Hmems := Hmclose $$ [Hown]
  · iexact Hown
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock_owned $$ [$Hmu] as Hmu
  (try wp_auto)
  iapply HΦ
  iframe Hmu Hmc
  iunfold membership.memAt
  iexists mp
  iframe
  ipureintro; exact Hdom

end proof

end EtcdGrove
end Perennial
