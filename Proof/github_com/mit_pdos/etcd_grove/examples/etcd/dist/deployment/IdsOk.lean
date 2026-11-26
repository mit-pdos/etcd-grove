/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/IdsOk.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.IdsOk
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.memberIDs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.grantsLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.RaftIdOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem IdsOk.wp_proof
    (hIDs : etcd_dist.memberIDs.spec (GF := GF) (hG := hG))
    (hGrants : etcd_dist.grantsLeases.spec (GF := GF) (hG := hG))
    (hRaft : etcd_dist.RaftIdOk.spec (GF := GF) (hG := hG)) :
    etcd_dist.IdsOk.spec (GF := GF) (hG := hG) := by
  intro v d hfips hpeers
  wp_start as #Hd
  wp_auto
  wp_apply (hIDs v d hfips hpeers) $$ [] as %isl %ids ⟨Hids, %Hids⟩
  · iframe #
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hlw := ownSlice_len _ _ _ $$ Hw
  rw [List.length_map] at Hlw
  ihave HI : (∃ (j : Nat) (wv : deployment.Workload) (g : Bool),
      "i" ∷ i_ptr ↦ W64 j ∗ "w" ∷ w_ptr ↦ wv ∗ "grants" ∷ grants_ptr ↦ g ∗
      "%Hj" ∷ ⌜j ≤ d.workloads.length ∧
        (g = true ↔ ∃ w ∈ d.workloads.take j, kindGrantsLeases w.kind = true)⌝ : IProp GF)
    $$ [i w grants]
  · iexists 0, _, false
    iframe
    ipureintro
    exact ⟨by omega, by simp⟩
  wp_for HI
  obtain ⟨Hj1, Hj2⟩ := Hj
  wp_if_destruct
  · have hj : j < d.workloads.length := by word
    have hc : sint.Z (W64 (j : Int)) < sint.Z v.Workloads'.len := by word
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, d.workloads[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index v.Workloads' (sint.Z (W64 (j : Int))) (d.workloads.map Workload.val) DFrac.discard x.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj, List.getElem?_map, hx]; rfl
    have htake : d.workloads.take (j + 1) = d.workloads.take j ++ [x] := by
      rw [List.take_add_one, hx]; rfl
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    cases g
    · wp_auto
      wp_apply hGrants
      wp_for_post
      iframe
      iexists (j + 1), _, _
      rw [hw]
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [htake]
      constructor
      · intro h; exact ⟨x, List.mem_append_right _ (List.mem_singleton_self _), h⟩
      · rintro ⟨w, hw', hg⟩
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact absurd (Hj2.2 ⟨w, hw', hg⟩) (by simp)
        · rw [List.mem_singleton] at hw'; subst hw'; exact hg
    · wp_auto
      wp_for_post
      iframe
      iexists (j + 1), _, true
      rw [hw]
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [htake]
      constructor
      · intro _
        obtain ⟨w, hw', hg⟩ := Hj2.1 rfl
        exact ⟨w, List.mem_append_left _ hw', hg⟩
      · intro _; rfl
  · have hjl : j = d.workloads.length := by word
    subst hjl
    rw [List.take_length] at Hj2
    wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %m16 Hm16
    wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %m15 Hm15
    ihave %Hli := ownSlice_len _ _ _ $$ Hids
    ihave HK : (∃ (j : Nat) (idv : w64) (mp16 mp15 : GMap w64 Bool),
        "i" ∷ i_ptr ↦ W64 j ∗ "id" ∷ id_ptr ↦ idv ∗ "Hm16" ∷ m16 ↦$ mp16 ∗ "Hm15" ∷ m15 ↦$ mp15 ∗
        "%Hk" ∷ ⌜j ≤ ids.length ∧
          (∀ k, mp16 !! k = if k ∈ (ids.take j).map (· &&& W64 65535) then some true else none) ∧
          (∀ k, mp15 !! k = if k ∈ (ids.take j).map (· &&& W64 32767) then some true else none) ∧
          ((ids.take j).map (· &&& W64 65535)).Nodup ∧
          (∀ id ∈ ids.take j, id &&& W64 65535 ≠ W64 0) ∧
          (∀ id ∈ ids.take j, raftIdOk id = true) ∧
          (g = true → ((ids.take j).map (· &&& W64 32767)).Nodup)⌝ : IProp GF)
      $$ [i id Hm16 Hm15]
    · iexists 0, _, ∅, ∅
      iframe
      ipureintro
      exact ⟨by omega, fun k => by simp, fun k => by simp, by simp, by simp, by simp, fun _ => by simp⟩
    wp_for HK
    obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5, HkR, Hk6⟩ := Hk
    wp_if_destruct
    · have hj : j < ids.length := by word
      have hc : sint.Z (W64 (j : Int)) < sint.Z isl.len := by word
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      simp only [h0, hc, and_self, ↓reduceIte]
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      obtain ⟨x, hx⟩ : ∃ x, ids[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
      wp_apply (wp_load_slice_index isl (sint.Z (W64 (j : Int))) ids (DFrac.own 1) x h0) $$ [Hids] as Hids
      · iframe; ipureintro; rw [hsj]; exact hx
      have htake : ids.take (j + 1) = ids.take j ++ [x] := by rw [List.take_add_one, hx]; rfl
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      have hmapins : ∀ (mp : GMap w64 Bool) (f : w64 → w64),
          (∀ k, mp !! k = if k ∈ (ids.take j).map f then some true else none) →
          ∀ k, (<[f x := true]> mp) !! k = if k ∈ (ids.take (j + 1)).map f then some true else none := by
        intro mp f hmp k
        rw [htake, List.map_append]
        by_cases hk : k = f x
        · subst hk; simp
        · rw [lookup_insert_ne mp true (Ne.symm hk), hmp k]; simp [hk]
      have hnd : ∀ (f : w64 → w64), ((ids.take j).map f).Nodup → f x ∉ (ids.take j).map f →
          ((ids.take (j + 1)).map f).Nodup := by
        intro f h1 h2
        rw [htake, List.map_append, List.nodup_append]
        refine ⟨h1, by simp, ?_⟩
        intro a ha b hb hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb; subst hab; exact h2 ha
      by_cases hz : x &&& W64 65535 = W64 0
      · simp only [hz, _root_.decide_true]
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro; intro _ h; cases h
      · simp only [hz, _root_.decide_false]
        wp_auto
        wp_apply hRaft
        by_cases hr : raftIdOk x = false
        · simp only [hr, Bool.not_false, ↓reduceIte]
          wp_auto
          wp_for_post
          iapply HΦ
          ipureintro; intro _ h; cases h
        have hr' : raftIdOk x = true := by simpa using hr
        simp only [hr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hR : ∀ id ∈ ids.take (j + 1), raftIdOk id = true := by
          intro id hid
          rw [htake] at hid
          rcases List.mem_append.1 hid with h | h
          · exact HkR id h
          · rw [List.mem_singleton] at h; subst h; exact hr'
        wp_auto
        wp_apply (wp_map_lookup1 _ _ m16 mp16 (x &&& W64 65535)) $$ [Hm16] as Hm16
        · iframe
        rw [Hk2]
        by_cases hin16 : x &&& W64 65535 ∈ (ids.take j).map (· &&& W64 65535)
        · rw [if_pos hin16]
          simp only [Option.getD_some]
          wp_auto
          wp_for_post
          iapply HΦ
          ipureintro; intro _ h; cases h
        · rw [if_neg hin16]
          simp only [Option.getD_none]
          rw [show (zero_val Bool) = false from rfl]
          wp_auto
          cases g
          · have hin15 : false = true → x &&& W64 32767 ∉ (ids.take j).map (· &&& W64 32767) :=
              fun h => by cases h
            wp_auto
            wp_apply (wp_mapInsert _ m16 mp16 (x &&& W64 65535) true) $$ [Hm16] as Hm16
            · iframe
            wp_apply (wp_mapInsert _ m15 mp15 (x &&& W64 32767) true) $$ [Hm15] as Hm15
            · iframe
            wp_for_post
            iframe
            iexists (j + 1), _, _, _
            rw [hw]
            iframe
            ipureintro
            refine ⟨by omega, hmapins mp16 _ Hk2, hmapins mp15 _ Hk3, hnd _ Hk4 hin16, ?_, hR, ?_⟩
            · intro id hid
              rw [htake] at hid
              rcases List.mem_append.1 hid with h | h
              · exact Hk5 id h
              · rw [List.mem_singleton] at h; subst h; exact hz
            · first | (intro _; exact hnd _ (Hk6 rfl) (hin15 rfl)) | (intro hg; cases hg) | (intro hg; simp at hg)
          · wp_auto
            wp_apply (wp_map_lookup1 _ _ m15 mp15 (x &&& W64 32767)) $$ [Hm15] as Hm15
            · iframe
            rw [Hk3]
            by_cases hin : x &&& W64 32767 ∈ (ids.take j).map (· &&& W64 32767)
            · rw [if_pos hin]
              simp only [Option.getD_some]
              wp_auto
              wp_for_post
              iapply HΦ
              ipureintro; intro _ h; cases h
            · have hin15 : true = true → x &&& W64 32767 ∉ (ids.take j).map (· &&& W64 32767) :=
                fun _ => hin
              rw [if_neg hin]
              simp only [Option.getD_none]
              rw [show (zero_val Bool) = false from rfl]
              wp_auto
              wp_apply (wp_mapInsert _ m16 mp16 (x &&& W64 65535) true) $$ [Hm16] as Hm16
              · iframe
              wp_apply (wp_mapInsert _ m15 mp15 (x &&& W64 32767) true) $$ [Hm15] as Hm15
              · iframe
              wp_for_post
              iframe
              iexists (j + 1), _, _, _
              rw [hw]
              iframe
              ipureintro
              refine ⟨by omega, hmapins mp16 _ Hk2, hmapins mp15 _ Hk3, hnd _ Hk4 hin16, ?_, hR, ?_⟩
              · intro id hid
                rw [htake] at hid
                rcases List.mem_append.1 hid with h | h
                · exact Hk5 id h
                · rw [List.mem_singleton] at h; subst h; exact hz
              · first | (intro _; exact hnd _ (Hk6 rfl) (hin15 rfl)) | (intro hg; cases hg) | (intro hg; simp at hg)
    · have hjl : j = ids.length := by word
      subst hjl
      rw [List.take_length] at Hk4 Hk5 HkR Hk6
      iapply HΦ
      ipureintro
      intro hall _
      rw [← Hids hall]
      have h16 : ∀ x : w64, uint.Z (x &&& W64 65535) = uint.Z x % 2 ^ 16 := by
        intro x
        have e : (W64 65535 : w64).toNat = 2 ^ 16 - 1 := by decide
        unfold uint.Z
        rw [BitVec.toNat_and, e, Nat.and_two_pow_sub_one_eq_mod]
        omega
      have h15 : ∀ x : w64, uint.Z (x &&& W64 32767) = uint.Z x % 2 ^ 15 := by
        intro x
        have e : (W64 32767 : w64).toNat = 2 ^ 15 - 1 := by decide
        unfold uint.Z
        rw [BitVec.toNat_and, e, Nat.and_two_pow_sub_one_eq_mod]
        omega
      have hnd : ∀ (f : w64 → w64) (g : w64 → Int), (∀ x, uint.Z (f x) = g x) → (ids.map f).Nodup →
          (ids.map g).Nodup := by
        intro f g hfg h
        unfold List.Nodup at h ⊢
        rw [List.pairwise_map] at h ⊢
        exact h.imp (fun {a b} hne heq => hne (by rw [← hfg a, ← hfg b] at heq; word))
      refine ⟨hnd _ _ h16 Hk4, fun id hid => ?_, fun id hid => ?_, fun hg => ?_⟩
      · rw [← h16]; have := Hk5 id hid; intro h; apply this; word
      · have := HkR id hid; simpa [raftIdOk] using this
      · exact hnd _ _ h15 (Hk6 (Hj2.2 hg))


end proof

end etcd_dist
end EtcdGrove
end Perennial

