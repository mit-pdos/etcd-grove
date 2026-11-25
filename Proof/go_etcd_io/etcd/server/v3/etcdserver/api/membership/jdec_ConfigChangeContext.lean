/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/jdec_ConfigChangeContext.lean`
(jsongen's generated code, membership's `json_model_gen.go`): the object's members in order, each by
`jdecMember_ConfigChangeContext`, over `models.lab/jsoncodec`'s `At`, `Empty`, `Member` and `Next`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdec_ConfigChangeContext
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdecMember_ConfigChangeContext
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.Empty
public import Net.Spec.models_lab.jsoncodec.Member
public import Net.Spec.models_lab.jsoncodec.Next
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

set_option goose.wp.extras true

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem membership.jdec_ConfigChangeContext.wp_proof
    (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
    (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
    (wp_Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG))
    (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
    (wp_jdecMember : membership.jdecMember_ConfigChangeContext.spec (GF := GF) (hG := hG)) :
    membership.jdec_ConfigChangeContext.spec (GF := GF) (hG := hG) := by
  intro b dq bs i p e ms r r' seen rest hnd hfresh hfold hb
  wp_start as ⟨Hb, Hown⟩
  ihave %Hlen := ownSlice_len $$ Hb
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + (membership.jobj ms).length ≤ bs.length := by
    have := congrArg List.length hb
    rw [List.length_drop, List.length_append] at this
    have : 1 ≤ (membership.jobj ms).length := by simp [membership.jobj]
    omega
  have h0 : bs[uint.nat i]? = some (W8 123) := by
    have := congrArg (fun l => l[0]?) hb
    simp only [List.getElem?_drop] at this; simpa [membership.jobj] using this
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ _ h0 (by decide)
  have hb1 : bs.drop (uint.nat i + 1) = membership.jmembers ms ++ 125#8 :: rest := by
    have := congrArg (List.drop 1) hb
    simpa [List.drop_drop, Nat.add_comm, membership.jobj] using this
  wp_auto
  wp_apply (wp_At b dq bs i (W8 123) (by omega) (by rw [hsk]; exact h0)) $$ Hb as Hb
  rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
  try wp_auto
  cases ms with
  | nil =>
    have h1 : bs[uint.nat i + 1]? = some (W8 125) := by
      have := congrArg (fun l => l[0]?) hb1
      simp only [List.getElem?_drop] at this; simpa [membership.jmembers] using this
    have hsk1 : JsonScan.skipEnd bs (uint.nat i + 1) = uint.nat i + 1 :=
      skipEnd_ns' bs _ _ h1 (by decide)
    have hle' : uint.nat i + 2 ≤ bs.length := by simpa [membership.jobj, membership.jmembers] using hlen
    wp_apply (wp_Empty b dq bs i (W8 125) (by omega) (by rw [hsk1]; exact h1)) $$ Hb as Hb
    rw [hsk1]
    try wp_auto
    simp only [membership.ccFold, Option.some.injEq] at hfold
    subst hfold
    rw [show W64 ((uint.nat i + 1 + 1 : Nat) : Int) =
        W64 ((uint.nat i + (membership.jobj []).length : Nat) : Int) by
      simp [membership.jobj, membership.jmembers]; congr 1]
    iapply HΦ
    iframe
  | cons m0 ms' =>
    obtain ⟨k0, v0⟩ := m0
    have h1 : bs[uint.nat i + 1]? = some (W8 34) := by
      have := congrArg (fun l => l[0]?) hb1
      simp only [List.getElem?_drop] at this
      simpa [membership.jmembers_cons, membership.jquoted] using this
    have hsk1 : JsonScan.skipEnd bs (uint.nat i + 1) = uint.nat i + 1 :=
      skipEnd_ns' bs _ _ h1 (by decide)
    have hle' : uint.nat i + 2 ≤ bs.length := by
      have := congrArg List.length hb1
      rw [List.length_drop] at this; simp [membership.jmembers_cons, membership.jquoted] at this; omega
    wp_apply (wp_Empty b dq bs i (W8 34) (by omega) (by rw [hsk1]; exact h1)) $$ Hb as Hb
    try wp_auto
    ihave HI : (∃ (rem : List (List w8 × membership.JVal)) (rc : membership.CcM)
        (sn : List GoString) (kw : w64),
        "k" ∷ k_ptr ↦ kw ∗ "Hown" ∷ membership.ccOwn p rc sn ∗
        "%Hinv" ∷ ⌜rem ≠ [] ∧ (rem.map Prod.fst).Nodup ∧ (∀ k ∈ rem.map Prod.fst, k ∉ sn) ∧
          membership.ccFold rem rc = some r' ∧
          bs.drop (uint.nat kw) = membership.jmembers rem ++ 125#8 :: rest ∧
          uint.nat kw + (membership.jmembers rem).length + 1 =
            uint.nat i + (membership.jobj ((k0, v0) :: ms')).length⌝ : IProp GF) $$ [k Hown]
    · iexists (k0, v0) :: ms', r, seen, i + W64 1
      iframe
      ipureintro
      have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      refine ⟨by simp, hnd, hfresh, hfold, ?_, ?_⟩
      · rw [hi1]; exact hb1
      · rw [hi1]; simp [membership.jobj]; omega
    wp_for HI
    obtain ⟨Hrem, Hnd, Hfr, Hfd, Hdrop, Hk⟩ := Hinv
    obtain ⟨⟨key, val⟩, rem', rfl⟩ : ∃ m rem', rem = m :: rem' := by
      cases rem with
      | nil => exact absurd rfl Hrem
      | cons a l => exact ⟨a, l, rfl⟩
    simp only [membership.ccFold] at Hfd
    obtain ⟨r1, hset, hfd'⟩ : ∃ r1, membership.ccSet key val rc = some r1 ∧
        membership.ccFold rem' r1 = some r' := by
      cases h : membership.ccSet key val rc with
      | none => rw [h] at Hfd; cases Hfd
      | some r1 => rw [h] at Hfd; exact ⟨r1, rfl, Hfd⟩
    have hkp := membership.ccSet_key_plain hset
    have hsep : bs.drop (uint.nat kw) = 34#8 :: (key ++ 34#8 :: 58#8 :: (val.json ++
        (if rem' = [] then [] else 44#8 :: membership.jmembers rem') ++ 125#8 :: rest)) := by
      rw [Hdrop, membership.jmembers_cons]; simp [membership.jquoted]
    have hklen : uint.nat kw + key.length + 3 + val.json.length +
        (if rem' = [] then 0 else 1 + (membership.jmembers rem').length) + 1 ≤ bs.length := by
      have := congrArg List.length hsep
      rw [List.length_drop] at this
      simp only [List.length_cons, List.length_append] at this
      by_cases hr : rem' = [] <;>
        simp only [hr, ↓reduceIte, List.length_nil, List.length_cons] at this ⊢ <;> omega
    wp_apply (wp_Member b dq bs kw key _ hkp hsep) $$ Hb as Hb
    try wp_auto
    have hv : uint.nat (W64 ((uint.nat kw + key.length + 3 : Nat) : Int)) =
        uint.nat kw + key.length + 3 := by
      have : uint.nat kw + key.length + 3 < 2 ^ 63 := by omega
      word
    have hvd : bs.drop (uint.nat kw + key.length + 3) =
        val.json ++ (if rem' = [] then [] else 44#8 :: membership.jmembers rem') ++ 125#8 :: rest := by
      have := congrArg (List.drop (key.length + 3)) hsep
      rw [List.drop_drop] at this
      rw [show uint.nat kw + key.length + 3 = uint.nat kw + (key.length + 3) by omega, this]
      simp
    have hnot : key ∉ sn := Hfr key (by simp)
    have hk1 : uint.nat (W64 ((uint.nat kw + key.length + 3 + val.json.length : Nat) : Int)) =
        uint.nat kw + key.length + 3 + val.json.length := by
      have : uint.nat kw + key.length + 3 + val.json.length < 2 ^ 63 := by omega
      word
    have hsep2 : bs.drop (uint.nat kw + key.length + 3 + val.json.length) =
        (if rem' = [] then [] else 44#8 :: membership.jmembers rem') ++ 125#8 :: rest := by
      have := congrArg (List.drop val.json.length) hvd
      rw [List.drop_drop] at this
      rw [show uint.nat kw + key.length + 3 + val.json.length =
        uint.nat kw + key.length + 3 + val.json.length by omega, this]
      simp
    by_cases hr : rem' = []
    · subst hr
      wp_apply (wp_jdecMember b dq bs _ key p e rc r1 sn val (W8 125) rest hnot hset
        (by rw [hv, hvd]; simp) (by right; rfl)) $$ [$Hb $Hown] as ⟨Hb, Hown⟩
      rw [hv]
      try wp_auto
      have hc : bs[uint.nat kw + key.length + 3 + val.json.length]? = some (W8 125) := by
        have := congrArg (fun l => l[0]?) hsep2
        simp only [List.getElem?_drop] at this; simpa using this
      have hskc := skipEnd_ns' bs _ _ hc (by decide)
      wp_apply (wp_Next b dq bs _ (W8 125) (by rw [hk1]; omega) (by rw [hk1, hskc]; exact hc))
        $$ Hb as Hb
      rw [hk1, hskc]
      try wp_auto
      wp_for_post
      rw [show W64 ((uint.nat kw + key.length + 3 + val.json.length + 1 : Nat) : Int) =
          W64 ((uint.nat i + (membership.jobj ((k0, v0) :: ms')).length : Nat) : Int) by
        congr 2; simp [membership.jmembers, membership.jquoted] at Hk; omega]
      simp only [membership.ccFold, Option.some.injEq] at hfd'
      subst hfd'
      iapply HΦ
      iframe
    · wp_apply (wp_jdecMember b dq bs _ key p e rc r1 sn val (W8 44) (membership.jmembers rem' ++ 125#8 :: rest) hnot hset
        (by rw [hv, hvd]; simp [hr]) (by left; rfl)) $$ [$Hb $Hown] as ⟨Hb, Hown⟩
      rw [hv]
      try wp_auto
      have hc : bs[uint.nat kw + key.length + 3 + val.json.length]? = some (W8 44) := by
        have := congrArg (fun l => l[0]?) hsep2
        simp only [List.getElem?_drop, hr, ↓reduceIte] at this; simpa using this
      have hskc := skipEnd_ns' bs _ _ hc (by decide)
      wp_apply (wp_Next b dq bs _ (W8 44) (by rw [hk1]; omega) (by rw [hk1, hskc]; exact hc))
        $$ Hb as Hb
      rw [hk1, hskc]
      try wp_auto
      wp_for_post
      iframe
      iexists rem', r1, key :: sn, W64 ((uint.nat kw + key.length + 3 + val.json.length + 1 : Nat) : Int)
      iframe
      ipureintro
      have hk2 : uint.nat (W64 ((uint.nat kw + key.length + 3 + val.json.length + 1 : Nat) : Int)) =
          uint.nat kw + key.length + 3 + val.json.length + 1 := by
        have : uint.nat kw + key.length + 3 + val.json.length + 1 < 2 ^ 63 := by omega
        word
      simp only [List.map_cons, List.nodup_cons] at Hnd
      refine ⟨hr, Hnd.2, ?_, hfd', ?_, ?_⟩
      · intro k hk hks
        rcases List.mem_cons.mp hks with rfl | hks
        · exact Hnd.1 hk
        · exact Hfr k (List.mem_cons_of_mem _ hk) hks
      · rw [hk2]
        have := congrArg (List.drop 1) hsep2
        rw [List.drop_drop] at this
        rw [this]
        simp [hr]
      · rw [hk2, ← Hk, membership.jmembers_cons]
        simp [hr, membership.jquoted]; omega

end proof

end EtcdGrove
end Perennial
