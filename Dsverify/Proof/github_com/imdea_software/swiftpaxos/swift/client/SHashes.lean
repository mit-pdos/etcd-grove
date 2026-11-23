/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/SHashes.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`SHashesEq` (swift/dpath.go:194) and `Dep.Equals` on nil dependencies (swift/defs.go:195):
what the client's `accept` closure compares.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.CmdKey
public import Perennial.Proof.bytes
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.SHashesDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [bytes.Assumptions]

theorem SHashesEq.wp_proof (wp_Equal : bytes.Equal.spec (GF := netDistGF)) :
    SHashesEq.specI (hG := hG) := by
  intro s1 s2 l1 l2
  wp_start as ⟨#Hs1, #Hs2, %Hlen⟩
  ihave %Hl1 := ownSlice_len $$ Hs1
  ihave %Hl2 := ownSlice_len $$ Hs2
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ; ipureintro; intro h; cases h
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s1.len ∧
        ∀ j h, j < sint.nat i → l1[j]? = some h → h ∈ l2⌝ : IProp netDistGF) $$ [i]
  · iexists _; iframe; ipureintro; refine ⟨by word, by word, ?_⟩; intro j h hj; word
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < l1.length := by simp only [List.length_map] at Hl1; word
    obtain ⟨x, hx⟩ : ∃ x, l1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    rw [if_pos (by word)]
    wp_apply (wp_load_slice_index (V := swift.SHash) s1 (sint.Z i) (l1.map shashOf) _ (shashOf x)
      Hi.1) $$ [Hs1] as -
    · iframe #; ipureintro; simp only [List.getElem?_map]; rw [show (sint.Z i).toNat = sint.nat i by word, hx]; rfl
    have Hleq : s1.len = s2.len := by assumption
    icases typedPointsto_split _ _ _ $$ h with h
    simp only [TypedPointsto.typedPointstoDef]
    icases h with ⟨H, -⟩
    ipersist H
    ihave #Hh := slice_array_dq _ 32 _ DFrac.discard (by simp [shashOf]; rw [Hlen.1 x (List.mem_of_getElem? hx)]; decide) $$ H
    ihave HJ : (∃ k : w64, "i" ∷ i_ptr ↦ k ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s2.len⌝ : IProp netDistGF) $$ [i]
    · iexists _; iframe; ipureintro; word
    wp_for HJ
    wp_if_destruct
    · have hkl : sint.nat k < l2.length := by simp only [List.length_map] at Hl2; word
      obtain ⟨y, hy⟩ : ∃ y, l2[sint.nat k]? = some y := ⟨_, List.getElem?_eq_getElem hkl⟩
      rw [if_pos (by word)]
      wp_apply (wp_load_slice_index (V := swift.SHash) s2 (sint.Z k) (l2.map shashOf) _ (shashOf y)
        Hk.1) $$ [Hs2] as -
      · iframe #; ipureintro; simp only [List.getElem?_map]
        rw [show (sint.Z k).toNat = sint.nat k by word, hy]; rfl
      icases typedPointsto_split _ _ _ $$ g with g
      simp only [TypedPointsto.typedPointstoDef]
      icases g with ⟨G, -⟩
      ipersist G
      ihave #Hg := slice_array_dq _ 32 _ DFrac.discard (by simp [shashOf]; rw [Hlen.2 y (List.mem_of_getElem? hy)]; decide) $$ G
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, go.arrayIndexRef_0,
        show W64 32 - W64 0 = W64 32 from rfl]
      wp_apply wp_Equal $$ [Hh Hg] as -
      · iframe #
      wp_if_destruct
      · -- found: `x = y`
        simp only [shashOf] at Hif
        subst Hif
        wp_for_post
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro j h hj hjh
        rcases Nat.lt_or_ge j (sint.nat i) with hlt | hge
        · exact Hi.2.2 j h hlt hjh
        · have : j = sint.nat i := by
            have : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            omega
          subst this
          rw [hx] at hjh; cases hjh
          exact List.mem_of_getElem? hy
      · wp_for_post
        iframe
        iexists _
        iframe
        ipureintro; word
    · wp_for_post
      iapply HΦ; ipureintro; intro h; cases h
  · iapply HΦ
    ipureintro
    intro _
    simp only [List.length_map] at Hl1 Hl2
    refine ⟨by word, ?_⟩
    intro h hh
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hh
    have : j < l1.length := by
      rcases Nat.lt_or_ge j l1.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none_iff.mpr h'] at hj; cases hj
    exact Hi.2.2 j h (by word) hj

theorem Dep.Equals.wp_proof : Dep.Equals.specI (hG := hG) := by
  haveI := cmdId_intoValInj (sem := sem)
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m1 Hm1
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m2 Hm2
  wp_for
  wp_apply (wp_map_len (K := swift.CommandId) (V := Unit)) $$ [$Hm1] as Hm1
  wp_apply (wp_map_len (K := swift.CommandId) (V := Unit)) $$ [$Hm2] as Hm2
  wp_apply (wp_map_len (K := swift.CommandId) (V := Unit)) $$ [$Hm1] as Hm1
  iapply HΦ; itrivial

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
