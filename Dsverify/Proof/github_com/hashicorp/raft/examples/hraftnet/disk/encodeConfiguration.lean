/-
(hraft_robust R3) The proof of `disk.encodeConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration.wp_proof
    (wp_putUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration.spec (GF := GF) (hG := hG) := by
  intro b bs c ss
  wp_start as ⟨Hb, Hcap, #Hc⟩
  iunfold cfgRep at Hc
  icases Hc with ⟨%svs, #Hs, %Hss⟩
  subst Hss
  ihave %Hsl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b0 ⟨Hb, Hcap⟩
  rw [dk_w64_of_length svs c.Servers'.len Hsl]
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
      "Hb" ∷ bb ↦* (bs ++ encU64 (W64 svs.length) ++ ((svs.map srvOf).take (sint.nat i)).flatMap encServer) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z c.Servers'.len⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 0, b0
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < svs.length := dk_idx_lt i c.Servers'.len _ Hsl Hi.1 Hif
    list_elem svs (sint.nat i) as sv
    have hml : (svs.map srvOf)[sint.nat i]? = some (srvOf sv) := by
      rw [List.getElem?_map, Hsv_lookup]; rfl
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z c.Servers'.len := ⟨Hi.1, Hif⟩
    icases ownSlice_elem_acc (sint.Z i) sv c.Servers' DFrac.discard svs Hi.1
      (by rw [dk_toNat_sint]; exact Hsv_lookup) $$ Hs with ⟨Hv, Hclose⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    iStructNamed Hv
    wp_apply (IntoValTyped.wp_load (t := ServerSuffrage.ty) _ _ _) $$ [$Suffrage] as -
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (IntoValTyped.wp_load (t := ServerID.ty) _ _ _) $$ [$ID] as -
    wp_apply (wp_string_to_bytes sv.ID') as %sid ⟨Hsid, -⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hsid] as %b2 ⟨Hb, Hcap, -⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (IntoValTyped.wp_load (t := ServerAddress.ty) _ _ _) $$ [$Address] as -
    wp_apply (wp_string_to_bytes sv.Address') as %sad ⟨Hsad, -⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hsad] as %b3 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b3
    obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i c.Servers'.len Hi.1 Hif
    rw [hs1, dk_flatMap_take_succ (svs.map srvOf) encServer _ _ hml]
    unfold encServer srvOf
    simp only [List.append_assoc]
    iframe
    ipureintro; exact ⟨hs2, hs3⟩
  · rw [dk_flatMap_take_length (svs.map srvOf) encServer _
      (by rw [List.length_map]; exact dk_idx_eq i c.Servers'.len _ Hsl Hi.2 Hif)]
    iapply HΦ
    unfold encCfg
    rw [List.length_map]
    simp only [List.append_assoc]
    iframe
