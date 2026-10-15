/- Lean-first (no Rocq counterpart).

`unlift(entry)`: four stores (the return's neighbours, then the call's), each a step of
`insertG` (`unlift_layout`).
-/
module

public import Spec.github_com.anishathalye.porcupine.unlift

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem unlift.wp_proof : unlift.spec (GF := GF) (hG := hG) :=
    fun hd loc val es B p q y hnd hp hpq hq => by
  wp_start as Hpre
  iunfold nodesOwn at Hpre
  icases Hpre with ⟨HG, %Hnn⟩
  obtain ⟨pc, nc, rp, rn, hpcm, hncm, hrpm, hrnm, hcpc, hrrp, h1, h2, h3⟩ :=
    unlift_layout hnd hp hpq hq
  have hcs : (some ⟨false, y⟩ : Slot) ∈ slots es := mem_slots_some (rem_get_mem hp)
  have hrs : (some ⟨true, y⟩ : Slot) ∈ slots es := mem_slots_some (rem_get_mem hq)
  -- `match := entry.match`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  -- `match.prev.next = match`
  icases nodesG_read hnd hrs _ $$ HG with ⟨Hr, HG⟩
  rw [h1]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hr
  icases nodesG_acc hnd (cur_sub_slots hrpm) _ $$ HG with ⟨Hrp, HG⟩
  rw [show nbrLoc hd loc (some rp) = slotLoc hd loc rp from rfl]
  wp_auto
  rw [show loc ⟨true, y⟩ = slotLoc hd loc (some ⟨true, y⟩) from rfl, nodeVal_next_some]
  ihave HG := HG $$ %_ Hrp
  -- `if match.next != nil { match.next.prev = match }`
  icases nodesG_read hnd hrs _ $$ HG with ⟨Hr, HG⟩
  rw [upd_ne hrrp, h1]
  simp only [slotLoc]
  wp_auto
  wp_join iprop(nodesG hd loc val es (insertG (layout es (y :: B)) rp (some ⟨true, y⟩) rn))
    with [HG Hr «match»] as HG
  · -- `match.next == nil`
    cases rn with
    | none =>
      ihave HG := HG $$ Hr
      simp only [insertG]
      iexact HG
    | some rn' =>
      exfalso
      exact slotLoc_ne_null Hnn (cur_sub_slots (hrnm rn' rfl)) Hif
  · -- `match.next != nil`
    cases rn with
    | none => exact absurd rfl Hif
    | some rn' =>
      have hrn's := cur_sub_slots (hrnm rn' rfl)
      ihave HG := HG $$ Hr
      icases nodesG_acc hnd hrn's _ $$ HG with ⟨Hrn, HG⟩
      simp only [nbrLoc]
      wp_auto
      rw [show loc ⟨true, y⟩ = slotLoc hd loc (some ⟨true, y⟩) from rfl, nodeVal_prev_some]
      ihave HG := HG $$ %_ Hrn
      wp_join_done
  -- `entry.prev.next = entry`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  rw [h2]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  icases nodesG_acc hnd (cur_sub_slots hpcm) _ $$ HG with ⟨Hpc, HG⟩
  simp only [nbrLoc]
  wp_auto
  rw [show loc ⟨false, y⟩ = slotLoc hd loc (some ⟨false, y⟩) from rfl, nodeVal_next_some]
  ihave HG := HG $$ %_ Hpc
  -- `entry.next.prev = entry`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  rw [upd_ne hcpc, h2]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  icases nodesG_acc hnd (cur_sub_slots hncm) _ $$ HG with ⟨Hnc, HG⟩
  simp only [nbrLoc]
  wp_auto
  rw [show loc ⟨false, y⟩ = slotLoc hd loc (some ⟨false, y⟩) from rfl, nodeVal_prev_some]
  ihave HG := HG $$ %_ Hnc
  iapply HΦ
  iunfold nodesOwn
  have hGf : ∀ G : Slot → Option Slot × Option Slot,
      upd (upd G pc ((G pc).1, some (some ⟨false, y⟩))) nc
        (some (some ⟨false, y⟩), (upd G pc ((G pc).1, some (some ⟨false, y⟩)) nc).2) =
      insertG G pc (some ⟨false, y⟩) (some nc) := fun G => rfl
  rw [hGf, nodesG_congr (fun x _ => h3 x)]
  iframe
  ipureintro; exact Hnn

end proof

end porcupine
end EtcdGrove
end Perennial
