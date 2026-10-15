/- Lean-first (no Rocq counterpart).

`lift(entry)`: four stores (the call's neighbours, then the return's), each a step of
`eraseG` (`lift_layout`).
-/
module

public import Spec.github_com.anishathalye.porcupine.lift

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

theorem lift.wp_proof : lift.spec (GF := GF) (hG := hG) := fun hd loc val es B p q y hnd hp hpq hq => by
  wp_start as Hpre
  iunfold nodesOwn at Hpre
  icases Hpre with ⟨HG, %Hnn⟩
  obtain ⟨pc, nc, rp, rn, hpcm, hncm, hrpm, hrnm, hcpc, hrrp, h1, h2, h3⟩ :=
    lift_layout hnd hp hpq hq
  have hcs : (some ⟨false, y⟩ : Slot) ∈ slots es := mem_slots_some (rem_get_mem hp)
  have hrs : (some ⟨true, y⟩ : Slot) ∈ slots es := mem_slots_some (rem_get_mem hq)
  -- `entry.prev.next = entry.next`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  rw [h1]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  icases nodesG_acc hnd (cur_sub_slots hpcm) _ $$ HG with ⟨Hpc, HG⟩
  simp only [nbrLoc]
  wp_auto
  rw [nodeVal_next_some]
  ihave HG := HG $$ %_ Hpc
  -- `entry.next.prev = entry.prev`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  rw [upd_ne hcpc, h1]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  icases nodesG_acc hnd (cur_sub_slots hncm) _ $$ HG with ⟨Hnc, HG⟩
  simp only [nbrLoc]
  wp_auto
  rw [nodeVal_prev_some]
  ihave HG := HG $$ %_ Hnc
  have hG2 : upd (upd (layout es B) pc ((layout es B pc).1, some nc)) nc
      (some pc, (upd (layout es B) pc ((layout es B pc).1, some nc) nc).2) =
      eraseG (layout es B) pc (some nc) := rfl
  rw [hG2]
  -- `match := entry.match`
  icases nodesG_read hnd hcs _ $$ HG with ⟨Hc, HG⟩
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hc
  -- `match.prev.next = match.next`
  icases nodesG_read hnd hrs _ $$ HG with ⟨Hr, HG⟩
  rw [h2]
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hr
  icases nodesG_acc hnd (cur_sub_slots hrpm) _ $$ HG with ⟨Hrp, HG⟩
  rw [show nbrLoc hd loc (some rp) = slotLoc hd loc rp from rfl]
  wp_auto
  rw [nodeVal_next]
  ihave HG := HG $$ %_ Hrp
  -- `if match.next != nil { match.next.prev = match.prev }`
  icases nodesG_read hnd hrs _ $$ HG with ⟨Hr, HG⟩
  rw [upd_ne hrrp, h2]
  simp only [slotLoc]
  wp_auto
  cases rn with
  | none =>
    simp only [nbrLoc]
    wp_auto
    ihave HG := HG $$ Hr
    iapply HΦ
    iunfold nodesOwn
    have hG4 : upd (eraseG (layout es B) pc (some nc)) rp
        ((eraseG (layout es B) pc (some nc) rp).fst, none) =
        eraseG (eraseG (layout es B) pc (some nc)) rp none := rfl
    rw [hG4, nodesG_congr (fun x _ => h3 x)]
    iframe
    ipureintro; exact Hnn
  | some rn' =>
    have hrn's := cur_sub_slots (hrnm rn' rfl)
    have hne := slotLoc_ne_null Hnn hrn's
    simp only [nbrLoc, hne, _root_.decide_false, Bool.not_false]
    wp_auto
    ihave HG := HG $$ Hr
    icases nodesG_acc hnd hrn's _ $$ HG with ⟨Hrn, HG⟩
    simp only [nbrLoc]
    wp_auto
    rw [nodeVal_prev_some]
    ihave HG := HG $$ %_ Hrn
    iapply HΦ
    iunfold nodesOwn
    have hG4 : upd (upd (eraseG (layout es B) pc (some nc)) rp
        ((eraseG (layout es B) pc (some nc) rp).fst, some rn')) rn'
        (some rp, (upd (eraseG (layout es B) pc (some nc)) rp
          ((eraseG (layout es B) pc (some nc) rp).fst, some rn') rn').2) =
        eraseG (eraseG (layout es B) pc (some nc)) rp (some rn') := rfl
    rw [hG4, nodesG_congr (fun x _ => h3 x)]
    iframe
    ipureintro; exact Hnn

end proof

end porcupine
end EtcdGrove
end Perennial
