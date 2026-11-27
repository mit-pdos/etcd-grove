/- Lean-first (no Rocq counterpart).

# A length lower bound of the open WAL is at most the handle's history (W6, `Sync`)

`walLenLb w dir i n` (a past state's history of `dir`'s incarnation `i` has length at least `n`), the
handle's record at `i` (`walOpenWI w dir i`, current: `walGhostI_openWI`) and the handle's half of its
tail record (`tailVar γ (H, …)`, which agrees with the invariant's current WAL of `dir`) give `n ≤ |H|`:
the past state is below the current one at the same incarnation (`walLenLb_ghost`: histories only grow). `Sync`
turns `sync`'s `walSyncedLb dir |H|` into the spec's `walSyncedLb dir n` with it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The invariant's contents bound a length lower bound by the handle's history** (kept). -/
theorem walInvBody_lenLb (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (w : Loc) (dir : GoString) (γ : GName) (tg : TailG) (n : Nat)
    (i : Nat) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗ walOpenWI (W := W) w dir i -∗ walLenLb (W := W) w dir i n -∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ walOpenWI (W := W) w dir i ∗ ⌜n ≤ tg.1.length⌝ := by
  letI := walAllG (W := W)
  iintro Hb Hk Hv Hw #Hn
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n', %F, Hg, Hrest⟩
  iunfold walGhost at Hg
  icases Hg with ⟨%Ig, Hg⟩
  icases walGhostI_openWI s Ig w dir i $$ Hg Hw with ⟨%hi, Hg, Hw⟩
  subst hi
  icases walLenLb_ghost s Ig w dir n $$ Hg Hn with %Hdp
  ihave Hg := walGhostI_ghost s Ig $$ Hg
  icases Hrest with ⟨%Har, Hcl, Hn', Hlays, %HW, %HWC, HCR, Htl, Hrest⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g, %hp, Hv'⟩
  unfold tailVar
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  obtain ⟨d', hd', hlen⟩ := Hdp
  rw [hp.1] at hd'
  cases hd'
  have hn : n ≤ tg.1.length := by
    rw [Htg]; exact hlen
  iframe Hk Hv Hw
  isplitl
  · iexists Ls, cl, n', F
    iframe Hg Hcl Hn' Hlays HCR Hrest
    isplitr
    · ipureintro; exact Har
    isplitr
    · ipureintro; exact HW
    isplitr
    · ipureintro; exact HWC
    iexists T
    iframe HTa HL
    isplitr
    · ipureintro; exact HTo
    isplitr
    · ipureintro; exact HTi
    iapply (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
      iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
          TailBound C Mr d lay⌝ ∗
        ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).2
    iframe HTm
    iexists d, lay, g
    iframe Hv'
    ipureintro; exact hp
  · ipureintro; exact hn

/-- **The same, at an update** (the invariant opened and closed; `notCrashed` excludes its crash
branch): for `Sync`, around any step. -/
theorem walLenLb_tail_le (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (w : Loc) (dir : GoString) (γ : GName) (tg : TailG) (n i : Nat) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗ walOpenWI (W := W) w dir i -∗
      walLenLb (W := W) w dir i n -∗
      |={E}=> notCrashed (hC := L.goose_crashGS) ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ walOpenWI (W := W) w dir i ∗ ⌜n ≤ tg.1.length⌝ := by
  iintro #Hinv Hnc Hk Hv Hw #Hn
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_lenLb C Mr R jr r s w dir γ tg n i $$ Hb Hk Hv Hw Hn with ⟨Hb, Hk, Hv, Hw, %hn⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hk Hv Hw
  ipureintro; exact hn

end iris

end WalFs
end EtcdGrove
end Perennial
