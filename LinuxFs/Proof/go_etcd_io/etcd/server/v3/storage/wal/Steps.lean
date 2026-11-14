/- Lean-first (no Rocq counterpart).

# The WALs' step bound at a look (`notes/bounds-plan.md`, "The WAL's segment sequence")

The invariant's ghost state holds the WALs' step bound (`walGhost`'s `walStepsLb`: `⧖ n`, every WAL's
history at most `n` long). An open handle reads its WAL's at a look, through its tail record
(`walInvBody_tailSteps`, `walTail_steps`: `⧖ |H|`): `Save` and `SaveSnapshot` raise it by one counted
step before their commit deposits it (`walHandleIn_steps`, `walHandleIn_append`); `ReadAll` bounds
its tail's sequence number by it (`WalAbsD.tailSeq`: the sequence is `|cuts| ≤ |H|`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

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

/-- **The tail record of `dir`** names the WAL, its layout and the layout's last segment (as
`CutSync.lean`'s `walTailsRes_lookup`, which this file does not import). -/
theorem walTailsRes_lookupA (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      ⌜∃ (d : WalDur) (lay : WalLay) (g0 : SegG), s.wal !! dir = some d ∧ Ls !! dir = some lay ∧
          lay.segs.getLast? = some g0 ∧ tg = tailG d lay g0.ino (F !! g0.ino)⌝ ∗
        walTailsRes (W := W) C Mr s Ls F ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg := by
  letI := walAllG (W := W)
  unfold walTailsRes tailVar
  iintro ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩ Hk Hv
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  isplitr
  · ipureintro; exact ⟨d, lay, g0, hp.1, hp.2.1, hp.2.2.1, Htg⟩
  iframe Hk Hv
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
  iexists d, lay, g0
  iframe Hv'
  ipureintro; exact hp

/-- **The step bound of the open handle's WAL, at a look** (`notes/bounds-plan.md`, "The WAL's segment
sequence"): its history, the tail record's, is within the invariant's step bound (`walGhost_steps`). -/
theorem walInvBody_tailSteps (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ ⧖ tg.1.length := by
  iintro Hb Hk Hv
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Har, Hcl, Hn, Hlays, HW, HWC, HCR, Htl, Hab, HNm, Hpk,
    Hdk, HAt, Hnms, Hbd⟩
  icases walGhost_steps (W := W) s $$ Hg with ⟨Hg, #Hst⟩
  icases walTailsRes_lookupA C Mr s Ls F dir γ tg $$ Htl Hk Hv with ⟨%hp, Htl, Hk, Hv⟩
  obtain ⟨d, lay, g0, hd, -, -, htg⟩ := hp
  ihave #Hd := walStepsLb_at s dir d hd $$ Hst
  iframe Hk Hv
  isplitl
  · iexists Ls, cl, n, F
    iframe
  · have e : tg.1 = d.H := by rw [htg]; rfl
    rw [e]; iexact Hd

/-- **The step bound of the open handle's WAL** (`walInvBody_tailSteps`), at an update of mask `⊤`. -/
theorem walTail_steps (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      |={⊤}=> notCrashed (hC := L.goose_crashGS) ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ ⧖ tg.1.length := by
  iintro #Hinv Hnc Hk Hv
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_tailSteps C Mr R jr r s dir γ tg $$ Hb Hk Hv with ⟨Hb, Hk, Hv, #Hd⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hk Hv Hd

end iris

end WalFs
end EtcdGrove
end Perennial

end
