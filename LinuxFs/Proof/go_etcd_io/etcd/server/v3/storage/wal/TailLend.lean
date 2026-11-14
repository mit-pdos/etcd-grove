/- Lean-first (no Rocq counterpart).

# Lending a tail to the invariant (I3b, option (d) of the `wal-tc13` entry; `wal-tc14`)

`ZeroToEnd`'s supplies (`ReadAll`'s, the tail's truncate to its write position and its growth back to
the size) quantify over every state the invariant allows, so at their commits they cannot tell the
length of the tail's `old` from the state (the growth needs `tg ≤ |old|` and `tg ≤ hi`). While
`ZeroToEnd` runs, the handle lends its tail to the invariant: its key goes into `walLentRes`, which
records `|old|`, and the holder gets the token `walLentTok dir γ k` in its place. No step that needs
the key (an append, a cut, the window's fdatasync, `Close`) runs while the tail is lent, and every other
step keeps `old` (`walLentRes_insert_same`), so the supplies, which step the tail by the token
(`walTailKeyL`, `walInvBody_tailW`), read `|old| = k` at each commit.

* `walInvBody_lend` / `walInv_lend`: an exact tail (the handle's `TailMeta`: `lo = hi = size`) is lent
  with `k` its size: the tail's `OsMeta` is the invariant's (`segRes`, no change in flight: the record
  idle), an exact tail's bytes are as long as `old` (`TailLast`), so `|old| = size`
  (`walAbsD_old_exact`).
* `walInvBody_unlend` / `walInv_unlend`: the token back for the key.

Both at any program step (`wp_notCrashed_acc` gives `notCrashed`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **An exact last segment's `old` is as long as its size** (`TailLast`'s `|bs| = |old|`). -/
theorem walAbsD_old_exact {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (h : WalAbsD C Mr d lay ents) (hg : lay.segs.getLast? = some g)
    (hlo : g.om.lo = g.om.size) (hhi : g.om.hi = g.om.size) : lay.old.length = g.om.size := by
  have hm := h.metas g (List.mem_of_getLast? hg)
  have hex : SegExact g := ⟨by rw [hlo, hm.1], by rw [hhi, hm.1]⟩
  obtain ⟨-, -, h3, -⟩ := (h.last g hg).1 hex
  rw [hm.1]; exact h3.symm

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **An exact, idle tail lent** (see the file header). -/
theorem walInvBody_lend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (m : OsMeta) (hlo : m.lo = m.size) (hhi : m.hi = m.size) :
    ⊢ walInvBody (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) -∗
      osMeta i (DFrac.own (1 : Qp).half) m ==∗
      walInvBody (W := W) C Mr R jr r s ∗ walLentTok (W := W) dir γ m.size ∗
        tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗ osMeta i (DFrac.own (1 : Qp).half) m := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Hb Hk Hv Hm
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HDK, %HAt, Hnms, %Hbd⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm with ⟨Hent, HTm⟩
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  have Htg' := Htg
  simp only [tailG, Prod.mk.injEq] at Htg'
  obtain ⟨-, -, -, -, hino, hF⟩ := Htg'
  obtain ⟨hd, hl, hg, hZ, hB⟩ := hp
  subst hino
  have hg0m : g0 ∈ segsAll Ls := mem_segsAll hl (List.mem_of_getLast? hg)
  iunfold laysResF at Hlays
  icases (BigSepL.bigSepL_mem_acc (PROP := IProp GF) (Φ := fun g => segResF (L := hG.goose_localGS) F g) hg0m) $$ Hlays
    with ⟨Hs0, Hlays⟩
  have eseg : segResF F g0 = segRes g0 := by unfold segResF; rw [← hF]
  rw [eseg]
  unfold segRes
  icases Hs0 with ⟨Hm0, Hb0⟩
  icases osMeta_agree2 _ _ _ _ _ $$ Hm Hm0 with %hm
  subst hm
  obtain ⟨lay1, nm, -, hl1, -, -, -, -, habs, -⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hold : lay.old.length = g0.om.size := walAbsD_old_exact habs hg hlo hhi
  imod walLentRes_lend T Ls dir γ lay HT hl $$ Hk HL with ⟨Hlt, HL⟩
  rw [hold]
  imodintro
  iframe Hlt Hv Hm
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HCR Hpk HDK Hnms
  isplitr
  · ipureintro; exact Har
  isplitl [Hlays Hm0 Hb0]
  · iunfold laysResF
    iapply Hlays
    rw [eseg]; unfold segRes; iframe Hm0 Hb0
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm Hv' HL]
  · iexists T
    iframe HTa HL
    isplitr
    · ipureintro; exact HTo
    isplitr
    · ipureintro; exact HTi
    iapply HTm
    iexists d, lay, g0
    iframe Hv'
    ipureintro; exact ⟨hd, hl, hg, hZ, hB⟩
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  isplitr
  · ipureintro; exact HAt
  ipureintro; exact Hbd

/-- **A lent tail returned** (see the file header). -/
theorem walInvBody_unlend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γ : GName) (k : Nat) :
    ⊢ walInvBody (W := W) C Mr R jr r s -∗ walLentTok (W := W) dir γ k ==∗
      walInvBody (W := W) C Mr R jr r s ∗ walTailKey (W := W) dir γ := by
  iintro Hb Hlt
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HDK, %HAt, Hnms, %Hbd⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  imod walLentRes_unlend T Ls dir γ k $$ Hlt HL with ⟨Hk, HL⟩
  imodintro
  iframe Hk
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HCR Hpk HDK Hnms Hlays
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm HL]
  · iexists T
    iframe HTa HL HTm
    ipureintro; exact ⟨HTo, HTi⟩
  ipureintro; exact ⟨Hab, HNm, HAt, Hbd⟩

/-- **An exact, idle tail lent, at a program step** (`walInvBody_lend` under `walInv`). -/
theorem walInv_lend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (m : OsMeta) (hlo : m.lo = m.size) (hhi : m.hi = m.size) :
    ⊢ walInv (W := W) C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) -∗
      osMeta i (DFrac.own (1 : Qp).half) m ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walLentTok (W := W) dir γ m.size ∗
        tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗ osMeta i (DFrac.own (1 : Qp).half) m := by
  iintro #Hinv Hnc Hk Hv Hm
  imod walInv_open C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_lend C Mr R jr r s dir γ H md cuts wr i m hlo hhi $$ Hb Hk Hv Hm with
    ⟨Hb, Hlt, Hv, Hm⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hlt Hv Hm

/-- **A lent tail returned, at a program step** (`walInvBody_unlend` under `walInv`). -/
theorem walInv_unlend (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) :
    ⊢ walInv (W := W) C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walLentTok (W := W) dir γ k ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walTailKey (W := W) dir γ := by
  iintro #Hinv Hnc Hlt
  imod walInv_open C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_unlend C Mr R jr r s dir γ k $$ Hb Hlt with ⟨Hb, Hk⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hk

end iris

end WalFs
end EtcdGrove
end Perennial

end
