/- Lean-first (no Rocq counterpart).

# `Create`'s ghost steps as updates of the WAL invariant (W4, `notes/wal-fsext-plan.md`, "W4
implementation log", tenth session)

The steps of `CreateDropStep.lean`, `CreateMergeStep.lean` and `CreateMint.lean` act on the
invariant's contents; `Create`'s body takes them at a program step, where the generation's
`notCrashed` is at hand (`wp_notCrashed_acc`, `GooseLang/Ext/Fs/NotCrashedAcc.lean`): `walInv_step`
opens the invariant with it (`walInv_open`), runs a step on the contents and closes it again. The
wrappers below are the five steps in that form, at any mask holding the WAL's and the file system's
shared invariants (`⊤` at a program step: `walN_osShN_top`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateMint

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- At a program step (mask `⊤`), the shared invariant is outside the WAL invariant's namespace. -/
theorem walN_osShN_top : (↑osShN : CoPset) ⊆ (⊤ : CoPset) \ ↑walN := by
  have h2 : (↑walN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h2 p ⟨hn, hp⟩⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A step of the invariant's contents, as an update of the invariant** (the generation's
`notCrashed` excluding its crash branch, handed back). -/
theorem walInv_step (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (P Q : IProp GF) (E : CoPset) (hE : ↑walN ⊆ E)
    (hstep : ∀ s, ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ P ={E \ ↑walN}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ Q) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗ P ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ Q := by
  iintro #Hinv Hnc HP
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  icases Hb with ⟨%s, Hb⟩
  ihave Hs := hstep s $$ Hb HP
  imod Hs with ⟨Hb, HQ⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe

/-- The drop of `b` off the area claim (`walInvBody_drop`), as an update of the invariant. -/
theorem walInv_drop (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (nm b : GoString) (E : CoPset) (hE : ↑walN ⊆ E)
    (hE' : ↑osShN ⊆ E \ ↑walN)
    (hnm : walNameOk nm) (hNnm : N.Mem nm) (hb : N.Mem b) (hbw : walNameP b = false)
    (hbn : ¬ walNameOk b) (hbs : AreaSlot b) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗
      walUnlockedTok (W := W) -∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) ∗
      osNames (L := L) jr (N.diff [b]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [b])) ∗
      osNames (L := L) jr (.only [b]) (DFrac.own 1) (h.restrict jr (N.inter [b])) := by
  iintro #Hinv #Hsi Hnc Hu H
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walUnlockedTok (W := W) ∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h)
    iprop(walUnlockedTok (W := W) ∗
      osNames (L := L) jr (N.diff [b]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [b])) ∗
      osNames (L := L) jr (.only [b]) (DFrac.own 1) (h.restrict jr (N.inter [b])))
    E hE (fun s => by
      iintro Hb ⟨#Hsi, Hu, H⟩
      iapply walInvBody_drop C Mr R jr r s N h nm b hnm hNnm hb hbw hbn hbs hE' $$ Hb Hsi Hu H)
    $$ Hinv Hnc [Hu H]
  isplitl []
  · iexact Hsi
  iframe

/-- The minting (`walInvBody_mint`), as an update of the invariant. -/
theorem walInv_mint (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm tmp : GoString) (N : NameSet) (h hT : NamesH) (J : Ino) (X : List GoString)
    (hJ : NamesH) (E : CoPset) (hE : ↑walN ⊆ E) (hE' : ↑osShN ⊆ E \ ↑walN)
    (hnm : walNameOk nm) (hNnm : N.Mem nm) (hNt : ¬ N.Mem tmp) (hDe : N.diff [nm] ≠ .only [])
    (htmp : ¬ walNameOk tmp) (htw : walNameP tmp = false) (hXnm : nm ∉ X)
    (hX : ∀ b ∈ X, walNameP b = false) (hXt : ∀ b ∈ X, b ∈ walTmps) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗
      walUnlockedTok (W := W) -∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h -∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT -∗
      osNames (L := L) J (.except X) (DFrac.own 1) hJ ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ ∃ hC, walCreating (W := W) dir (.only [nm, tmp]) hC J ∗
        osNames (L := L) jr (N.diff [nm]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [nm])) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        osNames (L := L) J (.except X) (DFrac.own 1) hJ ∗
        ⌜hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm]) ∧
          hC.next = max (h.restrict jr (N.inter [nm])).next hT.next⌝ := by
  iintro #Hinv #Hsi Hnc Hu H HT HJ
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walUnlockedTok (W := W) ∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
      osNames (L := L) jr (.only [tmp]) (DFrac.own 1) hT ∗
      osNames (L := L) J (.except X) (DFrac.own 1) hJ)
    iprop(∃ hC, walCreating (W := W) dir (.only [nm, tmp]) hC J ∗
        osNames (L := L) jr (N.diff [nm]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [nm])) ∗
        osNames (L := L) jr (.only [nm, tmp]) (DFrac.own (1 : Qp).half) hC ∗
        osNames (L := L) J (.except X) (DFrac.own 1) hJ ∗
        ⌜hC.restrict jr (.only [tmp]) = hT.restrict jr (.only [tmp]) ∧
          hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm]) ∧
          hC.next = max (h.restrict jr (N.inter [nm])).next hT.next⌝)
    E hE (fun s => by
      iintro Hb ⟨#Hsi, Hu, H, HT, HJ⟩
      imod walInvBody_mint C Mr R jr r s dir nm tmp N h hT J X hJ hnm hNnm hNt hDe htmp htw hXnm hX hXt
        hE' $$ Hb Hsi Hu H HT HJ with ⟨%hC, Hb, Ht, HD, HC, HJ, %hp⟩
      imodintro
      iframe Hb
      iexists hC
      iframe
      ipureintro; exact hp)
    $$ Hinv Hnc [Hu H HT HJ]
  isplitl []
  · iexact Hsi
  iframe

/-- The unminting (`walInvBody_unmint`), as an update of the invariant. -/
theorem walInv_unmint (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (N : NameSet) (h : NamesH) (J : Ino) (E : CoPset) (hE : ↑walN ⊆ E) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walCreating (W := W) dir N h J ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Ht
  iapply walInv_step C Mr R jr r (walCreating (W := W) dir N h J) (walUnlockedTok (W := W))
    E hE (fun s => by
      iintro Hb Ht
      imod walInvBody_unmint C Mr R jr r s dir N h J $$ Hb Ht with ⟨Hb, Hu⟩
      imodintro
      iframe) $$ Hinv Hnc Ht

/-- The merge of two area claims (`walInvBody_merge2`), as an update of the invariant. -/
theorem walInv_merge2 (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N1 N2 N : NameSet) (h1 h2 : NamesH) (b1 b2 : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) (E : CoPset) (hE : ↑walN ⊆ E)
    (hE' : ↑osShN ⊆ E \ ↑walN)
    (hb1 : walNameOk b1) (hN1 : N1.Mem b1) (hb2 : walNameOk b2) (hN2 : N2.Mem b2)
    (hb21 : ¬ N1.Mem b2) (hN : ∀ b, N.Mem b ↔ N1.Mem b ∨ N2.Mem b) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ T -∗
      osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) jr N2 (DFrac.own (1 : Qp).half) h2 ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ T ∗ ∃ h, osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝ := by
  iintro #Hinv #Hsi Hnc Ht H1 H2
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ T ∗ osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 ∗
      osNames (L := L) jr N2 (DFrac.own (1 : Qp).half) h2)
    iprop(T ∗ ∃ h, osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝)
    E hE (fun s => by
      iintro Hb ⟨#Hsi, Ht, H1, H2⟩
      imod walInvBody_merge2 C Mr R jr r s N1 N2 N h1 h2 b1 b2 T hT hb1 hN1 hb2 hN2 hb21 hN hE'
        $$ Hb Hsi Ht H1 H2 with ⟨%h, Hb, Ht, H, %hp⟩
      imodintro
      iframe Hb Ht
      iexists h
      iframe
      ipureintro; exact hp)
    $$ Hinv Hnc [Ht H1 H2]
  isplitl []
  · iexact Hsi
  iframe

/-- The merge of a whole claim of the area into an area claim (`walInvBody_mergeIn`), as an update
of the invariant. -/
theorem walInv_mergeIn (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N1 N2 N : NameSet) (h1 h2 : NamesH) (b1 b2 : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) (E : CoPset) (hE : ↑walN ⊆ E)
    (hE' : ↑osShN ⊆ E \ ↑walN)
    (hb1 : walNameOk b1) (hN1 : N1.Mem b1) (hN2 : N2.Mem b2)
    (hno : ∀ b, N2.Mem b → ¬ walNameOk b) (hN : ∀ b, N.Mem b ↔ N1.Mem b ∨ N2.Mem b) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ T -∗
      osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) jr N2 (DFrac.own 1) h2 ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ T ∗ ∃ h, osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝ := by
  iintro #Hinv #Hsi Hnc Ht H1 H2
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ T ∗ osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 ∗
      osNames (L := L) jr N2 (DFrac.own 1) h2)
    iprop(T ∗ ∃ h, osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝)
    E hE (fun s => by
      iintro Hb ⟨#Hsi, Ht, H1, H2⟩
      imod walInvBody_mergeIn C Mr R jr r s N1 N2 N h1 h2 b1 b2 T hT hb1 hN1 hN2 hno hN hE'
        $$ Hb Hsi Ht H1 H2 with ⟨%h, Hb, Ht, H, %hp⟩
      imodintro
      iframe Hb Ht
      iexists h
      iframe
      ipureintro; exact hp)
    $$ Hinv Hnc [Ht H1 H2]
  isplitl []
  · iexact Hsi
  iframe

end iris

end WalFs
end EtcdGrove
end Perennial

end
