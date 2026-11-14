/- Lean-first (no Rocq counterpart).

# `Create`'s WAL name is absent (W4, `notes/wal-fsext-plan.md`, eleventh session)

`renameWAL`'s `os.RemoveAll(dir)` and the rename onto `nm` need `nm` absent in the program's claim on
it. The invariant knows it (`AbsentNone`: a WAL name of the area with no WAL is absent in every area
claim of the invariant's holding it), given that `dir` has no WAL, which the client's update knows
(`walAbsent dir`). A claim's history is fixed while its holder holds a fraction of it, so the fact,
learned once, stays true.

* `walInvBody_absent`: the invariant's contents, `s.wal !! dir = none`, a fraction of a claim of the
  area holding `nm`: `nm` absent in it (`osClaims_keys` finds it among the invariant's, through
  `WalsCreateOk`'s claim holding `nm`).
* `walInv_absent`: the same at a program step (`notCrashed`), the fact `s.wal !! dir = none` read off
  the client's update, opened and aborted at once.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- See the file header. -/
theorem walInvBody_absent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N : NameSet) (dq : DFrac) (h : NamesH) (dir nm : GoString)
    (hin : InArea r dir nm) (hN : N.Mem nm) (hsw : s.wal !! dir = none) {Em : CoPset}
    (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      osNames (L := L) jr N dq h ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ osNames (L := L) jr N dq h ∗
        ⌜h.cur !! nm = none⌝ := by
  iintro Hb #Hsi H
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, #Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Ht, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt⟩
  imod osClaims_keys R jr N _ h _ (nameSet_ne_empty hN) hE $$ Hsi H Hcl with ⟨H, Hcl, %hkeys⟩
  obtain ⟨N1, h1, hm1, hN1⟩ := hwc nm hin.1
  obtain ⟨rfl, rfl⟩ := hkeys ((jr, N1, h1), _) (List.mem_map_of_mem hm1) rfl nm hN hN1
  have hnone : h1.cur !! nm = none :=
    (hab.1 dir nm (hr ▸ hin) hsw).1 N1 h1 hm1 hN1
  imodintro
  iframe H
  isplitl
  · iexists Ls, cl, n, F
    iframe Hg Hcl Hn HF Ht Hpk
    isplitr; · ipureintro; exact hr
    isplitr; · ipureintro; exact hwo
    isplitr; · ipureintro; exact hwc
    isplitl [HCRa]
    · iexists CR; iframe HCRa; ipureintro; exact hCR
    isplitr; · ipureintro; exact hab
    isplitr; · ipureintro; exact hwn
    isplitl [HK Hcc]
    · iexists K, cc; iframe HK Hcc; ipureintro; exact hdk
    ipureintro; exact hAt
  · ipureintro; exact hnone

/-- See the file header. -/
theorem walInv_absent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (dq : DFrac) (h : NamesH) (dir nm : GoString) (md : List w8) (Q : IProp GF)
    (hin : InArea r dir nm) (hN : N.Mem nm) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗
      (AU <{ walAbsent (W := W) dir }> @ walAuMask, ∅ <{ walDiskAt (W := W) dir (walDurFresh md), COMM Q }>) -∗
      osNames (L := L) jr N dq h ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗
      (AU <{ walAbsent (W := W) dir }> @ walAuMask, ∅ <{ walDiskAt (W := W) dir (walDurFresh md), COMM Q }>) ∗
      osNames (L := L) jr N dq h ∗ ⌜h.cur !! nm = none⌝ := by
  iintro #Hinv #Hsi Hnc Hau H
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗
      (AU <{ walAbsent (W := W) dir }> @ walAuMask, ∅ <{ walDiskAt (W := W) dir (walDurFresh md), COMM Q }>) ∗
      osNames (L := L) jr N dq h)
    iprop((AU <{ walAbsent (W := W) dir }> @ walAuMask, ∅ <{ walDiskAt (W := W) dir (walDurFresh md), COMM Q }>) ∗
      osNames (L := L) jr N dq h ∗ ⌜h.cur !! nm = none⌝)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, Hau, H⟩
      -- read `dir`'s absence off the client's update, aborted at once
      have hsub : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
        intro p hp
        exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, (LawfulSet.mem_diff.1 hp).2⟩
      imod (fupd_mask_subseteq hsub) with Hmc
      ihave Hacc := aupd_aacc $$ Hau
      unfold atomic_acc
      imod Hacc with Hacc
      isimp only [texist_nil] at Hacc
      icases Hacc with ⟨Hab0, Hcla⟩
      irevert Hab0
      dsimp only [Std.Tele.app]
      iintro Hab0
      unfold walAbsent walDirIs
      icases Hab0 with ⟨%M, HM, %HMd⟩
      iunfold walInvBody at Hb
      icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
      icases walOwn_agree s M $$ Hg HM with %HMs
      have hsd : s.wal !! dir = none := by
        have := HMs dir; rw [(walOptLe_none_iff _).1 HMd] at this; exact (walOptLe_none_iff _).1 this
      icases Hcla with ⟨Hab, -⟩
      imod Hab $$ [HM] with Hau
      · iexists M; iframe HM; ipureintro; exact HMd
      imod Hmc with -
      ihave Hb : walInvBody (L := L) (W := W) C Mr R jr r s $$ [Hg Hrest]
      · unfold walInvBody; iexists Ls, cl, n, F; iframe
      imod walInvBody_absent C Mr R jr r s N dq h dir nm hin hN hsd walN_osShN_top $$ Hb Hsi H
        with ⟨Hb, H, %hn⟩
      imodintro
      iframe
      ipureintro; exact hn)
    $$ Hinv Hnc [Hau H]
  iframe Hau H; iexact Hsi

end iris

end WalFs
end EtcdGrove
end Perennial

end
