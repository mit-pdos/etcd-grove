/- Lean-first (no Rocq counterpart).

# A path to the WAL area, lent by the invariant (W4 log, nineteenth session)

The invariant keeps a fraction of the area's spine (`walNamesRes`'s `∃ q, osPathS R r q jr`) and lends
half of it, kept by the borrower: `walInv_areaPath`. `Create` builds the two spines to its new WAL's
directory (`renameWAL`'s spine law, `createSp`) from it rather than from its caller's spine, since one of
them stays with the file pipeline `renameWAL` starts, which an error after the rename leaves running:
the caller's spine then comes back whole on every arm of `Create`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **The names' resources lend half their area spine.** -/
theorem walNamesRes_areaPath (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay) :
    walNamesRes (L := hG.goose_localGS) (W := W) R jr r Ls ⊢
      walNamesRes (L := hG.goose_localGS) (W := W) R jr r Ls ∗
        ∃ q : Qp, osPathS (L := hG.goose_localGS) R r (DFrac.own q) jr := by
  unfold walNamesRes
  iintro ⟨%o, %Wn, Ha, Hs, %hf, ⟨%qs, Hsp⟩, Hl⟩
  icases (osPathS_frac (L := hG.goose_localGS) R r qs.half qs.half jr).1 $$ [Hsp] with ⟨Hsp, Hsp2⟩
  · rw [Qp.half_add_half]; iexact Hsp
  isplitr [Hsp2]
  · iexists o, Wn
    iframe
    isplitr
    · ipureintro; exact hf.1
    ipureintro; exact hf.2
  · iexists qs.half; iexact Hsp2

/-- **A path to the area, lent by the invariant body.** -/
theorem walInvBody_areaPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗
        ∃ q : Qp, osPathS (L := hG.goose_localGS) R r (DFrac.own q) jr := by
  iintro Hb
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt, Hnms, Hbd⟩
  icases walNamesRes_areaPath R jr r Ls $$ Hnms with ⟨Hnms, Hp⟩
  imodintro
  iframe Hp
  iexists Ls, cl, n, F
  iframe
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  ipureintro; exact HAt

/-- **A path to the area, lent by the invariant at a program step.** -/
theorem walInv_areaPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        ∃ q : Qp, osPathS (L := hG.goose_localGS) R r (DFrac.own q) jr := by
  iintro #Hinv Hnc
  iapply walInv_step C Mr R jr r iprop(emp)
    iprop(∃ q : Qp, osPathS (L := hG.goose_localGS) R r (DFrac.own q) jr)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb -
      imod walInvBody_areaPath C Mr R jr r s $$ Hb with ⟨Hb, Hp⟩
      imodintro
      iframe)
    $$ Hinv Hnc []
  iempintro

end iris

end WalFs
end EtcdGrove
end Perennial

end
