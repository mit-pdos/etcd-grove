/- Lean-first (no Rocq counterpart).

# `Create`'s abort before the minting (W4, eleventh session)

After the drop of `nm.tmp` off the area claim and before the minting, an error gives `walAreaRes` back:
the claim on `nm.tmp` (whatever it holds now, a `tmpDirH`) merged back into the program's half of the
area claim (`walInv_mergeIn`, the free lock token excluding a creating entry), and `walAreaRes` rebuilt
with the claims under every other name (`area_give`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateMerge

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The merged claim says what the parts said. -/
theorem abort_cur (N : NameSet) (h h' : NamesH) (jr : Ino) (tmp : GoString)
    (hself : h.restrict jr N = h) (hself' : h'.restrict jr N = h')
    (h1 : h'.restrict jr (N.diff [tmp]) = (h.restrict jr (N.diff [tmp])).restrict jr (N.diff [tmp]))
    (b : GoString) (hb : b ≠ tmp) : h'.cur !! b = h.cur !! b := by
  by_cases hN : N.Mem b
  · have hm : (N.diff [tmp]).Mem b := (NameSet.mem_diff _ _ _).2 ⟨hN, by simpa using hb⟩
    rw [cur_of_part h1 hm]
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ hm]
  · have e1 : h'.cur !! b = none := by
      rw [← hself']; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hN]
    have e2 : h.cur !! b = none := by
      rw [← hself]; simp only [NamesH.restrict]; rw [restrictN_lookup_not _ _ _ hN]
    rw [e1, e2]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- See the file header. -/
theorem create_abortTmp (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (nm : GoString) (hT : NamesH)
    (Wn : List GoString) (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hNm : N.Mem nm) (hself : h.restrict jr N = h) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half)
        (h.restrict jr (N.diff [tmpName nm])) -∗
      tmpDirH jr (tmpName nm) hT -∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) -∗
      walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walUnlockedTok (W := W) ∗
        walAreaRes (L := hG.goose_localGS) jr := by
  iintro #Hinv #Hsi Hnc Hu HN Ht Hcl Hsf
  unfold tmpDirH
  icases Ht with ⟨HT, Hs⟩
  have hNnm : (N.diff [tmpName nm]).Mem nm :=
    (NameSet.mem_diff _ _ _).2 ⟨hNm, by simpa using (tmpName_ne nm).symm⟩
  imod walInv_mergeIn C Mr R jr r (N.diff [tmpName nm]) (.only [tmpName nm]) N
    (h.restrict jr (N.diff [tmpName nm])) hT nm (tmpName nm) (walUnlockedTok (W := W))
    walUnlockedTok_excl ⊤ CoPset.subseteq_top walN_osShN_top hnm hNnm (by simp [NameSet.Mem])
    (fun b hb => by simp only [NameSet.Mem, List.mem_singleton] at hb; subst hb; exact tmpName_not_walName nm)
    (fun b => by
      rw [NameSet.mem_diff]
      by_cases hb : b = tmpName nm
      · subst hb
        constructor
        · intro _; right; simp [NameSet.Mem]
        · intro _; exact areaOk_tmp hok hnm
      · simp [NameSet.Mem, hb])
    $$ Hinv Hsi Hnc Hu HN HT with ⟨Hnc, Hu, %h', HN, %hm⟩
  imod osNames_self R jr N _ h' CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself'⟩
  have htc : h'.cur !! tmpName nm = hT.cur !! tmpName nm := by
    have e := cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm))
    exact e
  imodintro
  iframe Hnc Hu
  iapply area_give N N h h' cl jr (tmpName nm) Wn hok (fun _ => Iff.rfl) (tmpName_not_walName nm)
    (fun b hb _ => abort_cur N h h' jr (tmpName nm) hself hself' hm.1 b hb)
  iframe HN Hcl Hsf
  rw [htc]
  iexact Hs

end iris

end WalFs
end EtcdGrove
end Perennial

end
