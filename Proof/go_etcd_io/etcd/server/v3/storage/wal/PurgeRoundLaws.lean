/- Lean-first (no Rocq counterpart).

# What a purge round uses of the WAL (unit `locks`, session 10; `notes/wal-units/locks.md`)

The tester's `purgeRound` (a round of `fileutil.purgeFile`'s loop on the WAL directory, while the WAL's
handle is lent to it, `walOpenWF_lend`) removes the oldest names ending in `"wal"`. Besides the two removal
updates (`walPurge_osAUnc` for a segment, `walPurgeOther_osAUnc` for a leftover file) and the leftover's
lending (`walInv_lendOther`/`walInv_unlendOther`, to learn that it is a file), it needs:

* `walInv_walFiles`: every `.wal` entry of the WAL directory's claim is a file (`SegsNamed`'s second part),
  read with the directory's key and a fraction of the claim;
* `purge_openTriple`: `os.OpenFile(dir/b, O_WRONLY, 0600)` of a file of the claim, as `TryLockFile` takes it
  (`openWALFiles.lean`'s `walOpen_triple`, restated here so that the round's proof imports no proof file).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeOther
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeLend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenLend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateLocked
public import Proof.os.NsS

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section look
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **Every `.wal` entry of a keyed WAL directory's claim is a file** (the invariant's body). -/
theorem walInvBody_walFiles (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (q : Qp) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own q) hj -∗
      ⌜∀ b e, walNameP b = true → hj.cur !! b = some e → ∃ i, e = .file i⌝ ∗
        osNames (L := L) j (.except X) (DFrac.own q) hj ∗ walInvBody (L := L) (W := W) C Mr R jr r s := by
  iintro Hb #Hkey Hq
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, HCR,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hkey with %HK
  obtain ⟨lay1, hj1, hl1, hj1j, hjjr, hXw, honce, hcoh, hexcl⟩ := Hdko.1 dir j X HK
  obtain ⟨l1, l2, hcl, hn1, hn2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  icases osNames_agree j (.except X) _ _ hj1 hj $$ Hα Hq with %Hhj
  subst Hhj
  have hclm : (j, NameSet.except X, hj1) ∈ l1 ++ (j, NameSet.except X, hj1) :: l2 :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hsn : SegsNamed lay1.segs hj1.cur :=
    (Hnm dir lay1 hl1).1 hj1 ⟨X, hXw, by rw [hj1j]; exact hclm, by rw [hj1j]; exact hcoh⟩
  iframe Hq
  isplitr
  · ipureintro; exact hsn.2
  iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
  iframe Hg Hcm Hlays HCR Htl Hpk Hnms
  isplitr
  · ipureintro; exact Har
  isplitl [Hl1 Hα Hl2]
  · iapply (osClaims_split _ _ _ _).2
    iframe Hl1 Hα Hl2
  isplitr
  · ipureintro; exact Hok
  isplitr
  · ipureintro; exact Hco
  isplitr
  · ipureintro; exact Han
  isplitr
  · ipureintro; exact Hnm
  isplitl [Hdk Hcp]
  · iexists K, cp; iframe Hdk Hcp; ipureintro; exact Hdko
  ipureintro; exact ⟨HAt, Hbd⟩

/-- `walInvBody_walFiles` at any step. -/
theorem walInv_walFiles (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (q : Qp) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) (DFrac.own q) hj ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) j (.except X) (DFrac.own q) hj ∗
        ⌜∀ b e, walNameP b = true → hj.cur !! b = some e → ∃ i, e = .file i⌝ := by
  iintro #Hinv Hnc #Hk Hq
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_walFiles C Mr R jr r s dir j X hj q $$ Hb Hk Hq with ⟨%hx, Hq, Hb⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hq
  ipureintro; exact hx

end look

section triple
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [os_sem : os.Assumptions]

/-- `os.OpenFile(d/b, flag, 0600)` of a file `b` of a claim, as `TryLockFile` takes it: the claim's
resources lent and given back, the inode `i` (`walOpen_triple`'s statement). -/
theorem purge_openTriple (R : Roots) (d b : GoString) (dq : DFrac) (j i : Ino)
    (N : NameSet) (dqn : DFrac) (h : NamesH) (qc : Qp) (flag : w64)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    fileutil.OpenTriple (X := Unit)
      (iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
      (child d b) flag (W32 384)
      (fun _ _ => iprop(osPathS (GF := GF) R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
      (fun _ i' => i' = i) := by
  unfold fileutil.OpenTriple
  iintro %Φ ⟨#Hospkg, #Hinv, #Hsi, Hp, Hn, Hperm⟩ HΦ
  wp_apply os.OpenFile.wp_fileS d b flag (W32 384) R j i N dq dqn h qc hfl htr hb hN hi
    $$ [Hp Hn Hperm] as %f %err ⟨Hp, Hn, Hperm, Hr⟩
  · iframe; (repeat' isplitl []) <;> iassumption
  iapply HΦ
  iunfold fileutil.openPost
  iexists ()
  icases Hr with (⟨%fd, %hh, Hf, Ho, Hfd⟩ | ⟨%hh, Herr, -⟩)
  · ileft
    isplitr
    · ipureintro; exact hh.1
    simp only []
    iframe
    ipureintro; exact ⟨hh.2, rfl⟩
  · iright
    isplitr
    · ipureintro; exact hh
    simp only []
    iframe

end triple

end WalFs
end EtcdGrove
end Perennial

end
