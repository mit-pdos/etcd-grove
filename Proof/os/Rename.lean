/-
Proof of `Spec/os/Rename.lean` (S5, 2026-11-18; until then an axiom, D22 S-f, 2026-10-19):
`os.Rename` of a file `fileAt src D` onto the name of an open database's file (`bPath γ dst`), from
the model's error-free rename in the tree's shared mode (`rename_fileNE`, below), at `theFs` (whose
`FsNoErrAll` covers every path). The two claims come with their own shared invariants; the two
agree on the roots at the call's first step (`Fs.wp_osSharedAgree`), and are of distinct keys, being
both whole (`osNames`' validity).
-/
module

public import Spec.os.Rename
public import Spec.os.RenameS
public import GooseLang.Ext.Fs.NoErrSpecsRename
public import GooseLang.Ext.Fs.TreeSharedRoots

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

section noerr
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [go.BasicIntoValInj] [os.Assumptions]
open Fs

/-- **The model's rename of a file onto a non-directory, with no error** (S5): under `NoIoErr`
covering every path, the model's `LstatDir` of a target that is no directory, then one `CallBegin`
and `rename(2)`, which has a success, so returns 0 (`wp_osRenameFileSNE`): `nil`, the two claims
(whole, distinct keys) after the rename. A lemma of this proof, not a spec (one spec per function:
`os.Rename`'s are `Spec/os/RenameS.lean`'s and this file's). -/
private theorem rename_fileNE :
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ p, Sio.path p) →
  ∀ (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet) (R : Roots) (dq dq' : DFrac)
    (h h' : NamesH) (qc : Qp),
  NameOk bs → NameOk bt → N.Mem bs → N'.Mem bt → (j, N) ≠ (j', N') →
  h.cur !! bs = some (.file i) → (∀ J, h'.cur !! bt ≠ some (.dir J)) →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      osNames j N (DFrac.own 1) h ∗ osNames j' N' (DFrac.own 1) h' }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d' bt)))
  {{ RET #interface.nil; osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      ∃ h1 h2 : NamesH, ⌜h1.cur = GMap.delete bs h.cur ∧ h2.cur = <[bt := .file i]> h'.cur⌝ ∗
        osNames j N (DFrac.own 1) h1 ∗ osNames j' N' (DFrac.own 1) h2 }}
 := by
  intro Sio _ hS d bs d' bt j j' i N N' R dq dq' h h' qc hbs hbt hN hN' hkey hsrc htgt
  wp_start as ⟨#Hos, #Hsi, Hp, Hp', Hperm, Hn1, Hn2⟩
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn1 with ⟨Hn1, #Hlb1⟩
  imod osNames_next R j' N' _ h' CoPset.subseteq_top $$ Hsi Hn2 with ⟨Hn2, #Hlb2⟩
  ihave #Hlb := osLogLb_max h.next h'.next $$ [Hlb1 Hlb2]
  · iframe #
  iclear Hlb1 Hlb2
  wp_apply wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply wp_osLstatDirS_mem R d' bt j' N' dq' (DFrac.own 1) h' t s0 qc hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp' Hn2 Hk as %isDir %e %hd Hperm Hp' Hn2
  have hd1 : isDir ≠ 1 := fun h1 => by obtain ⟨⟨J, hJ⟩, -⟩ := hd h1; exact htgt J hJ
  rw [decide_eq_false (show isDir ≠ W64 1 from hd1)]
  wp_auto
  wp_apply +noauto wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t2 %s1 %hs1 Hk Hls
  iclear Hls
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_osRenameFileSNE Sio hS R d bs d' bt j j' i N N' dq dq' h h' t2 s1 qc hbs hbt hN hN'
    hkey hsrc htgt (Nat.le_trans (Nat.le_max_left _ _) hs1)
    (Nat.le_trans (Nat.le_max_right _ _) hs1) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hp' Hn1 Hn2 Hk
  iintro Hperm Hp Hp' ⟨%x, -, Hn1, Hn2⟩
  wp_auto
  iapply HΦ
  iframe Hp Hp' Hperm
  iexists _, _
  iframe Hn1 Hn2
  ipureintro; exact ⟨rfl, rfl⟩

end noerr

open Fs in
/-- Two whole claims are of distinct keys. -/
theorem osNames_keys_ne [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (j j' : Ino) (b b' : GoString)
    (h h' : NamesH) :
    osNames (L := hG.goose_localGS) j (.only [b]) (DFrac.own 1) h ∗
      osNames (L := hG.goose_localGS) j' (.only [b']) (DFrac.own 1) h' ⊢
      ⌜(j, NameSet.only [b]) ≠ (j', NameSet.only [b'])⌝ ∗
      osNames (L := hG.goose_localGS) j (.only [b]) (DFrac.own 1) h ∗
      osNames (L := hG.goose_localGS) j' (.only [b']) (DFrac.own 1) h' := by
  by_cases hk : (j, NameSet.only [b]) = (j', NameSet.only [b'])
  · obtain ⟨rfl, hN⟩ := Prod.mk.inj hk
    rw [← hN]
    have hne : NameSet.only [b] ≠ .only [] := by simp
    rw [osNames_of_ne _ _ hne, osNames_of_ne _ _ hne]
    iintro ⟨H1, H2⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
    exact absurd hv.1 (dfrac_own_one_op_invalid _)
  · iintro ⟨H1, H2⟩
    iframe H1 H2
    ipureintro; exact hk

/-- See the file header. -/
theorem os.Rename.wp_proof [os.Assumptions] :
    os.Rename.spec (GF := GF) (hG := hG) := by
  intro src dst D γ
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.fileAt, onFs_none hfs]
    iintro %Φ ⟨H, -⟩ HΦ
    iexfalso; iexact H
  · have h' := @rename_fileNE _ _ _ _ _ GF hG _ Sx okx hasx _ _
    simp only [backend.fileAt, backend.bPath, backend.fileFree, onFs_some hfs, fileAtF, nameAtF,
      fileFreeF]
    obtain ⟨Sio, -, hpath, hs1, -⟩ := nex.ok
    haveI := hs1
    iintro %Φ ⟨Hs, ⟨%i', #Hino, Hd⟩⟩ HΦ
    icases Hs with ⟨%i, ⟨%R, %d, %bs, %dq, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hcp, Hn⟩, Hf⟩
    icases Hd with ⟨%R', %d', %bt, %dq', %j', %qc', %hh, %hp', -, #Hsh', Hp', Hcp', Hn'⟩
    obtain ⟨rfl, hbs, hi⟩ := hp
    obtain ⟨rfl, hbt, hi'⟩ := hp'
    icases osNames_keys_ne j j' bs bt h hh $$ [Hn Hn'] with ⟨%hkey, Hn, Hn'⟩
    · iframe Hn Hn'
    -- the two invariants' roots, at the call's first step
    iapply Fs.wp_osSharedAgree (L := hG.goose_localGS) R R' _ rfl CoPset.subseteq_top Φ $$ Hsh Hsh'
    iintro %hR
    subst hR
    wp_apply (h' Sio hpath d bs d' bt j j' i (.only [bs]) (.only [bt]) R dq dq' h hh qc hbs hbt
      (by simp [Fs.NameSet.Mem]) (by simp [Fs.NameSet.Mem]) hkey hi
      (fun J hJ => by rw [hi'] at hJ; cases hJ))
      $$ [$Hinv $Hsh $Hp $Hp' $Hcp $Hn $Hn'] as ⟨Hp, Hp', Hcp, %h1, %h2, %hc, Hn1, Hn2⟩
    iapply HΦ
    isplitr
    · ipureintro; rfl
    isplitl [Hp' Hcp' Hn2 Hf]
    · iexists i
      iframe Hf
      iexists R, d', bt, dq', j', qc', h2
      iframe Hinv Hsh Hp' Hcp' Hn2
      ipureintro
      refine ⟨rfl, hbt, ?_⟩
      rw [hc.2]; exact GMap.lookup_insert _ _ _
    · iexists R, d, bs, dq, j, qc, h1
      iframe Hinv Hsh Hp Hcp Hn1
      ipureintro
      refine ⟨rfl, hbs, ?_⟩
      rw [hc.1]; exact GMap.lookup_delete _ _

end proof

end EtcdGrove
end Perennial
