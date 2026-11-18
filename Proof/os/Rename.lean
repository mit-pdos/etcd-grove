/-
Proof of `Spec/os/Rename.lean` (S5, 2026-11-18; until then an axiom, D22 S-f, 2026-10-19):
`os.Rename` of a file `fileAt src D` onto the name of an open database's file (`bPath γ dst`), from
the model's error-free rename in the tree's shared mode (`os.Rename.specFileSNE`, the same function's
spec in the shared mode, proved in `Proof/os/RenameSNE.lean`: a derivation, so its proof is used
directly, not taken as a callee's hypothesis), at `theFs` (whose
`FsNoErrAll` covers every path). The two claims come with their own shared invariants; the two
agree on the roots at the call's first step (`Fs.wp_osSharedAgree`), and are of distinct keys, being
both whole (`osNames`' validity).
-/
module

public import Spec.os.Rename
public import Proof.os.RenameSNE
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
  · have h' := @os.Rename.wp_proofFileSNE _ _ _ Sx okx hasx _ _ _ GF hG _ _
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
