/-
`bbolt.Open_kv` (S3e, 2026-11-17; until then an axiom): `Spec/go_etcd_io/bbolt/Open_kv.lean` from
bbolt's error-free `Open` in the tree's shared mode (`Open_sharedNoErr.spec`, session S3d), at the
program's file-extension instances (`backend.theFs`, which carry `FsNoErrAll`: the steps do not fail
on files). The backend's `fileHolds path D` is what that spec takes (the claim on the name,
`nameHolds`); the database is opened in the namespace `dbNs path`, so that its names record its
path (`dbFile`), and what it keeps of the file (`dbRestF`: the claim, naming the file it opened) goes
into `ownDB`. The options: the backend's `optsAt` at options it accepts is bbolt's at options its
`Open` accepts (`optsAt_bolt`); the logger contract is bbolt's (`boltLogger_eq`).
-/
module

public import Spec.go_etcd_io.bbolt.Open_kv
public import Spec.go_etcd_io.bbolt.Open_sharedNoErrH

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The claim after `Open`'s create names the file it opened** (`crOut`/`crIno`, `OpenFileS.lean`):
a whole claim on `b` whose entry is the file `i`. -/
theorem crOut_file [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.Assumptions] (j : Ino) (b : GoString) (h : NamesH) (dq : DFrac)
    (oc : Option (Nat × Nat × Ino)) (i : Ino) (hi : crIno b h oc i) :
    crOut (GF := GF) j b h dq oc ⊢ ∃ h' : NamesH, osNames j (.only [b]) dq h' ∗
      ⌜h'.cur !! b = some (.file i)⌝ := by
  rcases oc with _ | ⟨x, s, i0⟩
  · simp only [crOut]
    iintro H
    iexists h
    iframe H
    ipureintro; exact hi
  · simp only [crOut]
    iintro ⟨-, -, H⟩
    iexists _
    iframe H
    ipureintro
    simp only [crIno] at hi
    subst hi
    simp only [NamesH.log]
    exact GMap.lookup_insert _ _ _

theorem bbolt.Open_kv.wp_proof :
    bbolt.Open_kv.spec (GF := GF) (hG := hG) := by
  intro hT hR path mode opts dq o D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.fileHolds, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · haveI := fax; haveI := fsax
    have h := bbolt.Open_sharedNoErrH.pendingS3d (GF := GF) (hG := hG)
    simp only [backend.fileHolds, backend.ownDB, backend.isDB, backend.boltLogger, hfs,
      onFs_some hfs]
    obtain ⟨Sio, hino, hpath, hs1, hs2⟩ := nex.ok
    iintro %Φ ⟨#Hpkg, Hf, Hbo, %Hok, #Hlog⟩ HΦ
    unfold fileHoldsF
    icases Hf with ⟨%R, %d, %b, %dqp, %j, %qc, %hn, %hpb, #Hinv, #Hsh, Hpath, Hcp, Hnm, Hnh⟩
    obtain ⟨hp, hb⟩ := hpb
    subst hp
    icases optsAt_bolt opts dq o Hok $$ Hbo with ⟨%f, %Hok', Hbo, Hback⟩
    ihave #Hlog' : ⌜(o.toBolt false f).logger = GoInterface.nil⌝ ∨
        bbolt.boltLogger (o.toBolt false f).logger $$ []
    · icases Hlog with (%Hl | #Hl)
      · ileft; ipureintro; exact Hl
      · iright
        rw [show (o.toBolt false f).logger = o.logger from rfl]
        iexact Hl
    wp_apply (h Sio hino hpath (dbNs (child d b)) R d b dqp j qc hn mode opts dq (o.toBolt false f) D hb)
      $$ [$Hpkg $Hinv $Hsh $Hpath $Hcp $Hnm $Hnh $Hbo $Hlog']
      as %db %err ⟨Hbo, Hpath, Hcp, %He, %oc, %γ, %i, Hcr, %hnc, #Hdb, #Hino, Hst, Hcl⟩
    · iframe %Hok'
      ipureintro; exact dbNs_osN _
    obtain ⟨hns, hci⟩ := hnc
    icases crOut_file j b hn (DFrac.own 1) oc i hci $$ Hcr with ⟨%h', Hnm, %hh'⟩
    ihave Hbo := Hback $$ Hbo
    iapply HΦ
    iframe Hbo
    isplitr
    · ipureintro; exact He
    iexists γ
    iframe Hdb Hst
    isplitl [Hpath Hcp Hnm Hcl]
    · unfold dbRestF
      iexists R, d, b, dqp, j, qc, h', i
      iframe Hinv Hsh Hpath Hcp Hnm Hino Hcl
      ipureintro; exact ⟨hns, hb, hh'⟩
    unfold wrTok dbFile
    isplitr
    · itrivial
    ipureintro; exact hns

end proof

end EtcdGrove
end Perennial
