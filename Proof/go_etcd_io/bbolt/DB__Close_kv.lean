/-
`bbolt.DB.Close_kv` (S3e, 2026-11-17; until then an axiom): `Spec/go_etcd_io/bbolt/DB__Close_kv.lean`
from bbolt's `DB.Close_ownNoErr.spec` (the file of the inode `Open` named given back, `fileHolds i D`),
at the program's file-extension instances (`backend.theFs`, with `FsNoErrAll`). What the database kept
of its file (`ownDB`'s `dbRestF`: the claim on its name, naming that inode) and the file make the
backend's `fileHolds` again; its path is `dbFile`'s (`dbNs` is injective).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close_kv
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
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem bbolt.DB.Close_kv.wp_proof
    (h : ∀ [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions],
      bbolt.DB.Close_ownNoErrH.spec (GF := GF) (hG := hG)) :
    bbolt.DB.Close_kv.spec (GF := GF) (hG := hG) := by
  intro db γ D path
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.isDB, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.fileHolds, backend.ownDB, backend.isDB, onFs_some hfs]
    obtain ⟨Sio, hino, -, hs1, hs2⟩ := nex.ok
    iintro %Φ ⟨-, #Hdb, Hpath, -, Hst, Hrest⟩ HΦ
    iunfold dbFile at Hpath
    icases Hpath with %Hpath
    unfold dbRestF
    icases Hrest with ⟨%R, %d, %b, %dq, %j, %qc, %hn, %i, %hr, #Hinv, #Hsh, Hp, Hcp, Hnm, #Hino⟩
    obtain ⟨hns, hb, hi⟩ := hr
    have hpath : path = child d b := dbNs_inj (Hpath.symm.trans hns)
    subst hpath
    wp_apply (h Sio hino db γ i D) $$ [$Hdb $Hino $Hst] as %err ⟨%He, Hf⟩
    iapply HΦ
    isplitr
    · ipureintro; exact He
    unfold fileHoldsF
    iexists R, d, b, dq, j, qc, hn
    iframe Hinv Hsh Hp Hcp Hnm
    isplitr
    · ipureintro; exact ⟨rfl, hb⟩
    unfold bbolt.nameHolds
    ileft
    iexists i
    iframe Hf
    ipureintro; exact hi

end proof

end EtcdGrove
end Perennial
