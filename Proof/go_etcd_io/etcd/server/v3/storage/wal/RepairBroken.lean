/- Lean-first (no Rocq counterpart).

# `Repair`'s open of the `.broken` file (law L3; W7 of `notes/wal-fsext-plan.md`, W7-W12 log, fourteenth session)

`createNewWALFile[*os.File](<seg>.broken, true)` opens `O_WRONLY|O_CREATE|O_TRUNC` (`createNewWALFile.specFile`,
over an open spec `fileutil.OpenTriple`). The name `bt` is in the WAL directory's claim `(j, .except X, hj)`,
whose program half `Repair` holds (`walLastOpen`):

* `repBroken_tripleNew`: `bt` absent (`hj.cur !! bt = none`): `os.OpenFile.specCreateTruncSncN` with
  `walBroken_osAUnc`'s update (the program keeps a quarter in the update, the call gets the other); on a
  commit the name logged in the claim's history and lent (`walBrokenQ`), the new file whole and empty
  (`crTr`).
* `repBroken_tripleOld`: a leftover file `i` at `bt` (a previous `Repair`'s), already lent by
  `walInv_lendOther` (its `trFile i False`): `os.OpenFile.wp_truncS`, nothing logged, the file truncated.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section triples
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics] [os_sem : os.Assumptions]

theorem qQuarter_three : qQuarter + ((1 : Qp).half + qQuarter) = 1 := by
  apply Subtype.ext
  show (1 : Rat) / 2 / 2 + ((1 : Rat) / 2 + (1 : Rat) / 2 / 2) = 1
  grind

/-- What the absent case's open gives (see the file header). -/
def repBrokenNewA (R : Roots) (dir : GoString) (I : GMap GoString Nat) (dq : DFrac) (j : Ino) (X : List GoString) (hj : NamesH)
    (o : WalOut) (bt : GoString) (qc : Qp) : Option (Nat × Nat × Ino) → Bool → IProp GF :=
  fun x ok => iprop(osPathS R dir dq j ∗ osCallPerm (callKey R dir) qc ∗ walBrokenQ (W := W) dir I j X hj o bt x ∗
    crOutN j (.except X) bt hj (DFrac.own qQuarter) x ∗ crTr (ok = true) x)

/-- **The absent case's open spec** (see the file header). -/
theorem repBroken_tripleNew (wp_OpenN : os.OpenFile.specCreateTruncSncN (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (I : GMap GoString Nat) (dq : DFrac) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut)
    (bt : GoString) (qc : Qp) (hb : NameOk bt) (hN : (NameSet.except X).Mem bt)
    (hcur : hj.cur !! bt = none) :
    fileutil.OpenTriple
      iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm (callKey R dir) qc ∗
        osNames j (.except X) (DFrac.own qQuarter) hj ∗
        osAUnc (osNames j (.except X) (DFrac.own ((1 : Qp).half + qQuarter)) hj)
          (crOutN j (.except X) bt hj (DFrac.own ((1 : Qp).half + qQuarter)))
          (walBrokenQ (W := W) dir I j X hj o bt))
      (child dir bt) (wal.walOpenFlag true) (W32 384) (repBrokenNewA (W := W) R dir I dq j X hj o bt qc)
      (crIno bt hj) := by
  obtain ⟨hfl, hcr, htr⟩ := walOpenFlag_ok
  unfold fileutil.OpenTriple
  iintro %Ψ ⟨#Hospkg, #Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΨ
  iapply wp_OpenN dir bt (wal.walOpenFlag true) (W32 384) R j (.except X) dq hj qQuarter
    ((1 : Qp).half + qQuarter) qc (walBrokenQ (W := W) dir I j X hj o bt) hfl hcr htr hb hN hcur
    qQuarter_three $$ [$Hospkg $Hos $Hsi $Hp $Hperm $Hn $Hau]
  inext
  iintro %f %err ⟨Hp, Hperm, %x, HQ, Ho, Htr, Hr⟩
  iapply HΨ
  unfold fileutil.openPost
  iexists x
  icases Hr with (⟨%fd, %i, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok⟩)
  · obtain ⟨rfl, hfd, hi⟩ := hres
    ileft
    isplitr
    · ipureintro; rfl
    isplitl [Hp Hperm HQ Ho Htr]
    · simp only [repBrokenNewA]
      iframe
    iexists fd, i
    iframe
    ipureintro; exact ⟨hfd, hi⟩
  · iright
    isplitr
    · ipureintro; exact herr
    iframe Hok
    simp only [repBrokenNewA]
    iframe
    have : (false = true) = (err = interface.nil) := by
      simp only [Bool.false_eq_true, false_iff, eq_iff_iff]; exact herr.1
    rw [this]
    iexact Htr

/-- What the leftover case's open gives (see the file header). -/
def repBrokenOldA (R : Roots) (dir : GoString) (dq dqn : DFrac) (j : Ino) (X : List GoString)
    (hj : NamesH) (i : Ino) (qc : Qp) : Unit → Bool → IProp GF :=
  fun _ ok => iprop(osPathS R dir dq j ∗ osNames j (.except X) dqn hj ∗ osCallPerm (callKey R dir) qc ∗
    trFile i (ok = true))

/-- **The leftover case's open spec** (see the file header). -/
theorem repBroken_tripleOld (R : Roots) (dir : GoString) (dq dqn : DFrac) (j : Ino) (X : List GoString)
    (hj : NamesH) (bt : GoString) (i : Ino) (qc : Qp) (hb : NameOk bt) (hN : (NameSet.except X).Mem bt)
    (hcur : hj.cur !! bt = some (.file i)) :
    fileutil.OpenTriple
      iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osNames j (.except X) dqn hj ∗
        osCallPerm (callKey R dir) qc ∗ trFile i False)
      (child dir bt) (wal.walOpenFlag true) (W32 384) (repBrokenOldA (GF := GF) R dir dq dqn j X hj i qc)
      (fun _ i' => i' = i) := by
  obtain ⟨hfl, -, htr⟩ := walOpenFlag_ok
  unfold fileutil.OpenTriple
  iintro %Ψ ⟨#Hospkg, #Hos, #Hsi, Hp, Hn, Hperm, Htr⟩ HΨ
  iapply os.OpenFile.wp_truncS dir bt (wal.walOpenFlag true) (W32 384) R j i (.except X) dq dqn hj qc
    hfl htr hb hN hcur $$ [$Hospkg $Hos $Hsi $Hp $Hn $Hperm $Htr]
  inext
  iintro %f %err ⟨Hp, Hn, Hperm, Htr, Hr⟩
  iapply HΨ
  unfold fileutil.openPost
  iexists ()
  icases Hr with (⟨%fd, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok, -⟩)
  · obtain ⟨rfl, hfd⟩ := hres
    ileft
    isplitr
    · ipureintro; rfl
    isplitl [Hp Hperm Hn Htr]
    · simp only [repBrokenOldA]
      iframe
    iexists fd, i
    iframe
    ipureintro; exact ⟨hfd, rfl⟩
  · iright
    isplitr
    · ipureintro; exact herr
    iframe Hok
    simp only [repBrokenOldA]
    iframe
    have : (false = true) = (err = interface.nil) := by
      simp only [Bool.false_eq_true, false_iff, eq_iff_iff]; exact herr.1
    rw [this]
    iexact Htr

end triples

end WalFs
end EtcdGrove
end Perennial

end
