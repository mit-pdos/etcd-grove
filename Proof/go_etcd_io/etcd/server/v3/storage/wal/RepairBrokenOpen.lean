/- Lean-first (no Rocq counterpart).

# `Repair`'s `createNewWALFile[*os.File](<seg>.broken, true)` (law L3; W7 of `notes/wal-fsext-plan.md`,
W7-W12 log, fifteenth session)

`repair_brokenOpen`: both cases of the `.broken` name `bt` in the WAL directory's claim `(j, .except X, hj)`
(the program's half, the claim out in `o`), as one triple:

* absent (`hj.cur !! bt = none`): the half split in quarters, the update `walBroken_osAUnc`, the open
  `repBroken_tripleNew`; on success the create committed (`crIno` rules out the no-effect outcome), the
  quarters joined at the new history, the new file lent (`lendKey j bt`) and whole, empty;
* a leftover file (`some (.file i)`): `walInv_lendOther` first (its `tmpEnt` the file whole), then the
  `O_TRUNC` open `repBroken_tripleOld`; on success the file truncated, the history unchanged;
* a directory (`some (.dir _)`): `walInv_lendOther`'s `tmpEnt` is `False`.

On success: the file open for writing at offset 0, held whole and empty (`trFile i True`, what
`io.CopyFiles.spec` takes), the claim's half at a history naming it at `bt`, the record with `lendKey j bt`.
On failure nothing is returned but the path and the call permission (`Repair` returns `false`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairBroken
public import Perennial.GooseLang.NotCrashed

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

/-- What `repair_brokenOpen` gives on success. -/
def repBrokenOk (dir bt : GoString) (j : Ino) (X : List GoString) (o : WalOut) (f : Loc) : IProp GF :=
  iprop(∃ (fd : w64) (i : Ino) (hj' : NamesH), ⌜0 ≤ fd.toInt ∧ hj'.cur !! bt = some (.file i)⌝ ∗
    os.ownFile f fd (child dir bt) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
    osFd fd (DFrac.own 1) (openFd i (wal.walOpenFlag true ||| W64 0x80000)) ∗ trFile i True ∗
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj' ∗ walOutFrag (W := W) (o.addClaim (lendKey j bt)))

/-- **`Repair`'s open of the `.broken` file** (see the file header). -/
theorem repair_brokenOpen
    (wp_cNWF : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specFile (GF := GF) (hG := hG))
    (wp_OpenN : os.OpenFile.specCreateTruncSncN (GF := GF) (hG := hG))
    (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (dq : DFrac) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut)
    (bt : GoString) (hb : NameOk bt) (hbt : go!".wal.broken" <:+ bt)
    (hX : ∀ b ∈ X, ¬ go!".wal.broken" <:+ b) (hoD : (j, NameSet.except X) ∈ o.D)
    (hD : lendKey j bt ∉ o.D) :
    {{ walInv (W := W) C Mr R jr r ∗ osInv (GF := GF) ∗ osSharedInv R ∗ walDirKey (W := W) dir j X ∗
        osPathS R dir dq j ∗ osCallPerm (callKey R dir) 1 ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        walOutFrag (W := W) o }}
      (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
          [go.GoType.PointerType os.File.ty])) (Val #(child dir bt))) (Val #true))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R dir dq j ∗ osCallPerm (callKey R dir) 1 ∗
        ((⌜err = interface.nil⌝ ∗ repBrokenOk (W := W) dir bt j X o f) ∨ ⌜err ≠ interface.nil⌝) }} := by
  iintro %Φ ⟨#Hinv, #Hos, #Hsi, #Hk, Hp, Hperm, Hn, Ho⟩ HΦ
  have hw : walNameP bt = false := walNameP_broken hbt
  have hN : (NameSet.except X).Mem bt := fun h => hX bt h hbt
  rcases hcur : hj.cur !! bt with _ | n
  · -- absent: the create, over the update
    ihave Hn' : osNames j (.except X) (DFrac.own (qQuarter + qQuarter)) hj $$ [Hn]
    · rw [show qQuarter + qQuarter = (1 : Qp).half from Qp.half_add_half _]; iexact Hn
    icases (osNames_frac j (.except X) qQuarter qQuarter hj).1 $$ Hn' with ⟨Hn1, Hn2⟩
    ihave Hau := walBroken_osAUnc C Mr R jr r dir j X hj o bt hoD hbt $$ Hinv [Hn2 Ho]
    · unfold walBrokenP; iframe Hk Hn2 Ho
    wp_apply (wp_cNWF (child dir bt) true _ _ _ _
        (repBroken_tripleNew wp_OpenN R dir dq j X hj o bt 1 hb hN hcur)) $$ [Hp Hperm Hn1 Hau]
      as %f %err Hpo
    · iframe; iframe #
    iunfold fileutil.openPost at Hpo
    icases Hpo with ⟨%x, (⟨%he, HA, %fd, %i, ⟨%hfd, %hi⟩, Hf, Hoff, Hfd⟩ | ⟨⟨%he, -⟩, HA, -⟩)⟩
    · simp only [repBrokenNewA] at *
      icases HA with ⟨Hp, Hperm, HQ, Hc, Htr⟩
      rcases x with _ | ⟨x, s0, i'⟩
      · simp only [crIno] at hi; rw [hcur] at hi; cases hi
      simp only [crIno] at hi
      subst i
      simp only [walBrokenQ, crOutN, crTr] at *
      icases HQ with ⟨-, HQn, HQo⟩
      icases Hc with ⟨-, -, Hcn⟩
      iapply HΦ
      iframe Hp Hperm
      ileft
      isplitr
      · ipureintro; exact he
      unfold repBrokenOk
      iexists fd, i', (hj.log x (crEnt j bt i' s0) (<[bt := .file i']> hj.cur))
      iframe Hf Hoff Hfd HQo
      isplitr
      · ipureintro; exact ⟨hfd, GMap.lookup_insert _ _ _⟩
      isplitl [Htr]
      · iexact Htr
      ihave Hw := (osNames_frac j (.except X) qQuarter qQuarter _).2 $$ [HQn Hcn]
      · iframe
      rw [show qQuarter + qQuarter = (1 : Qp).half from Qp.half_add_half _]
      iexact Hw
    · simp only [repBrokenNewA] at *
      icases HA with ⟨Hp, Hperm, -⟩
      iapply HΦ
      iframe Hp Hperm
      iright; ipureintro; exact he
  · -- a leftover: lent, then the `O_TRUNC` open
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_lendOther C Mr R jr r ⊤ CoPset.subseteq_top dir j X hj (DFrac.own (1 : Qp).half) o bt n
        hw hD hcur $$ Hinv Hnc Hk Hn Ho with ⟨Hnc, Hn, Ho, Ht⟩
    imodintro
    iframe Hnc
    rcases n with i | dn
    rotate_left
    · simp only [tmpEnt]; icases Ht with ⟨⟩
    simp only [tmpEnt]
    wp_apply (wp_cNWF (child dir bt) true _ _ _ _
        (repBroken_tripleOld R dir dq (DFrac.own (1 : Qp).half) j X hj bt i 1 hb hN hcur))
      $$ [Hp Hperm Hn Ht] as %f %err Hpo
    · iframe; iframe #
    iunfold fileutil.openPost at Hpo
    icases Hpo with ⟨%x, (⟨%he, HA, %fd, %i', ⟨%hfd, %hi⟩, Hf, Hoff, Hfd⟩ | ⟨⟨%he, -⟩, HA, -⟩)⟩
    · simp only [repBrokenOldA] at *
      subst i'
      icases HA with ⟨Hp, Hn, Hperm, Htr⟩
      iapply HΦ
      iframe Hp Hperm
      ileft
      isplitr
      · ipureintro; exact he
      unfold repBrokenOk
      iexists fd, i, hj
      iframe Hf Hoff Hfd Ho Hn
      isplitr
      · ipureintro; exact ⟨hfd, hcur⟩
      iexact Htr
    · simp only [repBrokenOldA] at *
      icases HA with ⟨Hp, -, Hperm, -⟩
      iapply HΦ
      iframe Hp Hperm
      iright; ipureintro; exact he

end triples

end WalFs
end EtcdGrove
end Perennial

end
