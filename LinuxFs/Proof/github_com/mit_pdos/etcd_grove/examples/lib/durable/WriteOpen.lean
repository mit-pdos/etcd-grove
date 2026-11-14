/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: `tryWrite`'s open of the temporary (W4c U2, `notes/wal-fsext-w4c-plan.md`)

`durTmpOpen`: `os.OpenFile(tmp, O_RDWR|O_CREATE|O_TRUNC, perm)` with the handle's parts. If the
temporary's name holds nothing, the create (`os.OpenFile.specCreateTruncSnc`, the update
`durCreate_osAUnc` on the invariant's half of its claim); if a file (a failed attempt's, the handle
holds it whole), the truncation (`os.OpenFile.wp_truncS`); never a directory (`DurOk.tmp`). After it
the temporary's claim is at some history `ht'` (the physical state's), and either the open failed
(the temporary's file, if any, held as before, `tmpRes`) or it holds the file `i`, opened, empty and
held whole (`trFile i True`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.WriteInv
public import LinuxFs.Proof.os.OpenFileTruncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DurFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem DurFs.tmpRes_file (f : DFile) (ht : NamesH) (i : Ino) (hx : ht.cur !! f.tb = some (.file i)) :
    tmpRes (GF := GF) f ht ⊣⊢ trFile i False := by
  unfold tmpRes; rw [hx]; exact .rfl

theorem DurFs.tmpRes_none (f : DFile) (ht : NamesH) (hx : ht.cur !! f.tb = none) :
    tmpRes (GF := GF) f ht ⊣⊢ emp := by
  unfold tmpRes; rw [hx]; exact .rfl

/-- See the file header. -/
theorem DurFs.durTmpOpen (wp_OpenCT : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG))
    (γ : DurGS) (f : DFile) (R : Roots) (qc qd : Qp) (p : DurPhys) (s : DurSt) (flag : w64)
    (perm : w32) (hf : f.Ok) (hok : DurOk f s p)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (hcr : (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 1) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ durInv γ f ∗ durPhys γ p ∗
        osNames f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) p.ht ∗ tmpRes f p.ht ∗
        osPathS R f.d (DFrac.own qd) f.J ∗ osCallPerm qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #f.tmp)) (Val #flag)) (Val #perm))
    {{ (fl : Loc) (err : GoInterface), RET (PairV #fl #err); osPathS R f.d (DFrac.own qd) f.J ∗
        osCallPerm qc ∗
        ∃ ht' : NamesH, durPhys γ { p with ht := ht' } ∗
          osNames f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) ht' ∗
          ((⌜err ≠ interface.nil⌝ ∗ tmpRes f ht') ∨
           (∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ ht'.cur !! f.tb = some (.file i)⌝ ∗
              trFile i True ∗ os.ownFile fl fd f.tmp (DFrac.own 1) ∗ os.ownOff fl (W64 0) ∗
              osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000)))) }} := by
  iintro %Φ ⟨#Hinv, #Hsi, #Hdi, Hp, Hnt, Htmp, Hpath, Hperm⟩ HΦ
  have hNt : (NameSet.only [f.tb]).Mem f.tb := by simp [NameSet.Mem]
  have htbn : NameOk f.tb := hf.2.2.2.2.1
  unfold DFile.tmp
  cases hx : p.ht.cur !! f.tb with
  | none =>
    ihave Hau := durCreate_osAUnc γ f p $$ Hdi Hp
    wp_apply wp_OpenCT f.d f.tb flag perm R f.J (DFrac.own qd) p.ht (1 : Qp).half (1 : Qp).half qc _
      hfl hcr htr htbn hx (Qp.half_add_half 1) $$ [Hinv Hsi Hpath Hperm Hnt Hau]
      as %fl %err ⟨Hpath, Hperm, %o, Hq, Hcr, Htr, Hres⟩
    · iframe; iframe #
    iapply HΦ
    iframe Hpath Hperm
    iexists (crHt f p.ht o)
    iframe Hq
    isplitl [Hcr]
    · rcases o with _ | ⟨x, s1, i⟩
      · simp only [crOut, crHt]; iexact Hcr
      · simp only [crOut, crHt]; icases Hcr with ⟨-, -, H⟩; iexact H
    icases Hres with (⟨%fd, %i, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, -⟩)
    · obtain ⟨he, -, hci⟩ := hres
      rcases o with _ | ⟨x, s1, i'⟩
      · simp only [crIno] at hci; rw [hx] at hci; cases hci
      · simp only [crIno] at hci; subst hci
        iright
        iexists fd, i
        simp only [crTr]
        iframe Hf Hoff Hfd
        isplitr
        · ipureintro; exact ⟨he, by simp [crHt, NamesH.log]⟩
        iapply trFile_mono i (err = interface.nil) True (fun _ => he) $$ Htr
    · ileft
      isplitr
      · ipureintro; exact herr.1
      rcases o with _ | ⟨x, s1, i'⟩
      · simp only [crHt]; iexact Htmp
      · simp only [crTr]
        iapply (tmpRes_file f _ i' (by simp [crHt, NamesH.log])).2
        iapply trFile_mono i' (err = interface.nil) False (fun h => h.elim) $$ Htr
  | some n =>
    cases n with
    | dir J => exact absurd hx (hok.tmp J)
    | file i =>
      icases (tmpRes_file f p.ht i hx).1 $$ Htmp with Htmp
      wp_apply os.OpenFile.wp_truncS f.d f.tb flag perm R f.J i (.only [f.tb]) (DFrac.own qd)
        (DFrac.own (1 : Qp).half) p.ht qc hfl htr htbn hNt hx $$ [Hinv Hsi Hpath Hnt Hperm Htmp]
        as %fl %err ⟨Hpath, Hnt, Hperm, Htr, Hres⟩
      · iframe; iframe #
      iapply HΦ
      iframe Hpath Hperm
      iexists p.ht
      iframe Hp Hnt
      icases Hres with (⟨%fd, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, -⟩)
      · iright
        iexists fd, i
        iframe Hf Hoff Hfd
        isplitr
        · ipureintro; exact ⟨hres.1, hx⟩
        iapply trFile_mono i (err = interface.nil) True (fun _ => hres.1) $$ Htr
      · ileft
        isplitr
        · ipureintro; exact herr.1
        iapply (tmpRes_file f p.ht i hx).2
        iapply trFile_mono i (err = interface.nil) False (fun h => h.elim) $$ Htr

end proof

end EtcdGrove
end Perennial
