/-
The proof of `Spec/go_etcd_io/bbolt/Open_sharedNoErr.lean` (session S3f): `Open`'s proof generic in the
environment's errors (`Open.wp_proofG`, `Open.lean`) at `Ek := False`:
- the callees' error arms witness `¬ FsNoErr` (`os.File.Stat.specW`, `flock.spec`, `DB.metasZero.spec_own`,
  `DB.init.spec`, `DB.getPageSize.spec_own`, `DB.mmapUnlocked.spec_own`, `fdatasync.specW`), which the
  premises refute (`FsNoErr` is them);
- the shared mode's open with no error (`os.OpenFile.specCreateSNoErr`, `openFileDbM_shared`), of a
  mappable file (`nameHoldsM`: `fileHoldsM_opened`, or the new file);
- the options' three fields (`optsAtNoErr`): half of the options' points-to is the witness `W`, which
  agrees with the fields `Open` reads (`Timeout` zero: no `ErrTimeout`; `NoFreelistSync`: no write
  transaction; `InitialMmapSize` at most `maxMapSize`: no "mmap too large", with the file's size).
-/
module

public import Spec.go_etcd_io.bbolt.Open_sharedNoErr
public import Spec.os.OpenFileSNoErr
public import Proof.go_etcd_io.bbolt.Open_shared
import all Proof.go_etcd_io.bbolt.Open_shared
public import Proof.go_etcd_io.bbolt.Open
import all Proof.go_etcd_io.bbolt.Open
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt
open Fs

/-- Half of a discardable fraction (`dfHalf dq • dfHalf dq = dq`). -/
private def dfHalf : DFrac → DFrac
  | .own q => .own q.half
  | .discard => .discard
  | .ownDiscard q => .ownDiscard q.half

private theorem dfHalf_op (dq : DFrac) : dfHalf dq • dfHalf dq = dq := by
  cases dq with
  | own q => show DFrac.own (q.half + q.half) = _; rw [Qp.half_add_half]
  | discard => rfl
  | ownDiscard q => show DFrac.ownDiscard (q.half + q.half) = _; rw [Qp.half_add_half]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]

/-- The name holds no directory. -/
private theorem nameHoldsM_notDir (h : NamesH) (b : GoString) (D : Data) :
    nameHoldsM (GF := GF) h b D ⊢ nameHoldsM h b D ∗ ⌜∀ J, h.cur !! b ≠ some (.dir J)⌝ := by
  unfold nameHoldsM
  iintro (⟨%i, %hi, H⟩ | %hn)
  · isplitl
    · ileft; iexists i; iframe H; ipureintro; exact hi
    · ipureintro; intro J hJ; rw [hi] at hJ; cases hJ
  · isplitl
    · iright; ipureintro; exact hn
    · ipureintro; intro J hJ; rw [hn.1] at hJ; cases hJ

/-- **The mappable file the open left at the name, opened**. -/
private theorem nameHoldsM_opened (j : Ino) (h : NamesH) (b : GoString) (D : Data)
    (o : Option (Nat × Nat × Ino)) (i : Ino) (hcr : crIno b h o i) :
    nameHoldsM (GF := GF) h b D ∗ crOut j b h (DFrac.own 1) o ∗ crMeta o ⊢
      crOut j b h (DFrac.own 1) o ∗ openedF i D (· ≤ 0xFFFFFFFFFFFF) := by
  unfold nameHoldsM
  cases o with
  | none =>
    dsimp only [crIno] at hcr
    dsimp only [crMeta]
    iintro ⟨(⟨%i0, %hi0, Hf⟩ | %hn), Ho, -⟩
    · rw [hcr] at hi0; cases hi0
      iframe Ho
      unfold fileHoldsM
      iapply fileHoldsM_opened $$ Hf
    · rw [hcr] at hn; exact absurd hn.1 (by simp)
  | some xsi =>
    obtain ⟨x, s, i1⟩ := xsi
    dsimp only [crIno] at hcr
    subst hcr
    dsimp only [crMeta, crOut]
    iintro ⟨(⟨%i0, %hi0, -⟩ | %hn), ⟨%hh, Hl, Hn⟩, Hm⟩
    · rw [hh.1] at hi0; cases hi0
    · obtain ⟨-, rfl⟩ := hn
      iframe Hl Hn
      isplitr
      · ipureintro; exact hh
      iapply new_opened _ (· ≤ 0xFFFFFFFFFFFF) (Nat.zero_le _) $$ Hm

/-- **The shared mode's open with no error** (`os.OpenFile.specCreateSNoErr`) as `openFileDb.spec` at
`Ek := False`, of a mappable file. -/
private theorem openFileDbM_shared (hCSN : os.OpenFile.specCreateSNoErr (GF := GF) (hG := hG))
    (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)] (hSp : ∀ p, Sio.path p)
    (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH) (perm : w32)
    (D : Data) (hb : NameOk b) :
    openFileDb.spec (GF := GF) (hG := hG) False (· ≤ 0xFFFFFFFFFFFF)
      iprop(osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ nameHoldsM h b D)
      (fun oc : Option (Nat × Nat × Ino) =>
        iprop(osPathS (GF := GF) R d dq j ∗ osCallPerm qc ∗ crOut j b h (DFrac.own 1) oc))
      (fun oc i => crIno b h oc i) (child d b) perm D := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hnh⟩ HΦ
  obtain ⟨hfl, hcr, htr⟩ := boltOpenFlag_create
  icases nameHoldsM_notDir h b D $$ Hnh with ⟨Hnh, %hnd⟩
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
    (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
  wp_apply hCSN Sio d b (W64 0x42) perm R j dq h (1 : Qp).half (1 : Qp).half qc
    (crOut j b h (DFrac.own (1 : Qp).half)) (hSp _) hfl hcr htr hb hnd (Qp.half_add_half 1)
    $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
    as %f %err ⟨Hp, Hperm, %oc, Ho1, Ho2, Hm, %fd, %i, %hres, Hf, -, Hfd⟩
  ihave Ho := os.crOut_join j b h oc $$ [$Ho1 $Ho2]
  iapply HΦ
  iexists oc
  dsimp only
  obtain ⟨rfl, hfd, hi⟩ := hres
  icases nameHoldsM_opened j h b D oc i hi $$ [$Hnh $Ho $Hm] with ⟨Ho, Hop⟩
  iframe Hp Hperm Ho
  isplitl [Hf Hfd Hop]
  · ileft
    iexists fd, i
    iframe Hf Hop
    isplitr
    · ipureintro; exact ⟨rfl, hfd, hi⟩
    have hofd : openFd i (W64 0x42 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := by
      have h1 : (W64 0x42 ||| W64 0x80000).toNat % 4 = 2 := by decide
      simp only [openFd, h1, O_WRONLY, O_RDONLY]; rfl
    rw [hofd] at *
    iexact Hfd
  · iapply fmtErrorOkOrNil_nil

private theorem pt_join_half (l : Loc) (v : go_etcd_io.bbolt.Options) (dq : DFrac) :
    (l ↦{dfHalf dq} v : IProp GF) ∗ l ↦{dfHalf dq} v ⊢ l ↦{dq} v := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional (dfHalf dq) (dfHalf dq)
  rw [dfHalf_op] at h
  exact h.2

private theorem optsAt_intro' (l : Loc) (dq : DFrac) (o : OptsM) (v : go_etcd_io.bbolt.Options)
    (h : optsVal v o) : (l ↦{dq} v : IProp GF) ⊢ optsAt l dq o := by
  unfold optsAt; iintro H; iexists v; iframe H; ipureintro; exact h

private theorem optsAt_elim' (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAt (GF := GF) l dq o ⊢ ∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v := by
  unfold optsAt; iintro ⟨%v, H, -⟩; iexists v; iexact H

private theorem optsAtNoErr_intro' (l : Loc) (dq : DFrac) (o : OptsM) (v : go_etcd_io.bbolt.Options)
    (h : optsVal v o ∧ optsNoErr v) : (l ↦{dq} v : IProp GF) ⊢ optsAtNoErr l dq o := by
  unfold optsAtNoErr; iintro H; iexists v; iframe H; ipureintro; exact h

private theorem optsAtNoErr_elim' (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAtNoErr (GF := GF) l dq o ⊢
      ∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o ∧ optsNoErr v⌝ := by
  unfold optsAtNoErr; exact .rfl

/-- The witness half of the options agrees with a field `Open` reads: `Timeout`. -/
private theorem optsW_timeout (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : time.Duration) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"Timeout"] ↦{dqx} x ⊢ ⌜False ∨ x = W64 0⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨H1, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H1 Hx
  ipureintro; right; rw [← h]; exact hv.1

private theorem optsW_nfs (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : Bool) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"NoFreelistSync"] ↦{dqx} x ⊢
      ⌜False ∨ x = true⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨-, -, H3, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H3 Hx
  ipureintro; right; rw [← h]; exact hv.2.1

private theorem optsW_mmap (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : w64) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"InitialMmapSize"] ↦{dqx} x ⊢
      ⌜False ∨ sint.Z x ≤ 0xFFFFFFFFFFFF⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨-, -, -, -, -, -, -, H8, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H8 Hx
  ipureintro; right; rw [← h]; exact hv.2.2

omit [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] in
set_option maxHeartbeats 4000000 in
theorem Open_sharedNoErr.wp_proof [sync.Assumptions]
    (hCSN : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      os.OpenFile.specCreateSNoErr (GF := GF) (hG := hG))
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hFlock : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], flock.spec (GF := GF) (hG := hG))
    (hStat : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], os.File.Stat.specW (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hMZ : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.metasZero.spec_own (GF := GF) (hG := hG))
    (hInit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.init.spec (GF := GF) (hG := hG))
    (hGPS : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.getPageSize.spec_own (GF := GF) (hG := hG))
    (hMmap : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.mmapUnlocked.spec_own (GF := GF) (hG := hG))
    (hLoad : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.loadFreelist.spec_open (GF := GF) (hG := hG))
    (hSync : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hFds : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], fdatasync.specW (GF := GF) (hG := hG))
    (hBegin : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.Begin_err.spec (GF := GF) (hG := hG))
    (hCommit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Tx.Commit_err.spec (GF := GF) (hG := hG))
    (hClose : DB.Close.spec (GF := GF) (hG := hG))
    (hclose : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.close.spec_owned (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOptStr : Options.String.spec (GF := GF) (hG := hG))
    (hModeStr : fs.FileMode.String.spec (GF := GF) (hG := hG)) :
    Open_sharedNoErr.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ _ Sio _ _ hSi hSp N R d b dq j qc h mode opts dqo o D hb
  have hne : FsNoErr := ⟨Sio, hSi, inferInstance, inferInstance⟩
  iintro %Φ ⟨#Hpkg, #Hos, %HN, #Hsi, Hp, Hperm, Hn, Hnh, Hopts, %Hok, Hlgr⟩ HΦ
  icases optsAtNoErr_elim' opts dqo o $$ Hopts with ⟨%v, Hv, %hv⟩
  icases ((typedPointsto_dfractional opts v).dfractional (dfHalf dqo) (dfHalf dqo)).1 $$ [Hv]
    with ⟨Hv1, Hv2⟩
  · rw [dfHalf_op]; iexact Hv
  iapply Open.wp_proofG hName hFlock hStat hSize hMZ hInit hGPS hMmap hLoad hSync hFds hBegin
    hCommit hClose hclose hLogger hOptStr hModeStr _ _ _ N (child d b) mode opts (dfHalf dqo) o D
    False (· ≤ 0xFFFFFFFFFFFF) (opts ↦{dfHalf dqo} v) (fun h => h hne) (fun _ hn => Or.inr hn)
    (optsW_timeout opts (dfHalf dqo) v hv.2) (optsW_nfs opts (dfHalf dqo) v hv.2)
    (optsW_mmap opts (dfHalf dqo) v hv.2)
    (openFileDbM_shared hCSN Sio hSp R d b dq j qc h mode D hb) $$ [Hp Hperm Hn Hnh Hv1 Hv2 Hlgr]
  · iframe; iframe #
    isplitr
    · ipureintro; exact HN
    isplitl [Hv1]
    · iapply optsAt_intro' opts (dfHalf dqo) o v hv.1 $$ Hv1
    ipureintro; exact Hok
  inext
  iintro %db %err ⟨Hopts, Hv2, %oc, ⟨Hp, Hperm, Ho⟩, Hr⟩
  icases Hr with (⟨%he, %γ, %i, %hg, Hb, Hino, Hst, Hcl⟩ | %hr)
  rotate_left
  · exact absurd hr.2 id
  icases optsAt_elim' opts (dfHalf dqo) o $$ Hopts with ⟨%v', Hv1⟩
  ihave %hvv := typedPointsto_agree_wand _ _ _ _ _ $$ Hv1 Hv2
  subst hvv
  iapply HΦ
  isplitr
  · ipureintro; exact he
  iframe Hp Hperm
  isplitl [Hv1 Hv2]
  · iapply optsAtNoErr_intro' opts dqo o v' hv
    iapply pt_join_half opts v' dqo $$ [Hv1 Hv2]
    iframe
  iexists oc, γ, i
  iframe Ho Hb Hino Hst Hcl
  ipureintro; exact hg

end proof

end bbolt
end EtcdGrove
end Perennial
