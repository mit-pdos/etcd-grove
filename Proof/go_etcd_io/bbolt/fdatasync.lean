/-
The proof of `Spec/go_etcd_io/bbolt/fdatasync.lean`: U4 (`notes/bbolt-proof-plan.md`), over `os.File.Fd` and
`syscall.Fdatasync` (its byte-less `specB`: bbolt holds none of the file's bytes here), with `errnoErrOk` (`Mmap/Infra`: a failed sync's errno is `fmtErrorOk`).
-/
module

public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.os.CrashStILA
public import Proof.go_etcd_io.bbolt.Inv.BFileSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem fdatasync.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    fdatasync.spec (GF := GF) (hG := hG) := by
  intro db f fd p i m dqf dq
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hSync fd dq (dbFd i) m $$ [Hfd Hm] as %e ⟨Hfd, Hr⟩
  · iframe; iframe #
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  icases Hr with (⟨%he, %c, Hm⟩ | ⟨%he, Hm⟩)
  · subst he
    iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists m.bsynced c; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · ileft; ipureintro; simp [errnoErr]
  · iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists _; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · iright
      isplitr
      · ipureintro; simp only [errnoErr, he.1, ↓reduceIte]; exact fun h => nomatch h
      · iapply hErr e he.1 $$ Hsys

/-- `fdatasync.specC`'s proof: `os.File.Fd`, then `wp_bFdatasyncC` (the crash-mode sync whose
value moves to idle, `syscall.Fdatasync.specCrashILAR`). -/
theorem fdatasync.wp_proofC (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSA : syscall.Fdatasync.specCrashILAR (GF := GF) (hG := hG)) :
    fdatasync.specC (GF := GF) (hG := hG) := by
  intro db f fd p c C' C m o ys dqf dq hc hns ho hys
  wp_start as ⟨#Hos, #Hinv, Hf, Hfo, Hfd, Hm, Hys⟩
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply wp_bFdatasyncC hSA fd dq (dbFd p.ino) p c hc C' C m o ys rfl hns ho hys
    $$ [Hfd Hm Hys] as %e ⟨Hfd, %he, Hr⟩
  · iframe; iframe #
  subst he
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  iapply HΦ
  iframe Hf Hfd Hfo Hr
  ipureintro; simp [errnoErr]

/-- The slots `S`' ranges: each slot `s` at `4096 * s`, its bytes' values `g s`. -/
def slotRel (g : Nat → List w8) (s : Nat) (r : Nat × List ByteG) : Prop :=
  r.1 = 4096 * s ∧ r.2.map Prod.fst = g s

theorem slots_ranges (p : BFile) (g : Nat → List w8) : ∀ S : List Nat,
    ([∗list] s ∈ S, osSlot (GF := GF) p s (g s)) ⊢
      ∃ R : List (Nat × List ByteG), bRanges p R ∗ ⌜List.Forall₂ (slotRel g) S R⌝
  | [] => by
    iintro -
    iexists []
    isplitl
    · unfold bRanges; iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; exact List.Forall₂.nil
  | s :: S => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hs, H⟩
    iunfold osSlot at Hs
    icases Hs with ⟨%xs, Hxs, %hx⟩
    icases slots_ranges p g S $$ H with ⟨%R, HR, %hR⟩
    iexists (4096 * s, xs) :: R
    isplitl
    · unfold bRanges; iapply BigSepL.bigSepL_cons.2; iframe
    ipureintro; exact List.Forall₂.cons ⟨rfl, hx⟩ hR

theorem ranges_slots (p : BFile) (g : Nat → List w8) : ∀ (S : List Nat) (R : List (Nat × List ByteG)),
    List.Forall₂ (slotRel g) S R →
    bRanges (GF := GF) p R ⊢ [∗list] s ∈ S, osSlot (GF := GF) p s (g s)
  | [], [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: S, r :: R, List.Forall₂.cons h hR => by
    unfold bRanges
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hr, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr]
    · unfold osSlot; iexists r.2; rw [← h.1]; iframe; ipureintro; exact h.2
    iapply ranges_slots p g S R hR
    unfold bRanges; iexact H

theorem slotRel_same (g : Nat → List w8) : ∀ (S : List Nat) (R R' : List (Nat × List ByteG)),
    List.Forall₂ (slotRel g) S R → RSame R R' → List.Forall₂ (slotRel g) S R'
  | [], [], [], _, _ => List.Forall₂.nil
  | _ :: S, _ :: R, _ :: R', List.Forall₂.cons h hR, List.Forall₂.cons h' hR' =>
    List.Forall₂.cons ⟨h'.1.trans h.1, h'.2.trans h.2⟩ (slotRel_same g S R R' hR hR')

theorem slotRel_len {g : Nat → List w8} {s : Nat} {r : Nat × List ByteG} (h : slotRel g s r) :
    r.2.length = (g s).length := by
  rw [← h.2, List.length_map]

theorem slotRel_mem (g : Nat → List w8) : ∀ (S : List Nat) (R : List (Nat × List ByteG)),
    List.Forall₂ (slotRel g) S R → ∀ r ∈ R, ∃ s ∈ S, slotRel g s r
  | [], [], _, r, hr => by cases hr
  | s :: S, r0 :: R, List.Forall₂.cons h hR, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨s, List.mem_cons_self, h⟩
    · obtain ⟨s', hs', h'⟩ := slotRel_mem g S R hR r hr
      exact ⟨s', List.mem_cons_of_mem _ hs', h'⟩

theorem slotRel_memS (g : Nat → List w8) : ∀ (S : List Nat) (R : List (Nat × List ByteG)),
    List.Forall₂ (slotRel g) S R → ∀ s ∈ S, ∃ r ∈ R, slotRel g s r
  | [], [], _, s, hs => by cases hs
  | s0 :: S, r0 :: R, List.Forall₂.cons h hR, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨r0, List.mem_cons_self, h⟩
    · obtain ⟨r', hr', h'⟩ := slotRel_memS g S R hR s hs
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem slotRel_disj (g : Nat → List w8) :
    ∀ (S : List Nat) (R : List (Nat × List ByteG)), List.Forall₂ (slotRel g) S R → S.Nodup →
      (∀ s ∈ S, (g s).length ≤ 4096) → RDisj R
  | [], [], _, _, _ => List.Pairwise.nil
  | s :: S, r :: R, List.Forall₂.cons h hR, hnd, hg => by
    have hnd' := List.nodup_cons.1 hnd
    refine List.Pairwise.cons (fun r' hr' k hk hk' => ?_)
      (slotRel_disj g S R hR hnd'.2 (fun x hx => hg x (List.mem_cons_of_mem _ hx)))
    obtain ⟨s', hs', h'⟩ := slotRel_mem g S R hR r' hr'
    have hne : s ≠ s' := fun e => hnd'.1 (e ▸ hs')
    have l1 := slotRel_len h; have l2 := slotRel_len h'
    have g1 := hg s List.mem_cons_self; have g2 := hg s' (List.mem_cons_of_mem _ hs')
    unfold rIn at hk hk'
    rw [h.1] at hk; rw [h'.1] at hk'
    rcases Nat.lt_or_gt_of_ne hne with hl | hl <;> omega

/-- `fdatasync.specR`'s proof: `os.File.Fd`, then `wp_bFdatasync` with the slots as ranges. -/
theorem fdatasync.wp_proofR (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hSC : syscall.Fdatasync.specCrashILR (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    fdatasync.specR (GF := GF) (hG := hG) := by
  intro db f fd p C L m S g dqf dq hns hcr
  wp_start as ⟨#Hos, #Hinv, Hf, Hfo, Hfd, Hm, HS⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  icases slots_ranges p g S $$ HS with ⟨%R, HR, %hR⟩
  wp_apply wp_bFdatasync hSync hSC fd dq (dbFd p.ino) p C L m R rfl hns
    (fun h k hr hks => by
      obtain ⟨hnd, hsl, hcov⟩ := hcr h
      obtain ⟨r0, hr0, k1, k2⟩ := hr
      have hs := hcov r0 hr0 k k1 k2 hks
      obtain ⟨r', hr', hrel⟩ := slotRel_memS g S R hR _ hs
      refine ⟨r', hr', ?_⟩
      have := slotRel_len hrel; rw [(hsl _ hs).1] at this
      unfold rIn; rw [hrel.1, this]; omega)
    (fun h => slotRel_disj g S R hR (hcr h).1
      (fun s hs => Nat.le_of_eq ((hcr h).2.1 s hs).1))
    (fun h r hr => by
      obtain ⟨s, hs, hrel⟩ := slotRel_mem g S R hR r hr
      have := slotRel_len hrel; rw [((hcr h).2.1 s hs).1] at this
      have h2 := ((hcr h).2.1 s hs).2
      rw [hrel.1, this]; omega)
    $$ [Hfd Hm HR] as %e ⟨Hfd, Hr⟩
  · iframe; iframe #
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  icases Hr with (⟨%he, %m', %R', Hm, HR, %Hm'⟩ | ⟨%he, Hm, HR⟩)
  · subst he
    iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [HR]
    · iapply ranges_slots p g S R' (slotRel_same g S R R' hR Hm'.2.2.1) $$ HR
    ileft
    isplitr
    · ipureintro; simp [errnoErr]
    iexists m'; iframe; ipureintro; exact ⟨Hm'.1, Hm'.2.1, Hm'.2.2.2⟩
  · iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [HR]
    · iapply ranges_slots p g S R hR $$ HR
    iright
    isplitr
    · ipureintro
      refine ⟨?_, he.2⟩
      simp only [errnoErr, he.1, ↓reduceIte]; exact fun h => nomatch h
    isplitr
    · iapply hErr e he.1 $$ Hsys
    iexact Hm

end proof

end bbolt
end EtcdGrove
end Perennial
