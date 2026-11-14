/-
WP specs of the Linux file extension's `fallocate` (`FallocStart`, `FallocFinish` for mode 0, a
truncate to `max size (off + len)`; `FallocKeep` for `FALLOC_FL_KEEP_SIZE`, no visible change) and
of the OFD lock (`OfdLock`, trivial), as `Truncate.lean`'s and `wp_osFlock`.
-/
module

public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- `fcntl(fd, F_OFD_SETLK[W], ...)`: any errno, nothing changed (the lock state is not
modelled). -/
theorem wp_osOfdLock (fd cmd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (#cmd)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "OfdLock" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, cmd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', cmd', e, d', hv, -, rfl, rfl⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: any errno, no visible change. -/
theorem wp_osFallocKeep (fd off len : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocKeep" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "FallocKeep" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, len, 0, d, rfl, hfd, hwr, hoff, hlen, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', off', len', e, d', hv, -, -, -, -, rfl, rfl⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- The first step of `fallocate(fd, 0, off, len)`, a resize to `max size (off + len)` in flight
(`wp_osResizeStart`, nothing cut off). -/
theorem wp_osFallocStart (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      mcellsAny m.maps m.size (max m.size (off.toNat + len.toNat)) -∗
      (∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗
        rsTok false t d.ino (max m.size (off.toNat + len.toNat)) m [] n -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FallocStart" (Val (PairV (#fd) (PairV (#off) (#len))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hc HΦ
  have hmin : min m.size (max m.size (off.toNat + len.toNat)) = m.size := by omega
  have hmax : rsHi false m.size (max m.size (off.toNat + len.toNat)) =
      max m.size (off.toNat + len.toNat) := by
    show max m.size (max m.size (off.toNat + len.toNat)) = _; omega
  iapply wp_osResizeStart "FallocStart" _ (by simp [DataOp]) (by simp [val.isPanic]) false fd
    (max m.size (off.toNat + len.toNat)) dq d m [] hE
    (fun st f t hfd hf hnb ht hc hsz => by
      simp only [IsFsStep]
      refine ⟨fd, off, len, t, d, f, rfl, hfd, hwr, hoff, hlen, hnb, hf, ht, hc, ?_, rfl⟩
      rw [hsz])
    (fun st e' st' hfd hsz hst => by
      simp only [IsFsStep] at hst
      obtain ⟨fd', off', len', t, d', f, hv, hfd', -, -, -, -, hf, ht, -, hst', rfl⟩ := hst
      injection hv with h1 h2; injection h2 with h3 h4
      cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
      simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
      refine ⟨f, t, hf, ht, rfl, ?_⟩
      rw [hst', hsz f hf])
    (by simp; omega) Φ $$ Hinv Hfd Hm [] [Hc]
  · rw [hmin]; unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  · rw [hmin, hmax]; iexact Hc
  · iintro %t %n - Hfd Ht
    iapply HΦ $$ Hfd Ht

/-- The second step of `fallocate`'s growth; if `keep` (a file with no sync cut), the `OsMeta` it
lands with knows the candidates of the bytes it announced past the new size (`rsPostK`: a partial
growth's). -/
theorem wp_osFallocFinishK (keep : Bool) (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (n : Nat)
    (hgrow : m.size ≤ tg) (hkeep : keep = true → m.cut = none) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ rsTok (L := L) false t p tg m [] n -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ rsDoneK (L := L) keep false p tg tg m [] n) ∨
         (⌜e ≠ 0⌝ ∗ (rsUndone (L := L) false p tg m [] n ∨
           ∃ w, ⌜m.size ≤ w ∧ w ≤ tg⌝ ∗ rsDoneK (L := L) keep false p tg w m [] n))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_os_step "FallocFinish" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold rsTok osTok
  icases Ht with ⟨Ht, %hxl⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  obtain ⟨c, f, hF⟩ := rsFacts_of hcoh Hti hxl
  have hcp := hF.hcino
  subst hcp
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have Hh : ∀ l, Mapped st l → (h !! l).isSome := by
    intro l hm
    obtain ⟨x, hx⟩ := cellView_isSome hwf hm
    obtain ⟨m0, hm0⟩ := Hag l x hx
    rw [hm0]; rfl
  have hchi' : c.hi = tg := by rw [hF.hchi]; show max m.size tg = tg; omega
  have hwf1 : c.target ≤ maxBytes → OsWf ((st.doneInflight t).setFile c.ino (f.land c c.hi c.target)) :=
    fun htm => osWf_setFile' (osWf_done (t := t) hwf) hF.hf
      (by have := hwf.sizes c.ino f hF.hf; simp only [OsFile.land]; omega)
      (fun b p0 hp0 => hwf.stamps c.ino f b p0 hF.hf hp0)
  have hland' : (max m.size tg ≤ c.hi ∧ c.hi = rsHi false m.size tg ∧ tg = tg) ∨
      (m.size ≤ tg ∧ m.size ≤ c.hi ∧ c.hi ≤ tg ∧ tg = c.hi) :=
    .inr ⟨hgrow, by omega, by omega, by omega⟩
  imodintro
  isplitr
  · ipureintro
    by_cases htm : c.target ≤ maxBytes
    · exact ⟨_, renderHeap ((st.doneInflight t).setFile c.ino (f.land c c.hi c.target)) h, _,
        ⟨t, c, tg, f, rfl, hF.hct, hF.hckind, hF.hf, .inl ⟨htm, rfl, rfl⟩⟩,
        mapsFresh_same rfl, heapRendered_render (hwf1 htm) rfl Hh⟩
    · exact ⟨_, renderHeap (st.doneInflight t) h, _,
        ⟨t, c, tg, f, rfl, hF.hct, hF.hckind, hF.hf, .inr ⟨27, by decide, rfl, .inl rfl⟩⟩,
        mapsFresh_same rfl, heapRendered_render (osWf_done hwf) rfl Hh⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨t', c', tg', f', hv, hinfl, hkind', hf', hres⟩ := Hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hF.hct, Option.some.injEq] at hinfl; subst hinfl
  rw [hF.hckind] at hkind'; simp only [rsKind, Bool.false_eq_true, if_false] at hkind'
  injection hkind' with ho; subst ho
  rw [hF.hf, Option.some.injEq] at hf'; subst hf'
  rcases hres with ⟨htm, rfl, rfl⟩ | ⟨e, he, rfl, rfl | ⟨htm, w, hw1, hw2, rfl⟩⟩
  · rw [hF.hctg] at Hr Hfr htm ⊢
    imod resize_done_worldK keep hwf hcoh hF c.hi tg hland' (fun h => by cases h) (fun _ => hgrow) hkeep htm Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; ileft; iframe; ipureintro; rfl
  · imod resize_undone_world hwf hcoh hF Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; iright; isplitr
    · ipureintro; exact he
    ileft; iexact Hd
  · have hlw : (max m.size tg ≤ w ∧ w = rsHi false m.size tg ∧ w = tg) ∨
        (m.size ≤ tg ∧ m.size ≤ w ∧ w ≤ tg ∧ w = w) := by
      rw [hF.hclo] at hw1; rw [hchi'] at hw2; right; omega
    imod resize_done_worldK keep hwf hcoh hF w w hlw (fun h => by cases h) (fun _ => hgrow) hkeep
      (by rw [hchi'] at hw2; rw [hF.hctg] at htm; omega) Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Ht
      with ⟨⟨%Γb', %Γm', %Γf', %Γt', Hw⟩, Hd⟩
    imodintro
    iexists Γb', Γm', Γf', Γt'
    isplitl [Hw]
    · iapply (osWorld_unfold (L := L)).1 $$ Hw
    iapply wp_value'
    iapply HΦ; iright; isplitr
    · ipureintro; exact he
    iright; iexists w; iframe; ipureintro
    rw [hF.hclo] at hw1; rw [hchi'] at hw2; omega
/-- The second step of `fallocate`'s growth (`wp_osFallocFinishK` without the candidates past the
new size). -/
theorem wp_osFallocFinish (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (n : Nat) (hgrow : m.size ≤ tg)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ rsTok (L := L) false t p tg m [] n -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ rsDone (L := L) false p tg tg m n) ∨
         (⌜e ≠ 0⌝ ∗ (rsUndone (L := L) false p tg m [] n ∨
           ∃ w, ⌜m.size ≤ w ∧ w ≤ tg⌝ ∗ rsDone (L := L) false p tg w m n))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  simp only [← rsDoneK_false (xs := [])]
  exact wp_osFallocFinishK false t p tg m n hgrow (fun h => by cases h) hE Φ
end specs

end Fs
end Perennial

end
