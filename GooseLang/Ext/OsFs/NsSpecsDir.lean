/-
WP specs of the namespace's operations over its whole history (`osNsAll`), for a program that
makes and moves directories (`examples/osfs/walfs`'s `dirswap.go`): the per-directory specs
(`NsSpecs2.lean`, `NsSpecs3.lean`) need their directory a directory in every prefix of the
history (`AllDir`), which a directory made since boot is not. Each takes the whole history `V`
(so no directory fd is open: `rdRes_whole`) and states its premises on the namespace now,
`nsReplay V.2 V.1`. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecs3
public import GooseLang.Ext.OsFs.NsMove

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The history with `o` logged. -/
abbrev nsPush (V : NsMap × List NsOp) (o : NsOp) : NsMap × List NsOp := (V.1, V.2 ++ [o])

/-- `d` is a directory of `m`, or a name in one: a path whose names (`child d b`) the namespace
manages, whatever `d` is now. -/
def NsBelowDir (m : NsMap) (d : GoString) : Prop :=
  m !! d = some .dir ∨ ∃ d0 b0, NameOk b0 ∧ d = child d0 b0 ∧ m !! d0 = some .dir

/-- A name the namespace manages: an `NsName`, no path of `files`. -/
theorem NsWf.below_facts {st : OsState} (hw : NsWf st) {d b : GoString}
    (hd : NsBelowDir st.ns d) (hb : NameOk b) : st.NsName (child d b) ∧ child d b ∉ st.files := by
  rcases hd with hd | ⟨d0, b0, hb0, rfl, hd0⟩
  · exact ⟨hw.nsName_child hd hb, hw.child_not_files hd hb⟩
  · obtain ⟨r, hr, hdr⟩ := hw.dir_form hd0
    have hc := canonBelow_child (.inr (canonBelow_child hdr hb0)) hb
    exact ⟨⟨r, hr, hc⟩, hw.not_files hr (.inr hc)⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `Regime(d/b)`, a name the namespace manages: `1`. -/
theorem wp_osRegimeG (d b : GoString) (hb : NameOk b) (dq : DFrac) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗
      (osNsAll (L := L) dq V -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv HV HΦ
  iapply wp_os_stepN "Regime" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hpf := (hw.below_facts (by rw [ns_eq_replay hw hc]; exact hd) hb).2
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨child d b, rfl, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, hst, rfl⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  imod osWorld_filesSame (filesSame_refl st) Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, _, Γdf
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  iframe
  isplitr
  · ipureintro; exact Hwc'
  isplitr
  · ipureintro; exact ⟨hw, hc⟩
  iapply wp_value'
  rw [if_neg hpf]
  iapply HΦ $$ HV

/-- `lstat`'s "is it a directory" of `d/b`, nothing there now: `0`. -/
theorem wp_osNsLstatDirG (d b : GoString) (hb : NameOk b) (dq : DFrac) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗
      (∀ e : w64, osNsAll (L := L) dq V -∗ Φ (PairV (#(0 : w64)) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsLstatDir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv HV HΦ
  iapply wp_os_stepN "NsLstatDir" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact hd
  have hnd' : st.ns !! child d b ≠ some .dir := by rw [ns_eq_replay hw hc, hn]; simp
  have hpath : st.NsPath (child d b) := .inr (hw.nsName_child hdir hb)
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨child d b, 0, 0, rfl, hpath, rfl, .inr rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', isDir, e, hv, -, hst, hres, rfl⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  have hd0 : isDir = 0 := by
    rcases hres with ⟨h1, -, -⟩ | h0
    · exact absurd h1 hnd'
    · exact h0
  subst hd0
  imod ns_step_close hwf hcoh (filesSame_refl st) Hr Hfr hw hc st.nsBusy rfl $$ HAb HAm HAf HAt
    Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, _, Γdf
  unfold osWorld nsWorld
  iframe Hw Hn
  iapply wp_value'
  iapply HΦ $$ %e HV

/-- `unlink(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: a file is removed (on a failure, removed or not); or it fails, unchanged. -/
theorem wp_osUnlinkG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(∃ k, nsReplay V.2 V.1 !! child d b = some (.file k)) ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "Unlink" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  icases rdRes_none _ Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hname := (hw.below_facts (by rw [ns_eq_replay hw hc]; exact hd) hb).1
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    exact ⟨_, h, st.nsFree, ⟨child d b, rfl, hname, hb1, .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, -, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  rcases hres with ⟨⟨k, hfile⟩, hr⟩ | ⟨e, he, rfl, rfl⟩
  · have hfileV := hfile
    rw [ns_eq_replay hw hc] at hfileV
    have hin := fileOpIn_remove hb hfile
    have hwe : NsWf (st.nsFree.nsDo (.remove (child d b))) :=
      nsWf_fileOp hw rfl rfl rfl rfl rfl rfl (fun k f h => ⟨f, h⟩) (fun k h => .inl h)
        (shape_remove hw.shape hfile)
        (fun p k' hp => by
          have hp' : (GMap.delete (child d b) st.ns) !! p = some (.file k') := hp
          by_cases hpe : child d b = p
          · subst hpe; rw [GMap.lookup_delete] at hp'; cases hp'
          · rw [GMap.lookup_delete_ne _ hpe] at hp'; exact hw.keys hp')
        hin.dir
    have hce : NsCoh (st.nsFree.nsDo (.remove (child d b))) (V.1, V.2 ++ [.remove (child d b)]) Γdf :=
      nsCoh_log hc Hnr rfl rfl rfl
    have hs1 : FilesSame st (st.nsFree.nsDo (.remove (child d b))) :=
      hs0.trans (filesSame_nsDo _ _)
    rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
    · imod osNsAll_update _ _ _ $$ HAd HV with ⟨HAd, HV⟩
      imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ
        HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
      imodintro
      iexists Γb, Γm, Γf, Γt, _, Γdf
      unfold osWorld nsWorld
      iframe Hw Hn
      iapply wp_value'
      iapply HΦ $$ %0 %_ %(.inl ⟨⟨k, hfileV⟩, .inl ⟨rfl, rfl⟩⟩) HV Hz
    · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb
        HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
      imodintro
      iexists Γb, Γm, Γf, Γt, _, Γdf
      unfold osWorld nsWorld
      iframe Hw Hn
      iapply wp_value'
      iapply HΦ $$ %e %_ %(.inl ⟨⟨k, hfileV⟩, .inr ⟨he, .inl rfl⟩⟩) HV Hz
    · imod osNsAll_update _ _ _ $$ HAd HV with ⟨HAd, HV⟩
      imod ns_step_close hwf hcoh hs1 Hr Hfr hwe hce false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ
        HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
      imodintro
      iexists Γb, Γm, Γf, Γt, _, Γdf
      unfold osWorld nsWorld
      iframe Hw Hn
      iapply wp_value'
      iapply HΦ $$ %e %_ %(.inl ⟨⟨k, hfileV⟩, .inr ⟨he, .inr rfl⟩⟩) HV Hz
  · imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, _, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %e %_ %(.inr ⟨he, rfl⟩) HV Hz

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/b`, nothing there now (`d` a directory now), with the
whole history and the in-flight flag set: the flag cleared; on success a new file under a fresh
key `k` and an fd on it; on failure the file may have been created. -/
theorem wp_osNsOpenCreateG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (L := L) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osNsAll (L := L) (DFrac.own 1) (nsPush V (.create (child d b) k)) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osNsAll (L := L) (DFrac.own 1) V ∨ ∃ k, ⌜IsInoKey k⌝ ∗
            osNsAll (L := L) (DFrac.own 1) (nsPush V (.create (child d b) k)) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HV Hz HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  icases rdRes_none _ Γdf $$ HV Hrd with ⟨%Hnr, HV, Hrd⟩
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact hd
  have hnone : st.ns !! child d b = none := by rw [ns_eq_replay hw hc]; exact hn
  have hcr : decide ((flCreat.toNat / O_CREAT) % 2 = 1) = true := by decide
  have htr : decide ((flCreat.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flCreat.toNat % 4 = 2 := by decide
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    refine ⟨_, h, st.nsFree, ⟨child d b, flCreat, rfl, .inr (hw.nsName_child hdir hb), flCreat_ok,
      fun _ => hb1, .inr ⟨1, by decide, rfl, .inl ?_⟩⟩, hfr, hr⟩
    simp only [hcr, ↓reduceIte]
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  simp only [hcr, htr, hacc, ↓reduceIte] at hres
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  -- what an effect is: a file created under a fresh key
  have heffect : ∀ st1 tgt, NsOpenEffect st.nsFree (child d b) 2 true false st1 tgt →
      ∃ k, IsInoKey k ∧ k ∉ st.files ∧ st1 = createdSt st d b k ∧ tgt = some k := by
    intro st1 tgt heff
    unfold NsOpenEffect at heff
    rw [show st.nsFree.ns = st.ns from rfl, hnone] at heff
    obtain ⟨-, -, -, k, hk, hkf, rfl, rfl⟩ := heff
    exact ⟨k, hk, hkf, rfl, rfl⟩
  -- the ghost state of a creation
  have hghost : ∀ k, IsInoKey k → k ∉ st.files →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap V) -∗
        osNsAll (L := L) (DFrac.own 1) V ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm (<[k := some newMeta]> Γm) ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd
          (histMap (V.1, V.2 ++ [.create (child d b) k])) ∗
        osNsAll (L := L) (DFrac.own 1) (nsPush V (.create (child d b) k)) ∗
        osMeta (L := L) k (DFrac.own 1) (some newMeta) := by
    intro k hk hkf
    obtain ⟨-, -, -, -, -, -, hΓm, -, -⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    iintro HAm HAd HV
    imod gAuth_insert _ _ _ k (some newMeta) hΓm $$ HAm with ⟨HAm, Hm⟩
    imod osNsAll_update _ (V.1, V.2 ++ [.create (child d b) k]) _ $$ HAd HV with ⟨HAd, HV⟩
    imodintro
    unfold osMeta
    iframe
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst | ⟨tgt, heff⟩⟩
  · -- success
    obtain ⟨k, hk, hkf, rfl, rfl⟩ := heffect st1 tgt heff
    obtain ⟨hwfB, hcohB, hcvB, hszB, hwB, hcB, -, hfkB, hbB⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hfdB : (createdSt st d b k).fds !! fd = none := hfdn
    have hst' : st' = { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } := by
      rw [hst]; simp [O_WRONLY, O_RDONLY]
    subst hst'
    imod hghost k hk hkf $$ HAm HAd HV with ⟨HAm, HAd, HV, Hm⟩
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn
    imod gAuth_insert _ _ _ fd (⟨k, true, true⟩ : OsFd) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hwf' := osWf_addFd hwfB fd ⟨k, true, true⟩ ⟨_, hfkB⟩
    have hcv : cellView { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } = cellView st :=
      (cellView_congr rfl rfl rfl).trans hcvB
    imod cells_same hwf hwf' Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    have htr' : tokRes (gooseOsGS (L := L)) { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γt =
        tokRes (gooseOsGS (L := L)) st Γt := create_tokRes _ Γt hszB
    have hw' : NsWf { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } := by
      refine ⟨hwB.roots, hwB.replay, hwB.hist, hwB.legacy, hwB.dfds, fun fd' h' => ?_⟩
      show (createdSt st d b k).dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he
        rw [show (createdSt st d b k).dfds = GMap.fmap (·.note (.create (child d b) k)) st.dfds
          from rfl, GMap.lookup_fmap, hdfn]; rfl
      · apply hwB.disj fd'
        have h'' : (<[fd := (⟨k, true, true⟩ : OsFd)]> (createdSt st d b k).fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    ihave Htok : tokRes (gooseOsGS (L := L)) { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γt $$ [Htok]
    · rw [htr']; iexact Htok
    have hcoh' : OsCoh { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γb (<[k := some newMeta]> Γm)
        (<[fd := ⟨k, true, true⟩]> Γf) Γt := by
      have : Γf = (createdSt st d b k).fds := by rw [hcoh.fds]; rfl
      rw [this]; exact osCoh_fds hcohB _
    ihave Hwn := worlds_fold ⟨hwf', hcoh'⟩ ⟨hw', hcB.congr rfl rfl rfl⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), (<[fd := ⟨k, true, true⟩]> Γf), Γt,
      (V.1, V.2 ++ [.create (child d b) k]), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 Hz
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    iexists k
    isplitr
    · ipureintro; exact hk
    unfold osMeta osFd
    iframe HV Hm
    iexact Hfd
  · -- failure, no effect
    subst hst
    imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, _, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e Hz
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    ileft; iexact HV
  · -- failure, created
    obtain ⟨k, hk, hkf, rfl, -⟩ := heffect st' tgt heff
    obtain ⟨hwfB, hcohB, hcvB, hszB, hwB, hcB, -, -, hbB⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    imod hghost k hk hkf $$ HAm HAd HV with ⟨HAm, HAd, HV, Hm⟩
    imod cells_same hwf hwfB Hr Hfr rfl hcvB $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    ihave Htok : tokRes (gooseOsGS (L := L)) (createdSt st d b k) Γt $$ [Htok]
    · rw [create_tokRes _ Γt hszB]; iexact Htok
    ihave Hwn := worlds_fold ⟨hwfB, hcohB⟩ ⟨hwB, hcB⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), Γf, Γt, (V.1, V.2 ++ [.create (child d b) k]), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e Hz
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    iright
    iexists k
    isplitr
    · ipureintro; exact hk
    unfold osMeta
    iframe

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/b`, the file of `k` now, with a fraction of `k`'s
`OsMeta` and the in-flight flag set (the retry of a create that made the file): an fd on `k`. -/
theorem wp_osNsOpenCreatExistingG (d b k : GoString) (hb : NameOk b) (dq : DFrac)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hf : nsReplay V.2 V.1 !! child d b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗ osMeta (L := L) k dqm mo -∗
      osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, ⌜mo ≠ none⌝ -∗ ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osNsAll (L := L) dq V -∗ osMeta (L := L) k dqm mo -∗ osNsBusy (L := L) false -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩ else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HV Hm Hz HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osMeta osNsBusy
  icases osNsAll_auth _ _ _ $$ HAd HV with %HVe
  subst HVe
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact hd
  have hfile : st.ns !! child d b = some (.file k) := by rw [ns_eq_replay hw hc]; exact hf
  obtain ⟨-, f, hkf⟩ := hw.keys hfile
  have hmo : mo ≠ none := by
    rintro rfl
    have := (hcoh.meta_none k).1 Hml; rw [hkf] at this; cases this
  have hfk : st.nsFree.file k = some f := file_eq_some.2 hkf
  have hcr : decide ((flCreat.toNat / O_CREAT) % 2 = 1) = true := by decide
  have htr : decide ((flCreat.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flCreat.toNat % 4 = 2 := by decide
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_nsFree st) Hag
    refine ⟨_, h, st.nsFree, ⟨child d b, flCreat, rfl, .inr (hw.nsName_child hdir hb), flCreat_ok,
      fun _ => hb1, .inr ⟨1, by decide, rfl, .inl ?_⟩⟩, hfr, hr⟩
    simp only [hcr, ↓reduceIte]
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold NsOpenEffect at heff
    rw [show st.nsFree.ns = st.ns from rfl, hfile] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hfdn' : st.fds !! fd = none := hfdn
    have hdfn' : st.dfds !! fd = none := hdfn
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn'
    imod gAuth_insert _ _ _ fd (⟨k, true, true⟩ : OsFd) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hst' : st' = { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } := by
      rw [hst]; simp [O_WRONLY, O_RDONLY]
    subst hst'
    have hwf0 := osWf_filesSame (filesSame_nsFree st) hwf
    have hcoh0 := osCoh_filesSame (filesSame_nsFree st) hcoh
    have hwf' := osWf_addFd hwf0 fd ⟨k, true, true⟩ ⟨f, hfk⟩
    have hcv : cellView { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } =
        cellView st := cellView_congr rfl rfl rfl
    imod cells_same hwf hwf' Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    have hw' : NsWf { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } := by
      refine ⟨hw.roots, hw.replay, hw.hist, hw.legacy, hw.dfds, fun fd' h' => ?_⟩
      show st.dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he; exact hdfn'
      · apply hw.disj fd'
        have h'' : (<[fd := (⟨k, true, true⟩ : OsFd)]> st.fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    have hcoh' : OsCoh { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γb Γm
        (<[fd := ⟨k, true, true⟩]> Γf) Γt := by
      have : Γf = st.nsFree.fds := by rw [hcoh.fds]; rfl
      rw [this]; exact osCoh_fds hcoh0 _
    ihave Htok : tokRes (gooseOsGS (L := L))
        { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γt $$ [Htok]
    · rw [show tokRes (gooseOsGS (L := L))
          { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γt =
          tokRes (gooseOsGS (L := L)) st Γt from rfl]
      iexact Htok
    ihave Hwn := worlds_fold ⟨hwf', hcoh'⟩ ⟨hw', hc.congr rfl rfl rfl⟩ false rfl
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, (<[fd := ⟨k, true, true⟩]> Γf), Γt, _, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %hmo %(.inl ⟨rfl, hfd0⟩) HV Hm Hz
    rw [if_pos rfl]; unfold osFd; iexact Hfd
  · have hst' : st' = st.nsFree := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold NsOpenEffect at heff; rw [show st.nsFree.ns = st.ns from rfl, hfile] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa using h1
    subst hst'
    imod ns_step_close hwf hcoh (filesSame_nsFree st) Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc)
      false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, _, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %hmo %(.inr ⟨he, rfl⟩) HV Hm Hz
    rw [if_neg he]; iempintro

end specs

end Perennial

end
