/- Lean-first (no Rocq counterpart). P1 (`BootP1.lean`) neither empties nor narrows the crashes
of a run beyond what it means to: from every reachable state (one satisfying `CacheOk`, which holds
from boot, after every step and after a crash: `GooseLang/Ext/Fs/Tests.lean`) with a machine crash,
the crash with the same tree that leaves every named file as of its last sync is a machine crash
satisfying P1 (`p1_crash_exists`), so the premise never makes `bootCrashSafety` vacuous; and a file
no change touched since its last sync satisfies P1's clause at every crash, whatever its bytes
(`p1_untouched`), so a file other than the database (holding a valid meta or not) never makes P1
fail. From the final review (`notes/axiom-review/fs-final.md`). Untrusted. -/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootP1
public import GooseLang.Ext.Fs.Tests

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs
namespace P1Sat

open Perennial.Fs Perennial.Fs.Tests
/-- Each file as of its last sync. -/
noncomputable def durFile (f : OsFile) : OsFile :=
  OsFile.ofDisk (fun b => valAt (f.cand b) 0) f.sizeLo

open Classical in
/-- The files of `durCrash`. -/
noncomputable def durFiles (st st' : OsState) : GMap Ino OsFile :=
  GMap.fmap durFile (GMap.filter (fun i _ => decide (Named st'.fs.treeDur i)) st.fs.files)

/-- `st'` with every named file replaced by its pre-crash file as of its last sync. -/
noncomputable def durCrash (st st' : OsState) : OsState :=
  ⟨⟨st'.fs.roots, st'.fs.treeDur, st'.fs.metaLog, st'.fs.committed, durFiles st st',
    st'.fs.nextIno, st'.fs.stamp⟩, st'.proc⟩

open Classical in
theorem durCrash_files (st st' : OsState) (i : Ino) :
    (durCrash st st').fs.files !! i =
      if Named st'.fs.treeDur i then (st.fs.files !! i).map durFile else none := by
  show ((st.fs.files.lookup i).filter _).map durFile = _
  by_cases h : Named st'.fs.treeDur i
  · rw [if_pos h]; cases st.fs.files.lookup i <;> simp [h] <;> rfl
  · rw [if_neg h]; cases st.fs.files.lookup i <;> simp [h]

theorem durCrash_machine {st st' : OsState} (hok : CacheOk st) (hc : MachineCrash st st') :
    MachineCrash st (durCrash st st') := by
  obtain ⟨hp, hr, hl, hcm, hn, hs, hS, hfiles⟩ := hc
  refine ⟨hp, hr, hl, hcm, hn, hs, hS, fun i => ⟨fun hN => ?_, fun hN => ?_⟩⟩
  · obtain ⟨f, f', hf, -, -⟩ := (hfiles i).1 hN
    have hcc := hok.1 i f hf
    refine ⟨f, durFile f, hf, (sectorWhole_durable st i f
      (Nat.le_trans hcc.2.1 hcc.2.2) hcc.1.2).1, ?_⟩
    simp only [durCrash] at hN
    rw [durCrash_files, if_pos hN, hf]; rfl
  · simp only [durCrash] at hN
    rw [durCrash_files, if_neg hN]

theorem durCrash_P1 [GooseExts] (st st' : OsState) : P1 st (durCrash st st') := by
  intro i f f' hf hf' j _ hsz _
  refine ⟨0, fun k _ => ?_⟩
  rw [durCrash_files, hf] at hf'
  split at hf'
  · simp only [Option.map_some, Option.some.injEq] at hf'
    subst hf'
    simp only [durFile, OsFile.ofDisk] at hsz ⊢
    rw [diskByte, if_pos]
    simp only [pageIn, decide_eq_true_eq]
    omega
  · cases hf'

/-- **P1 is never vacuous at a crash**: whenever the semantics has a crash from a reachable
state, it has one satisfying P1. -/
theorem p1_crash_exists [GooseExts] {st st' : OsState} (hok : CacheOk st)
    (hc : MachineCrash st st') : ∃ st'', OsCrash st st'' ∧ P1 st st'' :=
  ⟨durCrash st st', durCrash_machine hok hc, durCrash_P1 st st'⟩

/-- **A file nothing changed since its last sync satisfies P1's clause at every crash**, whatever
its bytes (a valid meta in another file of the roots' trees included): each byte has one candidate,
stamped 0, so every crash image is the file as of change 0. -/
theorem p1_untouched (st : OsState) (i : Ino) (f f' : OsFile) (v : Nat → w8)
    (hone : ∀ b, f.cand b = [(v b, 0)]) (hc : CrashFile st i f f') :
    ∀ j < 2, 4096 * j < f'.size →
      ∃ n, ∀ k < 64, f'.cache (4096 * j + 16 + k) = valAt (f.cand (4096 * j + 16 + k)) n := by
  intro j _ hsz
  obtain ⟨sz, img, -, himg, rfl⟩ := hc
  refine ⟨0, fun k _ => ?_⟩
  obtain ⟨s, hs⟩ := himg (4096 * j + 16 + k)
  rw [hone] at hs ⊢
  simp only [List.mem_singleton, Prod.mk.injEq] at hs
  simp only [OsFile.ofDisk] at hsz ⊢
  rw [diskByte, if_pos (by simp only [pageIn, decide_eq_true_eq]; omega), hs.1]
  simp [valAt]



end P1Sat
end osfs_bboltfs
end EtcdGrove
end Perennial

end
