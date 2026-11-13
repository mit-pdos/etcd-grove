/- Lean-first (no Rocq counterpart).

# What a cut adds to the WAL invariant (`notes/wal-fsext-plan.md`, W2; "W2 implementation log")

Pure. `(*WAL).cut` (S/wal.go:875-965) truncates and syncs the old tail, takes a fresh `N.tmp` from
the file pipeline (`O_TRUNC`, preallocated: zeros), writes the new segment's headers into it and
fdatasyncs it, renames it to the segment's name, then fsyncs the WAL directory. The invariant
(`Inv.lean`'s `WalsOk`) gains three things for it, each its own definition so the W1 lemmas are
unchanged where they do not meet them:

* **The pipeline's names are not the WAL's** (`WalDirClaim`): the invariant's claim on a WAL
  directory is on all names but a list `X` of non-`.wal` names (`walTmps`, the pipeline's
  `0.tmp`/`1.tmp`, whose claims the pipeline holds); the `.wal` names, all the crash condition
  reads, are the WAL's. The claim's history is coherent (`ClaimCoh`: its entries in index order,
  and a crash keeping all of them leaves its names as they are now), which a cut's rename keeps
  (`claimCoh_log`).
* **A cut's rename not yet made durable** (`CrashOkW`): between the rename of `N.tmp` to the new
  segment's name and the directory's fsync, a crash may keep or drop the rename. The invariant
  then holds the new layout (`cutLay`, the static relation over the directory's names now) and
  the old one as an alternative (`AltOk`: its own static relation, a prefix of the new segments);
  the crash condition (`CrashOkA`) gives `CrashTo` of either. Before the rename and after the
  directory's fsync the alternative is `none`, and `CrashOkA` is `CrashOk` (`crashOkW_iff`).
* **The new segment** (`cutLay`): the cut position `|H|` appended to the cuts, the segment (its
  bytes the headers' frames and zeros, all durable after the fdatasync) appended to the segments,
  the bytes under its stream zeros (`O_TRUNC` and the preallocation), its stream synced.

The intermediate states a cut goes through, as the invariant allows them (`WalsOk`): (1) the old
tail truncated (its `OsMeta`'s size cut, not yet synced: W6's tail step, `CrashOk` unchanged since
the reader stops at the stream's end with or without the zeros past it); (2) the old tail synced
(`d.m = |H|`, every byte of every segment durable); (3) `N.tmp` holding zeros, then headers, then
synced: not a `.wal` name, owned by the cut alone, so no invariant fact; (4) renamed, not yet
dir-synced: `CrashOkW` with the alternative (`crashOkA_rename`, `CutCrash.lean`); (5) dir-synced:
the alternative dropped (`crashOk_of_alt`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section cut
variable [GooseExts]

/-! ## The pipeline's names -/

/-- The file pipeline's names (`fmt.Sprintf("%d.tmp", fp.count%2)`, file_pipeline.go:77). -/
def walTmps : List GoString := [go!"0.tmp", go!"1.tmp"]

theorem walTmps_not_wal : ∀ b ∈ walTmps, walNameP b = false := by
  intro b hb
  simp only [walTmps, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl <;> decide

/-! ## A claim's coherence -/

/-- **A claim's history is coherent**: its entries are below `next` (logged in index order), and a
crash keeping all of them leaves each of its names as it is now. (True of every claim the shared
invariant hands out, `namesOf`; the WAL keeps it for its directory's claim by `coh_log`.) -/
def ClaimCoh (h : NamesH) (j : Ino) (N : NameSet) : Prop :=
  (∀ xe ∈ h.ents, xe.1 < h.next) ∧
  ∀ K : Nat → Prop, (∀ xe ∈ h.ents, K xe.1) → ∀ b, N.Mem b → h.valAfter j K b = h.cur !! b

/-- A claim with nothing logged, its names at boot as now, is coherent. -/
theorem claimCoh_init (h : NamesH) (j : Ino) (N : NameSet) (he : h.ents = [])
    (hb : ∀ b, N.Mem b → h.boot !! b = h.cur !! b) : ClaimCoh h j N := by
  refine ⟨by simp [he], fun K _ b hbN => ?_⟩
  unfold NamesH.valAfter
  rw [he]
  exact hb b hbN

/-- **Logging an entry keeps a claim coherent**, the entry's index at least the claim's `next`, the
names it does not write unchanged. -/
theorem claimCoh_log (h : NamesH) (j : Ino) (N : NameSet) (x : Nat) (e : LogEntry) (c : Ents)
    (hc : ClaimCoh h j N) (hx : h.next ≤ x)
    (hw : ∀ b, N.Mem b → ¬ e.op.Writes j b → c !! b = h.cur !! b) : ClaimCoh (h.log x e c) j N := by
  classical
  have hnext : (h.log x e c).next = x + 1 := by simp [NamesH.next, NamesH.log]
  refine ⟨fun xe hxe => ?_, fun K hK b hbN => ?_⟩
  · rw [hnext]
    simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
    rcases hxe with hxe | rfl
    · have := hc.1 xe hxe; omega
    · simp
  · have hKx : K x := hK (x, e, c) (by simp [NamesH.log])
    have hKo : ∀ xe ∈ h.ents, K xe.1 := fun xe hxe => hK xe (by simp [NamesH.log, hxe])
    unfold NamesH.valAfter NamesH.log
    simp only [List.filter_append, List.filter_cons, List.filter_nil]
    by_cases hwb : e.op.Writes j b
    · rw [if_pos (by simp [hKx, hwb])]; simp
    · rw [if_neg (by simp [hwb])]
      simp only [List.append_nil]
      have := hc.2 K hKo b hbN
      unfold NamesH.valAfter at this
      rw [this, hw b hbN hwb]

/-- **The WAL directory's claim** in the claims `cl`: on all names but `X` (names of no `.wal` file:
the pipeline's), coherent. -/
def WalDirClaim (j : Ino) (h : NamesH) (cl : List Claim) : Prop :=
  ∃ X : List GoString, (∀ b ∈ X, walNameP b = false) ∧ (j, NameSet.except X, h) ∈ cl ∧
    ClaimCoh h j (.except X)

/-! ## The crash condition with a pending rename -/

/-- **The layout before a cut's rename** (`lay0`), an alternative to `lay` while the rename may not
survive a crash: its own static relation (over the directory's names before the rename), the same
WAL directory, its segments a strict prefix of `lay`'s (so it never holds `lay`'s tail; W6's
decision of 2026-11-13). -/
def AltOk (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay lay0 : WalLay) : Prop :=
  (∃ ents0, WalAbsD C Mr d lay0 ents0) ∧ lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j ∧
    lay0.segs <+: lay.segs ∧ lay0.segs.length < lay.segs.length

/-- **The crash condition, with an alternative layout** (`CrashOk` when `alt = none`): every crash
the claims and `lay`'s halves allow leaves `CrashTo` of `lay` or of the alternative. -/
def CrashOkA (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (alt : Option WalLay)
    (cl : List Claim) (n : Nat) : Prop :=
  ∀ (m' : Tree) (fo : Ino → Option Fs.OsFile), RegionCrashed cl n m' →
    (∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino)) →
    (∀ g ∈ lay.segs, Named m' g.ino → (fo g.ino).isSome) →
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay) →
    CrashTo C Mr d lay m' fo ∨ ∃ lay0, alt = some lay0 ∧ CrashTo C Mr d lay0 m' fo

/-- **What the invariant says of a WAL's crashes**: the crash condition, with an alternative layout
(a cut's rename pending) or none. -/
def CrashOkW (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (cl : List Claim)
    (n : Nat) : Prop :=
  ∃ alt : Option WalLay, (∀ lay0, alt = some lay0 → AltOk C Mr d lay lay0) ∧
    CrashOkA C Mr d lay alt cl n

theorem crashOkA_none_iff (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay)
    (cl : List Claim) (n : Nat) : CrashOkA C Mr d lay none cl n ↔ CrashOk C Mr d lay cl n := by
  constructor
  · intro h m' fo hr hf hn hw
    rcases h m' fo hr hf hn hw with h | ⟨_, h, _⟩
    · exact h
    · cases h
  · intro h m' fo hr hf hn hw
    exact Or.inl (h m' fo hr hf hn hw)

theorem crashOkW_of_crashOk {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} (h : CrashOk C Mr d lay cl n) : CrashOkW C Mr d lay cl n :=
  ⟨none, fun _ h0 => absurd h0 (by simp), (crashOkA_none_iff C Mr d lay cl n).2 h⟩

/-- **The rename made durable drops the alternative**: if every crash the claims allow, the WAL
directory at its name, names a segment of `lay` that the alternative does not have (the new
segment, the rename kept), then the alternative's `CrashTo` cannot hold but by the WAL's absence,
which is `lay`'s too. -/
theorem crashOk_of_alt (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay lay0 : WalLay)
    (cl : List Claim) (n : Nat) (halt : AltOk C Mr d lay lay0)
    (hok : CrashOkA C Mr d lay (some lay0) cl n) (i : Ino) (hi : i ∉ lay0.segs.map (·.ino))
    (hkept : ∀ m', RegionCrashed cl n m' → m'.entry lay.jr lay.nm = some (.dir lay.j) →
      i ∈ walInos (entsOf m' lay.j)) :
    CrashOk C Mr d lay cl n := by
  intro m' fo hr hf hn hw
  rcases hok m' fo hr hf hn hw with h | ⟨l0, hl0, h⟩
  · exact h
  cases hl0
  obtain ⟨-, hjr, hnm, hj, -⟩ := halt
  rcases h with ⟨hnamed, hab⟩ | ⟨q, I, hent, -, hinos, -⟩
  · exact Or.inl ⟨hnamed, by rw [← hjr, ← hnm]; exact hab⟩
  · exfalso
    rw [hjr, hnm, hj] at hent
    have := hkept m' hr hent
    rw [← hj, hinos] at this
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 this
    exact hi (List.mem_map_of_mem (List.mem_of_mem_drop hg))

/-! ## The layout after a cut -/

/-- **The layout after a cut's rename**: the cut at `b` (`|H|`) and the new segment `g` appended; the
bytes under its stream zeros; its stream (the headers' frames, `wr` bytes) written and synced. -/
def cutLay (lay : WalLay) (b : Nat) (g : SegG) (wr : Nat) : WalLay :=
  { lay with
    cuts := lay.cuts ++ [b]
    segs := lay.segs ++ [g]
    old := List.replicate g.bs.length 0
    wr := wr
    so := wr
    z0 := 0 }

end cut

end WalFs
end EtcdGrove
end Perennial

end
