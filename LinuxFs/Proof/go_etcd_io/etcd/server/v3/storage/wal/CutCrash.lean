/- Lean-first (no Rocq counterpart).

# A cut's rename and directory sync keep the crash condition (`notes/wal-fsext-plan.md`, W2)

Pure. The two steps of `(*WAL).cut` (S/wal.go:936-940) that change what a crash can leave:

* **The rename** of `N.tmp` to the new segment's name `bt` (`crashOkA_rename`): the invariant's claim
  on the WAL directory (`(j, except X, h)`, coherent) logs the rename at `x`. A crash that drops it
  (`¬ K x`) is a crash of the claims before it, whose `CrashTo` the old layout's crash condition
  gives (the alternative of `CrashOkA`). A crash that keeps it keeps every earlier entry of the claim
  (they took effect before the rename's call began), so the directory's names are as now
  (`ClaimCoh`), and the WAL directory is where the old crash condition, applied to the crashed tree
  without the new name, says it is; the new layout's `CrashTo` then follows from its every byte
  being durable (`hkept`, given by `crashTo_synced`).
* **The directory's fsync** (`crashOk_dirSync`): once the commit bound passes the rename, every crash
  keeps it, so the new segment is named and the alternative's `CrashTo` is impossible
  (`crashOk_of_alt`).

`crashTo_synced`: a WAL every byte of whose segments is durable, its synced mark `|H|`, its directory
named as now: its `CrashTo` (the image is the history itself).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section cutcrash
variable [GooseExts]

/-! ## Region crashes with the kept set named -/

/-- `RegionCrashed` with its kept set `K`. -/
def RegionCrashedK (cl : List Claim) (n : Nat) (m' : Tree) (K : Nat → Prop) : Prop :=
  (∀ c ∈ cl, ∀ c' ∈ cl, ∀ x e E y e' E', (x, e, E) ∈ c.2.2.ents → (y, e', E') ∈ c'.2.2.ents →
      K x → y < e.start → K y) ∧
    (∀ c ∈ cl, ∀ y e E, (y, e, E) ∈ c.2.2.ents → y < n → K y) ∧
    (∀ c ∈ cl, ∀ b, c.2.1.Mem b → m'.entry c.1 b = c.2.2.valAfter c.1 K b)

theorem regionCrashed_iff (cl : List Claim) (n : Nat) (m' : Tree) :
    RegionCrashed cl n m' ↔ ∃ K, RegionCrashedK cl n m' K := Iff.rfl

open Classical in
/-- The claims with `c0` replaced by `c1`. -/
def replClaim (c0 c1 : Claim) (cl : List Claim) : List Claim :=
  cl.map (fun c => if c = c0 then c1 else c)

open Classical in
theorem mem_replClaim {c0 c1 c : Claim} {cl : List Claim} (h : c ∈ cl) :
    (if c = c0 then c1 else c) ∈ replClaim c0 c1 cl :=
  List.mem_map_of_mem h

theorem valAfter_log_notKept (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hx : ¬ K x) : (h.log x e c).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_neg (by simp [hx])]
  simp

theorem valAfter_log_notWrites (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hw : ¬ e.op.Writes j b) :
    (h.log x e c).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_neg (by simp [hw])]
  simp

theorem valAfter_log_last (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hK : K x) (hw : e.op.Writes j b) :
    (h.log x e c).valAfter j K b = c !! b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_pos (by simp [hK, hw])]
  simp

/-- A crash of the claims after an entry logged at `x` that drops it is a crash of the claims
before it. -/
theorem regionCrashedK_unlog (cl : List Claim) (n : Nat) (m' : Tree) (K : Nat → Prop) (j : Ino)
    (N : NameSet) (h : NamesH) (x : Nat) (e : LogEntry) (c : Ents)
    (hK : RegionCrashedK (replClaim (j, N, h) (j, N, h.log x e c) cl) n m' K) (hx : ¬ K x) :
    RegionCrashedK cl n m' K := by
  classical
  let f : Claim → Claim := fun c' => if c' = (j, N, h) then (j, N, h.log x e c) else c'
  have hf1 : ∀ c', (f c').1 = c'.1 := fun c' => by
    simp only [f]; split <;> simp_all
  have hf2 : ∀ c', (f c').2.1 = c'.2.1 := fun c' => by
    simp only [f]; split <;> simp_all
  have hfe : ∀ c' y, y ∈ c'.2.2.ents → y ∈ (f c').2.2.ents := fun c' y hy => by
    simp only [f]; split
    · rename_i hc; subst hc; simp [NamesH.log, hy]
    · exact hy
  have hfv : ∀ c' b, (f c').2.2.valAfter c'.1 K b = c'.2.2.valAfter c'.1 K b := fun c' b => by
    simp only [f]; split
    · rename_i hc; subst hc; exact valAfter_log_notKept _ _ _ _ _ _ _ hx
    · rfl
  obtain ⟨h1, h2, h3⟩ := hK
  refine ⟨fun c1 hc1 c2 hc2 x' e' E y e'' E' hx' hy hKx hlt => ?_, fun c1 hc1 y e' E hy hlt => ?_,
    fun c1 hc1 b hb => ?_⟩
  · exact h1 (f c1) (mem_replClaim hc1) (f c2) (mem_replClaim hc2) x' e' E y e'' E'
      (hfe c1 _ hx') (hfe c2 _ hy) hKx hlt
  · exact h2 (f c1) (mem_replClaim hc1) y e' E (hfe c1 _ hy) hlt
  · have := h3 (f c1) (mem_replClaim hc1) b (by rw [hf2]; exact hb)
    rw [hf1, hfv] at this
    exact this

/-- The tree `m'` without the name `bt` of the directory `j`. -/
def treeDel (m' : Tree) (j : Ino) (bt : GoString) : Tree := m'.upd j (fun D => GMap.delete bt D)

theorem treeDel_entry (m' : Tree) (j : Ino) (bt : GoString) (j' : Ino) (b : GoString) :
    (treeDel m' j bt).entry j' b = if j' = j ∧ b = bt then none else m'.entry j' b := by
  unfold treeDel Tree.upd Tree.entry
  by_cases hj : j' = j
  · subst hj
    rw [GMap.lookup_insert]
    simp only [Option.bind_some]
    by_cases hb : b = bt
    · subst hb; simp
    · rw [GMap.lookup_delete_ne _ (Ne.symm hb)]
      simp only [hb, and_false, ite_false]
      cases m' !! j' <;> simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj)]
    simp [hj]

theorem named_treeDel {m' : Tree} {j : Ino} {bt : GoString} {i : Ino}
    (h : Named (treeDel m' j bt) i) : Named m' i := by
  obtain ⟨j', b, hb⟩ := h
  refine ⟨j', b, ?_⟩
  rw [treeDel_entry] at hb
  split at hb
  · cases hb
  · exact hb

/-- **A crash that keeps the entry logged at `x`** (a rename writing, among the claim's names, only
`bt`, free before it) keeps every earlier entry of the coherent claim, and, without the name `bt`,
is a crash of the claims before it. -/
theorem regionCrashedK_kept (cl : List Claim) (n : Nat) (m' : Tree) (K : Nat → Prop) (j : Ino)
    (N : NameSet) (h : NamesH) (x : Nat) (e : LogEntry) (c : Ents) (bt : GoString)
    (hK : RegionCrashedK (replClaim (j, N, h) (j, N, h.log x e c) cl) n m' K) (hx : K x)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    (∀ xe ∈ h.ents, K xe.1) ∧ RegionCrashedK cl n (treeDel m' j bt) K := by
  classical
  have hold : ∀ xe ∈ h.ents, K xe.1 := by
    intro xe hxe
    have hc1 : (j, N, h.log x e c) ∈ replClaim (j, N, h) (j, N, h.log x e c) cl := by
      have := mem_replClaim (c0 := (j, N, h)) (c1 := (j, N, h.log x e c)) hcl
      simpa using this
    exact hK.1 _ hc1 _ hc1 x e c xe.1 xe.2.1 xe.2.2 (by simp [NamesH.log])
      (by simp [NamesH.log, hxe]) hx (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hs)
  refine ⟨hold, ?_⟩
  -- the closure and the commit bound: as for the claims after the entry
  let f : Claim → Claim := fun c' => if c' = (j, N, h) then (j, N, h.log x e c) else c'
  have hfe : ∀ c' y, y ∈ c'.2.2.ents → y ∈ (f c').2.2.ents := fun c' y hy => by
    simp only [f]; split
    · rename_i hc; subst hc; simp [NamesH.log, hy]
    · exact hy
  obtain ⟨h1, h2, h3⟩ := hK
  refine ⟨fun c1 hc1 c2 hc2 x' e' E y e'' E' hx' hy hKx hlt => ?_, fun c1 hc1 y e' E hy hlt => ?_,
    fun c1 hc1 b hb => ?_⟩
  · exact h1 (f c1) (mem_replClaim hc1) (f c2) (mem_replClaim hc2) x' e' E y e'' E'
      (hfe c1 _ hx') (hfe c2 _ hy) hKx hlt
  · exact h2 (f c1) (mem_replClaim hc1) y e' E (hfe c1 _ hy) hlt
  · have h3' := h3 (f c1) (mem_replClaim hc1)
    rw [treeDel_entry]
    by_cases hc : c1 = (j, N, h)
    · subst hc
      simp only [f, ite_true] at h3'
      by_cases hb' : b = bt
      · subst hb'
        simp only [and_self, ite_true]
        rw [hcoh.2 K hold b hb, hcur]
      · simp only [hb', and_false, ite_false]
        rw [h3' b hb]
        exact valAfter_log_notWrites _ _ _ _ _ _ _ (fun hw => hb' (hbt b hb hw))
    · simp only [f, hc, ite_false] at h3'
      have : ¬ (c1.1 = j ∧ b = bt) := fun ⟨e1, e2⟩ => hothers c1 hc1 hc e1 (e2 ▸ hb)
      simp only [this, ite_false]
      exact h3' b hb

/-! ## W1 over durable segments -/

theorem valAt_durB (x : w8) : valAt (durB x).2 0 = x := by
  simp [valAt]

/-- **W1 over segments whose every byte is durable** holds by itself: each image is its bytes (or
empty), so every accepted frame is as of the last sync. -/
theorem w1G_durable (C : WalCodec) (js : List Ino) (img : Ino → List w8)
    (bsOf : Ino → Option (List ByteG)) (rzOf : Ino → List Nat)
    (h : ∀ i bs, bsOf i = some bs → (∀ y ∈ bs, y = durB y.1) ∧
      (img i = bs.map (·.1) ∨ img i = [])) :
    W1G C js img bsOf rzOf := by
  intro k p hp i bs hi hbs _
  obtain ⟨hdur, himg⟩ := h i bs hbs
  obtain ⟨x, hx, hb⟩ := acceptsFiles_bound C _ _ p hp
  rw [List.getElem?_map, hi] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  subst hx
  left
  intro b hb1 hb2
  show (img i).getD b 0 = valAt (bs.getD b (0, [])).2 0
  rcases himg with himg | himg
  · have hlt : b < (img i).length := by omega
    rw [himg] at hlt ⊢
    simp only [List.length_map] at hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.getD_some]
    rw [hdur _ (List.getElem_mem hlt)]
    exact (valAt_durB _).symm
  · rw [himg] at hb hb2; unfold frameCore at hb hb2; simp at hb

/-- The bytes `segBytesOf` gives for a prefix of the segments, it gives for the whole list. -/
theorem segBytesOf_prefix {lay lay' : WalLay} (h : lay.segs <+: lay'.segs) (i : Ino)
    (bs : List ByteG) (hb : segBytesOf lay i = some bs) : segBytesOf lay' i = some bs := by
  obtain ⟨t, ht⟩ := h
  unfold segBytesOf at hb ⊢
  rw [← ht, List.find?_append]
  cases hf : lay.segs.find? (fun g => decide (g.ino = i)) with
  | none => rw [hf] at hb; cases hb
  | some g => rw [hf] at hb; simpa using hb

theorem w1G_prefix {C : WalCodec} {js : List Ino} {img : Ino → List w8} {lay lay' : WalLay}
    {rzOf : Ino → List Nat} (h : lay.segs <+: lay'.segs) (hw : W1G C js img (segBytesOf lay') rzOf) :
    W1G C js img (segBytesOf lay) rzOf :=
  fun k p hp i bs hi hbs => hw k p hp i bs hi (segBytesOf_prefix h i bs hbs)

/-! ## The rename -/

/-- A `.wal` name of `E` holding the file `i`: `i` is among `E`'s `.wal` files. -/
theorem mem_walInos {E : Ents} {b : GoString} {i : Ino} (hb : walNameP b = true)
    (he : E !! b = some (.file i)) : i ∈ walInos E := by
  unfold walInos walNames
  refine List.mem_filterMap.2 ⟨b, ?_, by rw [he]⟩
  refine (List.mergeSort_perm _ _).mem_iff.2 (List.mem_filter.2 ⟨?_, hb⟩)
  exact List.mem_map.2 ⟨(b, .file i), (GMap.mem_toList _ _ _).2 he, rfl⟩

theorem entsOf_lookup_entry (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry
  cases m !! j <;> rfl

/-- A listed `.wal` file is a file at a `.wal` name. -/
theorem walInos_mem_inv {E : Ents} {i : Ino} (h : i ∈ walInos E) :
    ∃ b, walNameP b = true ∧ E !! b = some (.file i) := by
  unfold walInos at h
  obtain ⟨b, hbm, hb⟩ := List.mem_filterMap.1 h
  refine ⟨b, ?_, ?_⟩
  · unfold walNames at hbm
    exact (List.mem_filter.1 (List.mem_mergeSort.1 hbm)).2
  · split at hb <;> simp_all

/-- Deleting a name lists no new `.wal` file. -/
theorem mem_walInos_treeDel {m' : Tree} {j J : Ino} {bt : GoString} {i : Ino}
    (h : i ∈ walInos (entsOf (treeDel m' j bt) J)) : i ∈ walInos (entsOf m' J) := by
  obtain ⟨b, hb, he⟩ := walInos_mem_inv h
  rw [entsOf_lookup_entry, treeDel_entry] at he
  split at he
  · cases he
  · exact mem_walInos hb (by rw [entsOf_lookup_entry]; exact he)

/-- **A cut's rename keeps the crash condition, with the old layout as the alternative.** Before
the rename: the crash condition `hok` of `lay` over the claims `cl`, its static relation `habs` (for
the sizes), every byte of its segments durable (`hdur`: the old tail truncated and synced), the
coherent claim `(j, except X, h)` on the WAL directory. The rename (the entry `e` at `x`, by a call
begun after the claim's last entry) writes, of the claim's names, only the free `bt` (no other claim
has it; not the WAL directory's name in the area); `hkept` is the new layout's `CrashTo` in a crash
keeping it (the directory's names as the claim has them after it, the WAL directory where the old
crash condition puts it). -/
theorem crashOkA_rename (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay lay' : WalLay)
    (ents : Ents) (cl : List Claim) (n : Nat) (X : List GoString) (h : NamesH) (x : Nat)
    (e : LogEntry) (c : Ents) (bt : GoString)
    (hok : CrashOk C Mr d lay cl n) (habs : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1)
    (hcl : (lay.j, NameSet.except X, h) ∈ cl) (hcoh : ClaimCoh h lay.j (.except X))
    (hcoh' : ClaimCoh (h.log x e c) lay.j (.except X)) (hs : h.next ≤ e.start)
    (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, h) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt)
    (hjr : lay.jr ≠ lay.j ∨ lay.nm ≠ bt)
    (hpre : lay.segs <+: lay'.segs) (hj' : lay'.j = lay.j)
    (hkept : ∀ (m' : Tree) (fo : Ino → Option Fs.OsFile),
      (∀ g ∈ lay'.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino)) →
      (∀ g ∈ lay'.segs, g.ino ∈ walInos (entsOf m' lay'.j) → (fo g.ino).isSome) →
      (∀ b, (NameSet.except X).Mem b → m'.entry lay.j b = c !! b) →
      ((d.named = false ∧ m'.entry lay.jr lay.nm = none) ∨
        m'.entry lay.jr lay.nm = some (.dir lay.j)) →
      CrashTo C Mr d lay' m' fo) :
    CrashOkA C Mr d lay' (some lay)
      (replClaim (lay.j, NameSet.except X, h) (lay.j, NameSet.except X, h.log x e c) cl) n := by
  classical
  intro m' fo hr hf hn hw
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  have hfo : ∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino) :=
    fun g hg => hf g (hpre.subset hg)
  by_cases hx : K x
  · -- the rename kept: every entry of the claim kept, the names as now
    obtain ⟨hold, hK'⟩ := regionCrashedK_kept cl n m' K lay.j _ h x e c bt hK hx hcl hcoh hs hbt
      hcur hothers
    left
    refine hkept m' fo hf hn (fun b hb => ?_) ?_
    · have hc1 : (lay.j, NameSet.except X, h.log x e c) ∈
          replClaim (lay.j, NameSet.except X, h) (lay.j, NameSet.except X, h.log x e c) cl := by
        simpa using mem_replClaim (c0 := (lay.j, NameSet.except X, h))
          (c1 := (lay.j, NameSet.except X, h.log x e c)) hcl
      rw [hK.2.2 _ hc1 b hb]
      refine hcoh'.2 K (fun xe hxe => ?_) b hb
      simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
      rcases hxe with hxe | rfl
      · exact hold xe hxe
      · exact hx
    · -- where the WAL directory is: the old crash condition, over the tree without `bt`
      have hct := hok (treeDel m' lay.j bt) fo ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩) hfo
        (fun g hg hin => hn g (hpre.subset hg) (by rw [hj']; exact mem_walInos_treeDel hin))
        (w1G_durable C _ _ _ _ (fun i bs hb => by
          obtain ⟨g, hg, rfl, rfl⟩ := segBytesOf_some_ex
            (fun g1 hg1 => Nat.le_of_eq (habs.metasEx hex g1 hg1).2.2.2) hb
          refine ⟨hdur g hg, ?_⟩
          cases hfg : fo g.ino with
          | none => right; simp [imgOf]
          | some f' =>
            left
            have hm := habs.metasEx hex g hg
            have hbs : g.bs = (g.bs.map (·.1)).map durB := by
              rw [List.map_map]
              exact (List.map_id' g.bs).symm.trans
                (List.map_congr_left (fun y hy => hdur g hg y hy))
            have hfc := hfo g hg
            rw [hfg, hbs] at hfc
            have := durable_img hfc (by rw [hm.2.2.1]; simp) (by rw [hm.2.2.2]; simp)
            simp [imgOf, this]))
      have hne : (treeDel m' lay.j bt).entry lay.jr lay.nm = m'.entry lay.jr lay.nm := by
        rw [treeDel_entry]
        have : ¬ (lay.jr = lay.j ∧ lay.nm = bt) := fun ⟨a, b⟩ => by
          rcases hjr with h1 | h1 <;> contradiction
        simp [this]
      rcases hct with ⟨hnamed, hab⟩ | ⟨q, I, hent, -⟩
      · left; exact ⟨hnamed, by rw [← hne]; exact hab⟩
      · right; rw [← hne]; exact hent
  · -- the rename dropped: a crash of the claims before it, the old layout's
    right
    refine ⟨lay, rfl, hok m' fo ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K
      lay.j _ h x e c hK hx⟩) hfo
      (fun g hg hin => hn g (hpre.subset hg) (by rw [hj']; exact hin)) ?_⟩
    rw [hj'] at hw
    exact w1G_prefix hpre (hw.mono_rz (segRzOf_prefix hpre))

/-! ## The directory's fsync -/

/-- **The directory's fsync drops the alternative**: a commit bound past the rename (logged at `x`
in the claim `(j, except X, h.log x e c)`, the new segment `i` at the `.wal` name `bt`) makes every
crash keep it. -/
theorem crashOk_dirSync (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay lay0 : WalLay)
    (cl : List Claim) (n : Nat) (X : List GoString) (h : NamesH) (x : Nat) (e : LogEntry)
    (c : Ents) (bt : GoString) (i : Ino)
    (halt : AltOk C Mr d lay lay0) (hok : CrashOkA C Mr d lay (some lay0) cl n)
    (hcl : (lay.j, NameSet.except X, h.log x e c) ∈ cl) (hx : x < n)
    (hw : e.op.Writes lay.j bt) (hbtX : bt ∉ X) (hwal : walNameP bt = true)
    (hc : c !! bt = some (.file i)) (hi : i ∉ lay0.segs.map (·.ino)) :
    CrashOk C Mr d lay cl n := by
  refine crashOk_of_alt C Mr d lay lay0 cl n halt hok i hi (fun m' hr _ => ?_)
  obtain ⟨K, -, h2, h3⟩ := (regionCrashed_iff _ _ _).1 hr
  have hK : K x := h2 _ hcl x e c (by simp [NamesH.log]) hx
  have he := h3 _ hcl bt hbtX
  simp only at he
  rw [valAfter_log_last _ _ _ _ _ _ _ hK hw, hc] at he
  rw [← entsOf_lookup] at he
  exact mem_walInos hwal he

end cutcrash

end WalFs
end EtcdGrove
end Perennial

end
