/- Lean-first (no Rocq counterpart).

# A purge's removal: the invariant's pure facts after its commit (unit `locks`, session 9)

Pure. The purge's `os.Remove(dir/bt)` (`os.Remove.specFileSncN`) of the first named segment `g0` of the WAL
`dir` (not its last), under the WAL directory's claim `(j, .except X, hj)` (half the handle's, lent, half
the invariant's, the key `walDirKey dir j X`), logs the unlink at `x` (a call begun at `s0`); the claim's
names after it are `purgeNames X bt hj` (the directory without `bt`, `rmFileOutN`'s). The WAL state moves to
`purSt s dir p k` (`pur` raised to `p`, the read position to `k`, the next segment's start: the client's
update, `walPurge_osAUnc`), the layout to `purgeLayP lay g0` (`PurgeWals.lean`).

`purgeCommit_pure` bundles what `walInvBody`'s pure conjuncts need after the commit, as `cutCommit_pure`
(`CutCommit.lean`) for a cut's rename. Per conjunct:
- `WalsOk`: the purged WAL's static relation `walAbsD_purgeP` (the claim's `.wal` files the other segments',
  `walInos_delete_first`), its full condition `walFullOk_purge` (over `DirKeysOk`'s crash condition: no cut
  pending, `walCutFrag none`); the others' conditions over the logged claim (`walFullOk_purge_other`); the
  inodes as before (the segments the same list per directory); `AbsentOk`, `DirsOk` (`absentNone_purge`,
  `dirsOk_purge`: a crash keeping the removal is one of the claims before it, `bt` set back to `g0`'s file,
  which no WAL name of the area and no successful walk to a directory reads).
- `WalsCreateOk`, `CreatingOk`, `AbsentNone`: claims of `jr` unchanged (`j ≠ jr`).
- `WalsNamed`: the other segments at their names in the new claim; after a crash keeping the removal, as
  the new claim has them (`g0` named nowhere: a removed segment, `segsNamedC_pg`); dropping it, as before
  (the segments the same list).
- `DirKeysOk`: the key's claim replaced once (`dirKeysOk_purge`, `dirKeysOk_cut`'s argument), no cut
  pending, every WAL's crash condition over the logged claim.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeWals
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnl
public import Spec.os.RemoveN
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockRange

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-! ## The state after the purge -/

/-- The WAL update of a purge's removal: `pur` raised to `p`, the read position `k`. -/
def purD (p k : Nat) (d : WalDur) : WalDur := { d with pur := max d.pur p, cut := k }

/-- **The state after a purge's removal in `dir`.** -/
def purSt (s : AbsDiskState) (dir : GoString) (p k : Nat) : AbsDiskState :=
  absDiskUpd s dir (purD p k)

theorem purD_walPurgeD (d : WalDur) (lay : WalLay) (p : Nat) :
    purD p (segStart lay.cuts (lay.first + 1)) d = walPurgeD d lay p := rfl

theorem purSt_lookup (s : AbsDiskState) (dir : GoString) (p k : Nat) (k' : GoString) :
    (purSt s dir p k).wal !! k' = (s.wal !! k').map (fun d => if k' = dir then purD p k d else d) := by
  unfold purSt absDiskUpd
  cases hd : s.wal !! dir with
  | none =>
    simp only
    cases hk : s.wal !! k' with
    | none => rfl
    | some d =>
      simp only [Option.map_some]
      by_cases e : k' = dir
      · subst e; rw [hd] at hk; cases hk
      · rw [if_neg e]
  | some d0 =>
    simp only
    by_cases e : k' = dir
    · subst e; rw [GMap.lookup_insert_eq, hd]; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]
      cases s.wal !! k' <;> simp [e]

theorem purSt_self {s : AbsDiskState} {dir : GoString} {p k : Nat} {d : WalDur} (hd : s.wal !! dir = some d) :
    (purSt s dir p k).wal !! dir = some (purD p k d) := by
  rw [purSt_lookup, hd]; simp

theorem purSt_ne {s : AbsDiskState} {dir : GoString} {p k : Nat} {k' : GoString} (h : k' ≠ dir) :
    (purSt s dir p k).wal !! k' = s.wal !! k' := by
  rw [purSt_lookup]; cases s.wal !! k' <;> simp [h]

theorem purSt_none {s : AbsDiskState} {dir : GoString} {p k : Nat} {k' : GoString} :
    (purSt s dir p k).wal !! k' = none ↔ s.wal !! k' = none := by
  rw [purSt_lookup]; cases s.wal !! k' <;> simp

theorem purSt_area (s : AbsDiskState) (dir : GoString) (p k : Nat) : (purSt s dir p k).area = s.area :=
  absDiskUpd_area s dir _

theorem purSt_dirs (s : AbsDiskState) (dir : GoString) (p k : Nat) : (purSt s dir p k).dirs = s.dirs := by
  unfold purSt absDiskUpd; cases s.wal !! dir <;> rfl

theorem absLe_purSt (s : AbsDiskState) (dir : GoString) (p k : Nat) : absLe s (purSt s dir p k) :=
  absLe_upd s dir _ (fun _ => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)

/-! ## The claim after the removal -/

/-- **The WAL directory's names after the removal of `bt`** (`rmFileOutN`'s). -/
def purgeNames (X : List GoString) (bt : GoString) (hj : NamesH) : Ents :=
  restrictN (.except X) (GMap.delete bt hj.cur)

/-- **The WAL directory's claim after the removal** (logged at `x` by a call begun at `s0`). -/
def purgeClaim (j : Ino) (X : List GoString) (hj : NamesH) (bt : GoString) (i : Ino) (x s0 : Nat) : Claim :=
  (j, .except X, hj.log x (rmFileEnt j bt i s0) (purgeNames X bt hj))

theorem rmFileEnt_writes (j : Ino) (bt : GoString) (i : Ino) (s0 : Nat) (j' : Ino) (b : GoString) :
    (rmFileEnt j bt i s0).op.Writes j' b ↔ j' = j ∧ b = bt := by
  unfold rmFileEnt MetaOp.Writes MetaOp.slots
  constructor
  · rintro (h | ⟨j0, b0, h⟩)
    · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
      exact h
    · cases h
  · rintro ⟨rfl, rfl⟩; left; simp

theorem purgeNames_lookup {X : List GoString} {bt b : GoString} {hj : NamesH}
    (hb : (NameSet.except X).Mem b) (hne : b ≠ bt) : purgeNames X bt hj !! b = hj.cur !! b := by
  unfold purgeNames
  rw [restrictN_lookup _ _ _ hb, GMap.lookup_delete_ne _ (Ne.symm hne)]

theorem purgeNames_bt {X : List GoString} {bt : GoString} {hj : NamesH} : purgeNames X bt hj !! bt = none := by
  unfold purgeNames restrictN
  rw [GMap.lookup_filter, GMap.lookup_delete]; rfl

/-- The names after the removal are some of the claim's. -/
theorem purgeNames_sub {X : List GoString} {bt b : GoString} {hj : NamesH} {n : Node}
    (h : purgeNames X bt hj !! b = some n) : hj.cur !! b = some n := by
  unfold purgeNames restrictN at h
  rw [GMap.lookup_filter] at h
  by_cases hb : b = bt
  · subst hb; rw [GMap.lookup_delete] at h; simp at h
  · rw [GMap.lookup_delete_ne _ (Ne.symm hb)] at h
    cases hc : hj.cur !! b with
    | none => rw [hc] at h; simp at h
    | some v =>
      rw [hc] at h
      by_cases hm : (NameSet.except X).Mem b
      · simp [Option.filter, hm] at h; rw [h]
      · simp [Option.filter, hm] at h

/-- The client's state after a purge's commit stays below the real one. -/
theorem walDurLe_purD {dc d : WalDur} (h : walDurLe dc d) (p k : Nat) :
    walDurLe { dc with pur := max dc.pur p, cut := k } (purD p k d) := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, by simp [purD, h3], rfl, h5, h6, h7, h8⟩

/-- The `.wal` names of the names after the removal: those of the directory without `bt`. -/
theorem purgeNames_wal {X : List GoString} {bt : GoString} {hj : NamesH} (hX : ∀ b ∈ X, walNameP b = false) :
    ∀ b, walNameP b = true → purgeNames X bt hj !! b = GMap.delete bt hj.cur !! b := by
  intro b hb
  unfold purgeNames
  exact restrictN_lookup _ _ _ (fun h => by rw [hX b h] at hb; cases hb)

theorem except_mem_name {X : List GoString} (hX : ∀ b ∈ X, walNameP b = false) {b : GoString}
    (hb : walNameP b = true) : (NameSet.except X).Mem b := fun h => by rw [hX b h] at hb; cases hb

/-! ## What reads no `(j, bt)` -/

/-- A successful walk to a directory in the tree with `(j, bt)` a file is one in the tree (it never reads
that entry: a file ends a walk, and is no directory). -/
theorem walk_treeSetE_file {m : Tree} {j : Ino} {bt : GoString} {i : Ino} :
    ∀ (cs : List GoString) (nd : Node) (J : Ino),
      walk (treeSetE m j bt (some (.file i))) nd cs = some (.dir J) → walk m nd cs = some (.dir J)
  | [], _, _, h => h
  | c :: cs, nd, J, h => by
    cases nd with
    | file _ => simp [walk] at h
    | dir j' =>
      simp only [walk] at h ⊢
      rw [treeSetE_entry] at h
      by_cases hc : j' = j ∧ c = bt
      · rw [if_pos hc] at h
        cases cs with
        | nil => simp [walk] at h
        | cons c' cs' => simp [walk] at h
      · rw [if_neg hc] at h
        cases hm : m.entry j' c with
        | none => rw [hm] at h; cases h
        | some n' =>
          rw [hm] at h
          exact walk_treeSetE_file cs n' J h

theorem lookupH_treeSetE_file {R : Roots} {m : Tree} {j : Ino} {bt : GoString} {i : Ino} {p : GoString}
    {J : Ino} (h : lookupH R (treeSetE m j bt (some (.file i)), []) p = some (.dir J)) :
    lookupH R (m, []) p = some (.dir J) := by
  unfold lookupH OsState.lookup at *
  split at h
  · rename_i hc
    split
    · exact walk_treeSetE_file _ _ _ h
    · rename_i hc'; exact absurd hc hc'
  · cases h

/-- **Strong absence after the removal** (the claim not of the area directory). -/
theorem absentNone_purge {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} {j : Ino}
    {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (han : AbsentNone s jr cl n) (hjjr : j ≠ jr)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    AbsentNone s jr (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro dir nm hin hnone
  obtain ⟨h1, h2⟩ := han dir nm hin hnone
  refine ⟨fun N' h' hm hN => ?_, fun m' hr => ?_⟩
  · rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
    · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hjjr
    · exact h1 N' h' hm' hN
  · rcases regionCrashed_purge hr hcl hcoh hs hbt hothers with hr' | hr'
    · have := h2 _ hr'
      rw [treeSetE_entry] at this
      simpa [Ne.symm hjjr] using this
    · exact h2 m' hr'

/-- **The durable directories after the removal** (`bt` held a file). -/
theorem dirsOk_purge {R : Roots} {s : AbsDiskState} {cl : List Claim} {n : Nat} {j : Ino}
    {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString} {i : Ino}
    (hdo : DirsOk R s cl n)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = some (.file i))
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    DirsOk R s (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro dd hdd m' hr
  rcases regionCrashed_purge hr hcl hcoh hs hbt hothers with hr' | hr'
  · obtain ⟨J, hJ⟩ := hdo dd hdd _ hr'
    rw [hcur] at hJ
    exact ⟨J, lookupH_treeSetE_file hJ⟩
  · exact hdo dd hdd m' hr'

/-! ## The segments' list -/

/-- The purged layout lists the same segments. -/
theorem purgeLayP_all {lay : WalLay} {g0 : SegG} {gs : List SegG} (hs : lay.segs = g0 :: gs) :
    (purgeLayP lay g0).pg ++ (purgeLayP lay g0).segs = lay.pg ++ lay.segs := by
  simp [hs]

theorem segsAll_purge_mem {Ls : GMap GoString WalLay} {dir : GoString} {lay : WalLay} {g0 : SegG}
    {gs : List SegG} (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs) {g : SegG} :
    g ∈ segsAll (<[dir := purgeLayP lay g0]> Ls) ↔ g ∈ segsAll Ls := by
  constructor
  · intro hg
    obtain ⟨dd, ll, hll, hg'⟩ := segsAll_mem hg
    by_cases hdd : dd = dir
    · rw [hdd, GMap.lookup_insert_eq] at hll
      cases hll
      rw [purgeLayP_all hs] at hg'
      exact mem_segsAll_all hl hg'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hll
      exact mem_segsAll_all hll hg'
  · intro hg
    obtain ⟨dd, ll, hll, hg'⟩ := segsAll_mem hg
    by_cases hdd : dd = dir
    · subst hdd
      rw [hl] at hll; cases hll
      refine mem_segsAll_all (GMap.lookup_insert_eq _ _ _) ?_
      rw [purgeLayP_all hs]; exact hg'
    · exact mem_segsAll_all (by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hll) hg'

theorem segsAll_purge_nodup {Ls : GMap GoString WalLay} {dir : GoString} {lay : WalLay} {g0 : SegG}
    {gs : List SegG} (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs)
    (h : ((segsAll Ls).map (·.ino)).Nodup) :
    ((segsAll (<[dir := purgeLayP lay g0]> Ls)).map (·.ino)).Nodup := by
  refine segsAll_nodup_sub h (fun dd ll hll => ?_)
  by_cases hdd : dd = dir
  · rw [hdd, GMap.lookup_insert_eq] at hll
    cases hll
    exact ⟨lay, by rw [hdd]; exact hl, by rw [purgeLayP_all hs]; exact List.Sublist.refl _⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hll
    exact ⟨ll, hll, List.Sublist.refl _⟩

/-! ## The segments at their names -/

/-- **The segments at their names after the removal** (see the file header). -/
theorem walsNamed_purge {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {d : WalDur}
    {lay : WalLay} {g0 : SegG} {gs : List SegG} {X : List GoString} {hj : NamesH} {x : Nat}
    {e : LogEntry} {bt : GoString}
    (hW : WalsOk C Mr R jr s Ls cl n) (hNm : WalsNamed Ls cl n)
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs)
    (hcl : (lay.j, NameSet.except X, hj) ∈ cl) (hX : ∀ b ∈ X, walNameP b = false)
    (hcoh : ClaimCoh hj lay.j (.except X))
    (hcoh' : ClaimCoh (hj.log x e (purgeNames X bt hj)) lay.j (.except X))
    (hexcl : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j → ∀ b,
      walNameP b = true → ¬ c'.2.1.Mem b)
    (hst : hj.next ≤ e.start) (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hcur : hj.cur !! bt = some (.file g0.ino)) (hbtw : walNameP bt = true)
    (hwal' : walInos (purgeNames X bt hj) = gs.map (·.ino)) :
    WalsNamed (<[dir := purgeLayP lay g0]> Ls)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e (purgeNames X bt hj)) cl)
      n := by
  classical
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl c' hc hne hcj bt hbtw
  have hall := purgeLayP_all (lay := lay) (g0 := g0) hs
  intro dir' lay' hl'
  by_cases hdd : dir' = dir
  · subst hdd
    rw [GMap.lookup_insert_eq] at hl'
    simp only [Option.some.injEq] at hl'
    subst hl'
    have hsn : SegsNamed lay.segs hj.cur := (hNm dir' lay hl).1 hj ⟨X, hX, hcl, hcoh⟩
    have hnd := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir' lay hl
    rw [hs, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
    have hgi : ∀ g ∈ gs, g.ino ≠ g0.ino := fun g hg he => hnd.2.1.1 (he ▸ List.mem_map_of_mem hg)
    have hsn' : SegsNamed gs (purgeNames X bt hj) := by
      refine ⟨fun g hg => ?_, fun b e' hb he => ?_⟩
      · obtain ⟨hw, he⟩ := hsn.1 g (by rw [hs]; exact List.mem_cons_of_mem _ hg)
        have hne : g.name ≠ bt := by
          intro hb; rw [hb, hcur] at he
          exact hgi g hg (Node.file.inj (Option.some.inj he)).symm
        exact ⟨hw, by rw [purgeNames_lookup (except_mem_name hX hw) hne]; exact he⟩
      · rw [purgeNames_wal hX b hb] at he
        by_cases hbe : b = bt
        · rw [hbe, GMap.lookup_delete] at he; cases he
        · rw [GMap.lookup_delete_ne _ (Ne.symm hbe)] at he
          exact hsn.2 b e' hb he
    refine ⟨fun hj'' hWc => ?_, fun m' hr => ?_, fun N' hj'' hm => ?_⟩
    rotate_left 2
    · have h3 := (hNm dir' lay hl).2.2
      rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
      · rw [Prod.mk.injEq, Prod.mk.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        exact (h3 _ _ hcl).log x e _ (fun b hb _ hw J => by
          rw [hbt b hb hw, purgeNames_bt]; simp)
      · exact h3 N' hj'' hm'
    · obtain ⟨X', hX', hm, -⟩ := hWc
      rcases mem_replClaim_cases hm with he | ⟨hm', hne⟩
      · simp only [Prod.mk.injEq] at he
        rw [he.2.2]; simpa [hs, NamesH.log] using hsn'
      · exact absurd (except_mem_wal hX') (hexcl _ hm' hne rfl _ walNameP_wal)
    · show SegsNamedC ((purgeLayP lay g0).pg ++ (purgeLayP lay g0).segs) (entsOf m' lay.j)
      obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
      obtain ⟨lay0, -, -, hl0, -, -, -, -, -, ⟨⟨e0, hF⟩, -⟩⟩ := hW.1 dir' d hd
      rw [hl] at hl0; cases hl0
      by_cases hx : K x
      · obtain ⟨hold, -⟩ := regionCrashedK_keptSet cl n m' K lay.j _ hj x e _ bt hK hx hcl hcoh hst hbt
          hothers
        have hpg : ∀ g ∈ lay.pg ++ [g0], walNameP g.name = true := by
          intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact pg_walNameP hF g hg
          · rw [List.mem_singleton.1 hg]; exact (hsn.1 g0 (by rw [hs]; simp)).1
        have hpgi : ∀ g ∈ lay.pg ++ [g0], g.ino ∉ gs.map (·.ino) := by
          intro g hg hi
          rcases List.mem_append.1 hg with hg | hg
          · exact hnd.2.2 _ (List.mem_map_of_mem hg) _ (List.mem_cons_of_mem _ hi) rfl
          · rw [List.mem_singleton.1 hg] at hi; exact hnd.2.1.1 hi
        simp only [purgeLayP_pg, purgeLayP_segs, hs, List.tail_cons]
        refine segsNamedC_pg (segsNamedC_congr_ents (fun b hb => ?_) (hsn'.crash (fun i hi => ?_))) hpg hpgi
        · have hbX : (NameSet.except X).Mem b := except_mem_name hX hb
          rw [entsOf_entry, hK.2.2 _ (mem_replClaim_new hcl) b hbX]
          refine (hcoh'.2 K (fun xe hxe => ?_) b hbX).symm
          simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
          rcases hxe with hxe | hxe
          · exact hold xe hxe
          · rw [hxe]; exact hx
        · rw [hwal'] at hi; exact hi
      · have hr' : RegionCrashed cl n m' :=
          (regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K lay.j _ hj x e _ hK hx⟩
        rw [hall]
        exact (hNm dir' lay hl).2.1 m' hr'
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
    have hjne : lay'.j ≠ lay.j := walsOk_dir_ne hW hexcl hd hl rfl hdd hl'
    obtain ⟨h1, h2, h3⟩ := hNm dir' lay' hl'
    refine ⟨fun hj'' hWc => ?_, fun m' hr => ?_, fun N' hj'' hm => ?_⟩
    · obtain ⟨X', hX', hm, hcoh''⟩ := hWc
      rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
      · simp only [Prod.mk.injEq] at he; exact absurd he.1 hjne
      · exact h1 hj'' ⟨X', hX', hm', hcoh''⟩
    rotate_left
    · rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
      · rw [Prod.mk.injEq] at he; exact absurd he.1 hjne
      · exact h3 N' hj'' hm'
    · rcases regionCrashed_purge hr hcl hcoh hst hbt hothers with hr' | hr'
      · rw [← entsOf_treeSetE_ne m' bt _ hjne]; exact h2 _ hr'
      · exact h2 m' hr'

/-! ## The directory keys -/

/-- **The directory keys after the removal**: the purged WAL's claim replaced once, the other keys as
before (their directories not `j`); no cut pending; every WAL's crash condition over the logged claim (the
purged one's `hcrP`, the caller's: `crashOkA_full_purge`). -/
theorem dirKeysOk_purge {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s s' : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString} {d d' : WalDur} {lay lay' : WalLay}
    {X : List GoString} {hj : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hW : WalsOk C Mr R jr s Ls cl n) (hDK : DirKeysOk C Mr jr s Ls cl n K none)
    (hK : K !! dir = some (lay.j, X)) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hd' : s'.wal !! dir = some d') (hs' : ∀ k, k ≠ dir → s'.wal !! k = s.wal !! k)
    (hlj' : lay'.j = lay.j) (hjjr : lay.j ≠ jr) (hX : ∀ b ∈ X, walNameP b = false)
    (hc0 : ClaimOnce (lay.j, NameSet.except X, hj) cl)
    (hcoh : ClaimCoh hj lay.j (.except X)) (hcoh' : ClaimCoh (hj.log x e c) lay.j (.except X))
    (hexcl : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j → ∀ b,
      walNameP b = true → ¬ c'.2.1.Mem b)
    (hst : hj.next ≤ e.start) (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hbtw : walNameP bt = true)
    (hcrP : CrashOkA C Mr (walFullD d' lay'.pg lay') (unpurge lay'.pg lay') none
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl) n) :
    DirKeysOk C Mr jr s' (<[dir := lay']> Ls)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl) n K none := by
  classical
  have hcl := claimOnce_mem hc0
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl c' hc hne hcj bt hbtw
  have hne10 : (lay.j, NameSet.except X, hj.log x e c) ≠ (lay.j, NameSet.except X, hj) := by
    intro h; simp only [Prod.mk.injEq] at h; exact namesH_log_ne _ _ _ _ h.2.2
  have hcutOnce : ClaimOnce (lay.j, NameSet.except X, hj.log x e c)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl) := by
    obtain ⟨l1, l2, hcl', hrep⟩ :=
      claimOnce_repl (c' := (lay.j, NameSet.except X, hj.log x e c)) hc0
    have hnot : ∀ l : List Claim, (∀ y ∈ l, y ∈ cl) →
        (lay.j, NameSet.except X, hj.log x e c) ∉ l := fun l hsub hm =>
      hexcl _ (hsub _ hm) hne10 rfl _ walNameP_wal (except_mem_wal hX)
    exact ⟨l1, l2, hrep, hnot l1 (fun y hy => by rw [hcl']; exact List.mem_append_left _ hy),
      hnot l2 (fun y hy => by rw [hcl']; simp [hy])⟩
  have hcutEx : ∀ c' ∈ replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl,
      c' ≠ (lay.j, NameSet.except X, hj.log x e c) → c'.1 = lay.j → ∀ b, walNameP b = true →
        ¬ c'.2.1.Mem b := by
    intro c' hc' hne hcj b hb
    rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
    · exact absurd he hne
    · exact hexcl c' hc'' hne0 hcj b hb
  have hother : ∀ (j' : Ino) (X' : List GoString) (hj1 : NamesH), j' ≠ lay.j → DirClaimOk jr cl j' X' hj1 →
      DirClaimOk jr (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl)
        j' X' hj1 := by
    intro j' X' hj1 hj'j ⟨hj1jr, hX1, honce1, hcoh1, hex1⟩
    have hne0 : (j', NameSet.except X', hj1) ≠ (lay.j, NameSet.except X, hj) := fun e => hj'j
      (by simp only [Prod.mk.injEq] at e; exact e.1)
    have hne1 : (j', NameSet.except X', hj1) ≠ (lay.j, NameSet.except X, hj.log x e c) := fun e =>
      hj'j (by simp only [Prod.mk.injEq] at e; exact e.1)
    refine ⟨hj1jr, hX1, claimOnce_repl_other honce1 hne0 hne1, hcoh1, fun c' hc' hne hc1 b hb => ?_⟩
    rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
    · rw [he] at hc1; exact absurd hc1.symm hj'j
    · exact hex1 c' hc'' hne hc1 b hb
  refine ⟨fun dir' j' X' hk' => ?_, fun dir' d'' lay'' hd'' hl'' _ => ?_, fun dir' l hl' => ?_⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [hK] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      exact ⟨lay', hj.log x e c, GMap.lookup_insert_eq .., hlj', hjjr, hX, hcutOnce, hcoh', hcutEx⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
      obtain ⟨lay1, hj1, hl1, hlj1, hj1jr, hX1, honce1, hcoh1, hex1⟩ := hDK.1 dir' j' X' hk'
      have hj'j : j' ≠ lay.j := hlj1 ▸ walsOk_dir_ne hW hexcl hd hl rfl hdd hl1
      obtain ⟨-, -, honce', -, hex'⟩ := hother j' X' hj1 hj'j ⟨hj1jr, hX1, honce1, hcoh1, hex1⟩
      exact ⟨lay1, hj1, hl1, hlj1, hj1jr, hX1, honce', hcoh1, hex'⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl''
      cases hl''
      rw [hd'] at hd''; cases hd''
      exact hcrP
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl''
      rw [hs' dir' hdd] at hd''
      obtain ⟨la, -, -, hla, -, hjr', -, -, -, -⟩ := hW.1 dir' d'' hd''
      rw [hl''] at hla; cases hla
      have hjne := walsOk_dir_ne hW hexcl hd hl rfl hdd hl''
      have hjrne : lay''.jr ≠ lay.j := by rw [hjr']; exact Ne.symm hjjr
      exact crashOkA_purge_other (hDK.2.1 dir' d'' lay'' hd'' hl'' (fun h => by cases h))
        (fun _ h => by cases h) hjne hjrne hcl hcoh hst hbt hothers
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [hlj']
      obtain ⟨X2, hj2, hD2, hx2⟩ := hDK.2.2 _ lay hl
      obtain ⟨hXe, hje⟩ := hD2.eq_of_mem hX hcl
      subst hXe hje
      refine ⟨X, hj.log x e c, ⟨hjjr, hX, hcutOnce, hcoh', hcutEx⟩, hx2.repl fun c' hc' hne _ => ?_⟩
      rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
      · exact absurd he hne
      · exact ⟨hc'', hne0⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      obtain ⟨X', hj1, hk3, hx3⟩ := hDK.2.2 dir' l hl'
      have hj'j := walsOk_dir_ne hW hexcl hd hl rfl hdd hl'
      refine ⟨X', hj1, hother _ X' hj1 hj'j hk3, hx3.mono fun c' hc' hcj _ => ?_⟩
      rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
      · rw [he] at hcj; exact absurd hcj.symm hj'j
      · exact hc''

/-! ## The removed name is the first segment's -/

/-- **The smallest `.wal` name of the directory, not its only one, is the first segment's** (not the last),
and its sequence number is `first` (the handle's bound on it, `walDirLks_purge`, then bounds the segment's
end). -/
theorem purge_first_seg {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {E : Ents}
    {bt : GoString} {i : Ino} {sq ix : Nat}
    (habs : WalAbsD C Mr d lay E) (hsn : SegsNamed lay.segs E) (hnd : (walInos E).Nodup)
    (hcur : E !! bt = some (.file i)) (hbtw : walNameP bt = true)
    (hfirst : ∀ b n, E !! b = some n → walNameP b = true → b = bt ∨ go.GoStringLt bt b)
    (hlast : ∃ b n, E !! b = some n ∧ walNameP b = true ∧ go.GoStringLt bt b)
    (hbt : bt = walFileName sq ix) (hsq : sq < 2 ^ 64) (hcl : lay.cuts.length < 2 ^ 64) :
    ∃ g0 gs, lay.segs = g0 :: gs ∧ gs ≠ [] ∧ i = g0.ino ∧ sq = lay.first := by
  obtain ⟨g0, gs, hs⟩ : ∃ g0 gs, lay.segs = g0 :: gs := by
    cases h : lay.segs with
    | nil => exact absurd h habs.nonempty
    | cons g0 gs => exact ⟨g0, gs, rfl⟩
  have hp := habs.names.2
  rw [hs, List.map_cons, List.pairwise_cons] at hp
  -- a `.wal` name of `E` is a segment's
  have hseg : ∀ b n, E !! b = some n → walNameP b = true → ∃ g ∈ lay.segs, g.name = b := by
    intro b n hb hw
    obtain ⟨i', rfl⟩ := hsn.2 b n hw hb
    have hi := mem_walInos hw hb
    rw [habs.names.1] at hi
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
    exact ⟨g, hg, walName_unique_nd hnd (hsn.1 g hg).1 hw (hsn.1 g hg).2 hb⟩
  have hg0 := hsn.1 g0 (by rw [hs]; simp)
  have hg0n : g0.name = bt := by
    obtain ⟨g, hg, hgn⟩ := hseg bt _ hcur hbtw
    rcases hfirst g0.name _ hg0.2 hg0.1 with h | h
    · exact h
    · rw [hs] at hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · rw [hgn] at h; exact absurd h (go.goStringLt_irrefl _)
      · have := hp.1 _ (List.mem_map_of_mem hg')
        rw [hgn] at this; exact absurd h (go.goStringLt_asymm this)
  have hi : i = g0.ino := by
    rw [hg0n, hcur] at hg0; exact Node.file.inj (Option.some.inj hg0.2)
  have hgs : gs ≠ [] := by
    obtain ⟨b, n, hb, hw, hlt⟩ := hlast
    obtain ⟨g, hg, rfl⟩ := hseg b n hb hw
    rw [hs] at hg
    rcases List.mem_cons.1 hg with rfl | hg'
    · rw [hg0n] at hlt; exact absurd hlt (go.goStringLt_irrefl _)
    · exact List.ne_nil_of_mem hg'
  refine ⟨g0, gs, hs, hgs, hi, ?_⟩
  obtain ⟨ix0, hix0⟩ := habs.seqName 0 g0 (by rw [hs]; rfl)
  rw [hg0n, hbt] at hix0
  have hm := (walFileName_inj hix0).1
  have hlen := habs.cuts.2.2
  rw [hs] at hlen
  have hgl : 1 ≤ gs.length := List.length_pos_iff.2 hgs
  simp only [List.length_cons] at hlen
  rw [Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt (by omega)] at hm
  omega

/-! ## The commit -/

/-- **The pure facts after a purge's removal commit** (see the file header). The old state: the invariant's
pure conjuncts (no cut pending), the WAL `d` of `dir` with its layout `lay` (the first named segment `g0`,
not the last), its key `(j, X)` and claim `(j, .except X, hj)`; `bt` naming `g0` in it; the removal begun
after the claim's last entry; `p` past `g0`'s end. -/
theorem purgeCommit_pure {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {dir : GoString} {d : WalDur} {lay : WalLay} {g0 : SegG} {gs : List SegG} {j : Ino}
    {X : List GoString} {hj : NamesH} {bt : GoString} {x s0 p : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K none) (hK : K !! dir = some (j, X))
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs) (hgs : gs ≠ [])
    (hc0 : ClaimOnce (j, .except X, hj) cl)
    (hcur : hj.cur !! bt = some (.file g0.ino)) (hbtw : walNameP bt = true)
    (hp : segStart lay.cuts (lay.first + 1) ≤ p) (hs0 : hj.next ≤ s0) (hsx : s0 ≤ x) :
    WalsOk C Mr R jr (purSt s dir p (segStart lay.cuts (lay.first + 1))) (<[dir := purgeLayP lay g0]> Ls)
        (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) n ∧
      WalsCreateOk jr (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) ∧
      CreatingOk jr (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) CR ∧
      AbsentNone (purSt s dir p (segStart lay.cuts (lay.first + 1))) jr
        (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) n ∧
      WalsNamed (<[dir := purgeLayP lay g0]> Ls)
        (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) n ∧
      DirKeysOk C Mr jr (purSt s dir p (segStart lay.cuts (lay.first + 1))) (<[dir := purgeLayP lay g0]> Ls)
        (replClaim (j, .except X, hj) (purgeClaim j X hj bt g0.ino x s0) cl) n K none ∧
      lay.j = j ∧ j ≠ jr := by
  classical
  unfold purgeClaim
  obtain ⟨lay1, hj1, hl1, hlj, hjjr, hX, -, hcoh1, hexcl1⟩ := hDK.1 dir j X hK
  rw [hl] at hl1
  cases hl1
  subst hlj
  have hcl : (lay.j, NameSet.except X, hj) ∈ cl := claimOnce_mem hc0
  have hj1e := walClaim_eq hexcl1 hX hcl
  simp only [Prod.mk.injEq, true_and] at hj1e
  subst hj1e
  have hst : hj.next ≤ (rmFileEnt lay.j bt g0.ino s0).start := hs0
  have hbt' : ∀ b, (NameSet.except X).Mem b → (rmFileEnt lay.j bt g0.ino s0).op.Writes lay.j b → b = bt :=
    fun b _ hw => ((rmFileEnt_writes _ _ _ _ _ _).1 hw).2
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl1 c' hc hne hcj bt hbtw
  have hcoh' : ClaimCoh (hj.log x (rmFileEnt lay.j bt g0.ino s0) (purgeNames X bt hj)) lay.j (.except X) := by
    refine claimCoh_log _ _ _ _ _ _ hcoh1 (Nat.le_trans hs0 hsx) (fun b hb hw => ?_)
    have hne : b ≠ bt := fun eb => hw ((rmFileEnt_writes _ _ _ _ _ _).2 ⟨rfl, eb⟩)
    exact purgeNames_lookup hb hne
  -- the old static relation, over the claim's names
  obtain ⟨la, nm, hja, hla, hin, hjr, hnm, ⟨Xa, hXa, hma, -⟩, habs, hfull⟩ := hW.1 dir d hd
  rw [hl] at hla
  cases hla
  have hjae := walClaim_eq hexcl1 hXa hma
  simp only [Prod.mk.injEq, true_and] at hjae
  rw [hjae.2] at habs
  have hnodup := (segsAll_nodup_iff Ls).1 hW.2.2.1
  have hndS := segsAll_nodup_segs hW.2.2.1 hl
  have hwal0 : walInos hj.cur = g0.ino :: gs.map (·.ino) := by rw [habs.names.1, hs]; rfl
  have hwal' : walInos (purgeNames X bt hj) = gs.map (·.ino) := by
    rw [walInos_congr (purgeNames_wal hX)]
    exact walInos_delete_first hbtw hcur hwal0 (by rw [← hwal0, habs.names.1]; exact hndS)
  have hlen : 1 < lay.segs.length := by
    rw [hs]; cases gs with
    | nil => exact absurd rfl hgs
    | cons _ _ => simp
  have habs' : WalAbsD C Mr (walPurgeD d lay p) (purgeLayP lay g0) (purgeNames X bt hj) :=
    walAbsD_purgeP habs hlen hp (by rw [hwal', hs]; rfl)
  have hcr0 := hDK.2.1 dir d lay hd hl (fun h => by cases h)
  have hcrP := crashOkA_full_purge hC hfull hcr0 habs (hnodup.1 dir lay hl) hs hgs hp hX hcl hcoh1 hcoh'
    hst hbt' hothers hcur hwal'
  have hfull' := walFullOk_purge hC hfull hcr0 habs (hnodup.1 dir lay hl) hs hgs hp hX hcl hcoh1 hcoh'
    hst hbt' hothers hcur hwal'
  have hpd : (purSt s dir p (segStart lay.cuts (lay.first + 1))).wal !! dir = some (walPurgeD d lay p) :=
    purSt_self hd
  have hWnew : WalsOk C Mr R jr (purSt s dir p (segStart lay.cuts (lay.first + 1)))
      (<[dir := purgeLayP lay g0]> Ls)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x (rmFileEnt lay.j bt g0.ino s0) (purgeNames X bt hj)) cl)
      n := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
    refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => ?_, segsAll_purge_nodup hl hs h3,
      fun g hg => h4 g ((segsAll_purge_mem hl hs).1 hg), ?_, ?_⟩
    · by_cases hdd : dir' = dir
      · subst hdd
        rw [hpd] at hd'
        cases hd'
        refine ⟨purgeLayP lay g0, nm, _, GMap.lookup_insert_eq .., by rw [purSt_area]; exact hin, hjr, hnm,
          ⟨X, hX, mem_replClaim_new hcl, hcoh'⟩, habs', hfull'⟩
      · rw [purSt_ne hdd] at hd'
        obtain ⟨lay', nm', hj', hl', hin', hjr', hnm', ⟨X', hX', hm', hc'⟩, habs'', hfa⟩ := h1 dir' d' hd'
        have hne := walsOk_dir_ne ⟨h1, h2, h3, h4, h5, h6⟩ hexcl1 hd hl rfl hdd hl'
        have hjrne : lay'.jr ≠ lay.j := by rw [hjr']; exact Ne.symm hjjr
        refine ⟨lay', nm', hj', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hl',
          by rw [purSt_area]; exact hin', hjr', hnm', ⟨X', hX', mem_replClaim_of_ne hm' (fun e => hne (by
            simp only [Prod.mk.injEq] at e; exact e.1)), hc'⟩, habs'',
          walFullOk_purge_other hfa hne hjrne hcl hcoh1 hst hbt' hothers⟩
    · have hdd : dir' ≠ dir := by
        intro e; rw [e, hpd] at hn'; cases hn'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
      exact h2 dir' (purSt_none.1 hn')
    · refine absentOk_of_absentNone ?_
      intro dir' nm' hin' hn'
      exact absentNone_purge hAN hjjr hcl hcoh1 hst hbt' hothers dir' nm'
        (by rw [← purSt_area s dir p (segStart lay.cuts (lay.first + 1))]; exact hin') (purSt_none.1 hn')
    · intro dd hdd
      rw [purSt_dirs] at hdd
      exact dirsOk_purge h6 hcl hcoh1 hst hbt' hcur hothers dd hdd
  refine ⟨hWnew, walsCreateOk_cut hjjr hWC,
    creatingOk_cut hCO hjjr hcl ⟨_, walNameP_wal, except_mem_wal hX⟩,
    fun dir' nm' hin' hn' => absentNone_purge hAN hjjr hcl hcoh1 hst hbt' hothers dir' nm'
      (by rw [← purSt_area s dir p (segStart lay.cuts (lay.first + 1))]; exact hin') (purSt_none.1 hn'),
    walsNamed_purge hW hNm hd hl hs hcl hX hcoh1 hcoh' hexcl1 hst hbt' hcur hbtw hwal',
    dirKeysOk_purge hW hDK hK hd hl hpd (fun k hk => purSt_ne hk) rfl hjjr hX hc0 hcoh1 hcoh' hexcl1 hst
      hbt' hbtw hcrP, rfl, hjjr⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
