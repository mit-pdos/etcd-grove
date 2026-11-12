/-
Iris reasoning principles for the abstract-disk extension (`Impl.lean`; WAL W4a, 2026-11-11, the
approved W4 Draft's §1.2, `notes/decisions.md`, "WAL W4a", and its revision after the Freeze review,
"WAL W4a revision"). Proved: nothing here is trusted.

* **The WALs' state**: one ghost variable of the whole map of WAL directories (`GMap GoString
  WalDur`), half of it in the state interpretation and half the program's, with an exclusive
  token (`walOwn M`), as the durable extension's `durableOwn`: it says which directories hold no
  WAL, which `Create` needs. The per-directory predicates (`walDirIs`, `walDiskAt`, `walAbsent`)
  each hold the whole map (so two of them, even of two directories, are exclusive): the program
  has one WAL directory (the tester's, the server's); a claim operation would be needed to own
  directories separately, since the map has no fragments for the infinitely many directories
  without a WAL.
* **The program's copy is a lower bound in the mark and `named`** (W4a.1 revision 1, 2026-11-12, the
  delta review's B1 and M1; `notes/decisions.md`, "WAL W4a.1 revision 1"): the interpretation holds
  its half of the map at a map below the real one (`walMapLe`: the same directories, every field
  equal but the synced mark and `named`, which the program's copy bounds from below, `walDurLe`),
  and `walDirIs` is closed under lowering them. A body whose atomic update has committed has no
  `walDiskAt` left, yet Go syncs after `Save` writes and fsyncs the parent after `Create`'s rename:
  the steps `"WalSync"` and `"WalNamed"` raise only these two fields, so they have specs from a
  handle's persistent length fact alone (`wp_WalSyncLen`, `wp_WalNamedLen`). The facts
  `walSyncedLb`, `walNamed` are of the real past states, so a client's copy with `named = false`
  next to `walNamed` is consistent (the exact copy made it contradictory: `Create` committed
  `named = false` and then gave `walNamed`, B1). The crash lemmas keep their statements.
* **The WAL area** (`walArea r`, persistent): the state's fixed `area`. The interpretation keeps
  every WAL key in the area (`walKeysInArea`), so `walAbsent dir` of an area directory gives the
  whole of `Create`'s region free (`walCreateRegion_free`): nothing in `Create(area/n)`'s region can
  be a WAL key (`area/n.tmp` and `area/n.broken.*` contain `.`, `area/n/…` has a `/` in the name),
  and no durable directory or durable file is under the area. So the whole-map ownership is no
  longer what makes `Create` sound (cross-key effects are gone, M2 of the Freeze review's aliasing
  lens): a per-directory split (rung 3) would only need the invariant.
* **The start** (`absDiskInitOk`, the adequacy theorem's premise through `initP`): the area clean,
  the WAL keys in it, no durable directory under it, and no WAL (`s0.wal = ∅`, WAL W4a.2 revision 2:
  every WAL history is one the run builds from `Create`, so `Save`'s and `SaveSnapshot`'s index
  premises cover it; a crash's next generation gets the crashed state, not a start); `absDiskStart`
  hands `walOwn s0.wal` (empty) for a concrete `s0`. **W4c gate:** the tester's adequacy quantifies
  `s0` constrained at its own directories (`s0.area = root/data/member`, the real disk empty under the
  area). **C6 gate:** a restart start with a WAL present names its directories by premise (B3-1),
  hands the durable reservation from the start or proves that no durable operation precedes it, and
  needs a stronger start condition than `s0.wal = ∅`: every WAL present "written by etcd at the pin
  from its `Create`, under the `Save`/`SaveSnapshot` premises"; a WAL named by an older etcd does not
  meet it (its names can sit below a snapshot record before them: `walOpenPos` and `ReadAll`'s read
  would be unsound, not only the restart's liveness).
* **Facts** (persistent): `absPast s`, the extension's state was `s` at some point of this
  generation; the state only grows (`absLe`: the area kept, marks, lengths, `named` and the durable
  directories do not decrease, no WAL disappears), so a past state bounds the present one.
  `walSyncedLb`, `walNamed`, `dirDurable`, `walArea` are facts about a past state; `walLenLb w dir n`
  also names a handle of `w` (a persistent handle fact).
* **Handles**: `walOpenW w dir` / `walOpening w dir s` / `walReadFailed w dir`, an exclusive mode
  (`WalMode`) and a persistent `(w, dir)` under a ghost name `γ` that the step allocating the handle
  picks fresh (`walHandle_alloc`), in maps whose authority is in the state interpretation. The
  authority is sealed (`absHandleAuth` is `@[no_expose]`; `absHandle_alloc`/`absHandle_set` and
  their lifted forms are private): outside this file a handle is allocated or its mode changed only
  through the step specs `wp_WalCreate` (`"WalCreate"`), `wp_WalOpenHandle` (`"WalUnlock"`),
  `wp_WalReadFail` (`"WalUnlock"` of 0) and `wp_WalNamedOpen` (`"WalNamed"`), so no freshness of
  `w` is needed. **W4c gate:** a trusted model that performs one of these operations (today only
  the WAL's axiomatized bodies do; the tester's `purgeRound` performs only `"WalPurge"`) is reviewed
  against these specs. Each handle carries one purge right (`walPurgeW`, exclusive), minted with
  it, handed out with `walOpenW` (by `Create`, or by a successful `ReadAll`), consumed by `Close`.
  Per generation: a crash allocates fresh ghost names, so no handle or right survives it.
  **Revision round 3** (the third Freeze review): `walHandleP`, `walOpenW`, `walOpening` and
  `walReadFailed` are sealed (`@[no_expose]`) and the split of a handle into the open WAL and its
  right is private and of append handles only (F1: no right from an opening or failed handle);
  `Open` raises `unl` to `walOpenPos H s.1`, a position at or after the start of the file `Open` locks from (the smaller of `|H|` if an index may wrap (unreachable), else 0 at index 0, else the snapshot record's last position under `walRelGuard`, else `|H|`, and the last position a file named at most `s.1` can start at; WAL W4a.2) (`wp_WalOpenHandle` performs `"WalUnlock"` of that position,
  F1 (b)), so `unl` is current wherever a right exists. **The lock token**
  (`walUnlockedTok`, B2): one per generation (`absDiskStart`, `absDiskCrashStart`), taken by the
  handle a successful `Create`/`Open` allocates, carried by every handle predicate and given back
  only by `Close` (`wp_WalCloseHandle`): at most one handle, so one purge right (M2), per
  generation, and a dropped handle (whose locks Go's finalizers release, losing its buffered
  records) blocks every later `Open` until a crash. `wp_WalCloseHandle` joins the W4c gate's list.
  **W4c gate (M1):** the purge right constrains only through its consumers: the tester's
  `purgeRound` spec must take `walPurgeW w dir` and `walOpenW w dir`, consumed or framed, never
  derived (the extension's `wp_WalPurge` itself requires no right).
* **The steps** (`wp_WalCreate`, ...): one spec per external operation, logically atomic, each
  returning the new state's fact (a WAL above the program's new copy); `wp_WalSyncLen` and
  `wp_WalNamedLen` take no WAL resource.
* **The crash** (`absDisk_crash_interp`): the new generation's ghost state is allocated from the
  crashed state; `absDiskCrashStart old new` holds the old generation's half of the WAL map and its
  facts' authority, and the new generation's half and start fact, with the crash relation between
  them. `walDiskAt_crash` is the Draft's `walDisk_crash` in these terms, `walDiskAt_crash_any` the
  same without `walNamed` (the WAL may vanish).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.CrashAdequacy
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import Perennial.Golang.Defn.PostLang
public import GooseLang.Ext.AbsDisk.Impl

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The state's order -/

instance : Pos.Countable WalDur :=
  .ofInjective (fun d => Pos.Countable.encode
      (d.H, d.m, d.unl, d.pur, d.cut, d.metadata, d.named, d.sized))
    (by intro a b h; cases a; cases b; simp_all)

instance : DecidableEq AbsDiskState := fun a b => Classical.propDecidable (a = b)

instance : Pos.Countable AbsDiskState :=
  .ofInjective (fun s => Pos.Countable.encode (s.area, s.wal, s.dirs))
    (by intro a b h; cases a; cases b; simp_all)

/-- **The state only grows**: the area is kept, no durable directory or WAL disappears, and a WAL's
synced mark, length and `named` do not decrease. -/
def absLe (s s' : AbsDiskState) : Prop :=
  s'.area = s.area ∧
  (∀ d, s.dirs !! d = some () → s'.dirs !! d = some ()) ∧
  ∀ dir d, s.wal !! dir = some d → ∃ d', s'.wal !! dir = some d' ∧
    d.m ≤ d'.m ∧ d.H.length ≤ d'.H.length ∧ (d.named = true → d'.named = true)

theorem absLe_refl (s : AbsDiskState) : absLe s s :=
  ⟨rfl, fun _ h => h, fun _ d h => ⟨d, h, Nat.le_refl _, Nat.le_refl _, id⟩⟩

theorem absLe_trans {s1 s2 s3 : AbsDiskState} (h12 : absLe s1 s2) (h23 : absLe s2 s3) :
    absLe s1 s3 := by
  refine ⟨h23.1.trans h12.1, fun d h => h23.2.1 d (h12.2.1 d h), fun dir d h => ?_⟩
  obtain ⟨d2, h2, hm2, hl2, hn2⟩ := h12.2.2 dir d h
  obtain ⟨d3, h3, hm3, hl3, hn3⟩ := h23.2.2 dir d2 h2
  exact ⟨d3, h3, Nat.le_trans hm2 hm3, Nat.le_trans hl2 hl3, fun x => hn3 (hn2 x)⟩

theorem absDiskUpd_area (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur) :
    (absDiskUpd s dir f).area = s.area := by
  unfold absDiskUpd; cases s.wal !! dir <;> rfl

/-- An update of one WAL that keeps its marks, length and `named` from decreasing. -/
theorem absLe_upd (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur)
    (hf : ∀ d, d.m ≤ (f d).m ∧ d.H.length ≤ (f d).H.length ∧ (d.named = true → (f d).named = true)) :
    absLe s (absDiskUpd s dir f) := by
  unfold absDiskUpd
  cases hd : s.wal !! dir with
  | none => exact absLe_refl s
  | some d0 =>
    refine ⟨rfl, fun _ h => h, fun dir' d h => ?_⟩
    simp only
    by_cases hdir : dir = dir'
    · subst hdir
      rw [hd] at h; cases h
      exact ⟨f d0, by simp [GMap.lookup_insert_eq_iff], hf d0⟩
    · exact ⟨d, by rw [GMap.lookup_insert_eq_iff]; simp [hdir, h], Nat.le_refl _, Nat.le_refl _, id⟩

theorem absDiskUpd_wal (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur) (d : WalDur)
    (hd : s.wal !! dir = some d) : (absDiskUpd s dir f).wal = <[dir := f d]> s.wal := by
  unfold absDiskUpd; rw [hd]

/-- `"WalUnlock"` of position 0 changes nothing. -/
theorem absDiskUpd_unl0 (s : AbsDiskState) (dir : GoString) :
    absDiskUpd s dir (fun d => { d with unl := max d.unl 0 }) = s := by
  unfold absDiskUpd
  cases h : s.wal !! dir with
  | none => rfl
  | some d =>
    have hd : { d with unl := max d.unl 0 } = d := by cases d; simp
    simp only [hd]
    rw [GMap.insert_id _ _ _ h]

/-! ## The program's view: the mark and `named` as lower bounds (W4a.1 revision 1) -/

/-- **`d` is `d'` with its synced mark and `named` bounded from below** (W4a.1 revision 1, the
review's B1 and M1): every other field equal, `d.m ≤ d'.m`, and `d.named` only if `d'.named`. The
program's copy of a WAL (`walDiskAt`) is related to the real one by it: the two fields a body
raises after its atomic update has committed (`Save`'s sync, `Create`'s parent fsync) are lower
bounds, so a step that raises them needs no program resource (`wp_WalSyncLen`, `wp_WalNamedLen`). -/
def walDurLe (d d' : WalDur) : Prop :=
  d.H = d'.H ∧ d.unl = d'.unl ∧ d.pur = d'.pur ∧ d.cut = d'.cut ∧ d.metadata = d'.metadata ∧
  d.sized = d'.sized ∧ d.m ≤ d'.m ∧ (d.named = true → d'.named = true)

theorem walDurLe_refl (d : WalDur) : walDurLe d d :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, id⟩

theorem walDurLe_trans {d1 d2 d3 : WalDur} (h12 : walDurLe d1 d2) (h23 : walDurLe d2 d3) :
    walDurLe d1 d3 :=
  ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, h12.2.2.1.trans h23.2.2.1,
    h12.2.2.2.1.trans h23.2.2.2.1, h12.2.2.2.2.1.trans h23.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h23.2.2.2.2.2.1, Nat.le_trans h12.2.2.2.2.2.2.1 h23.2.2.2.2.2.2.1,
    fun h => h23.2.2.2.2.2.2.2 (h12.2.2.2.2.2.2.2 h)⟩

/-- `walDurLe` on a directory's entry (`none`: no WAL on either side). -/
def walOptLe : Option WalDur → Option WalDur → Prop
  | none, none => True
  | some d, some d' => walDurLe d d'
  | _, _ => False

theorem walOptLe_none_iff (o : Option WalDur) : walOptLe none o ↔ o = none := by
  cases o <;> simp [walOptLe]

theorem walOptLe_some_iff (d : WalDur) (o : Option WalDur) :
    walOptLe (some d) o ↔ ∃ d', o = some d' ∧ walDurLe d d' := by
  cases o <;> simp [walOptLe]

theorem walOptLe_trans {o1 o2 o3 : Option WalDur} (h12 : walOptLe o1 o2) (h23 : walOptLe o2 o3) :
    walOptLe o1 o3 := by
  cases o1 <;> cases o2 <;> cases o3 <;> simp_all [walOptLe]
  exact walDurLe_trans h12 h23

/-- **The WAL map `M` is `M'` up to lower bounds** (the program's map against the real one): the
same directories, each by `walDurLe`. -/
def walMapLe (M M' : GMap GoString WalDur) : Prop :=
  ∀ k, walOptLe (M !! k) (M' !! k)

theorem walMapLe_refl (M : GMap GoString WalDur) : walMapLe M M := by
  intro k; cases M !! k <;> simp [walOptLe, walDurLe_refl]

/-- The real WAL in `dir` raised by `f` (a step the program's map does not see): the program's map
stays below it when `f` keeps every lower bound below. -/
theorem walMapLe_upd (G : GMap GoString WalDur) (s : AbsDiskState) (dir : GoString)
    (f : WalDur → WalDur) (hf : ∀ d0 d, walDurLe d0 d → walDurLe d0 (f d))
    (hG : walMapLe G s.wal) : walMapLe G (absDiskUpd s dir f).wal := by
  intro k
  unfold absDiskUpd
  cases hd : s.wal !! dir with
  | none => exact hG k
  | some d =>
    simp only
    by_cases hk : dir = k
    · subst hk
      rw [GMap.lookup_insert]
      have h := hG dir
      rw [hd] at h
      cases hg : G !! dir with
      | none => rw [hg] at h; exact h.elim
      | some d0 => rw [hg] at h; exact hf d0 d h
    · rw [GMap.lookup_insert_ne _ _ hk]; exact hG k

/-! ## The WAL area -/

/-- **Every WAL directory lies in the area** (the interpretation's invariant). -/
def walKeysInArea (s : AbsDiskState) : Prop :=
  ∀ k d, s.wal !! k = some d → walAreaDir s.area k

theorem walKeysInArea_upd (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur)
    (hk : walKeysInArea s) : walKeysInArea (absDiskUpd s dir f) := by
  intro k d h
  rw [absDiskUpd_area]
  unfold absDiskUpd at h
  cases hd : s.wal !! dir with
  | none => rw [hd] at h; exact hk k d h
  | some d0 =>
    rw [hd] at h
    simp only at h
    by_cases hdir : dir = k
    · subst hdir; exact hk dir d0 hd
    · rw [GMap.lookup_insert_ne _ _ hdir] at h; exact hk k d h

theorem walKeysInArea_crash {s s' : AbsDiskState} (hc : absDisk_semantics.crash s s')
    (hk : walKeysInArea s) : walKeysInArea s' := by
  intro k d' h'
  rw [hc.1]
  cases hs : s.wal !! k with
  | none => rw [hc.2.2.2 k hs] at h'; cases h'
  | some d => exact hk k d hs

private theorem prefix_slash_mem {n n' : GoString} (h : (n ++ go!"/") <+: n') : W8 47 ∈ n' :=
  h.subset (by simp)

/-- **`Create`'s region holds no WAL** when `dir` is an area directory without one: no area key is
`dir.tmp` (it contains `.`), or under `dir/` or `dir.tmp/` (a `/` in the name). -/
theorem walCreateRegion_free {s : AbsDiskState} {dir : GoString} (hk : walKeysInArea s)
    (hdir : walAreaDir s.area dir) (hnone : s.wal !! dir = none) :
    ∀ k, walCreateRegion dir k → s.wal !! k = none := by
  intro k hreg
  cases hs : s.wal !! k with
  | none => rfl
  | some d =>
    exfalso
    obtain ⟨n', ⟨-, hn1', hn2'⟩, rfl⟩ := hk k d hs
    obtain ⟨n, -, rfl⟩ := hdir
    unfold walCreateRegion underDir at hreg
    simp only [List.append_assoc] at hreg
    rcases hreg with h | h | h | h
    · have := List.append_cancel_left (List.append_cancel_left h)
      subst this
      rw [hnone] at hs; cases hs
    · exact hn1' (prefix_slash_mem ((List.prefix_append_right_inj _).1
        ((List.prefix_append_right_inj _).1 h)))
    · have := List.append_cancel_left (List.append_cancel_left h)
      subst this
      exact hn2' (by simp)
    · have h' := (List.prefix_append_right_inj _).1 ((List.prefix_append_right_inj _).1 h)
      rw [← List.append_assoc] at h'
      exact hn1' (prefix_slash_mem h')

/-! ## Ghost state -/

/-- **A handle's mode**: ready to append, opened for reading at a snapshot, or failed (its
`ReadAll` returned an error: only `Close` accepts it). -/
inductive WalMode where
  | append
  | opening (s : w64 × w64)
  | failed

instance : Pos.Countable WalMode :=
  .ofInjective (fun m => Pos.Countable.encode (match m with
      | .append => (none : Option (Option (w64 × w64)))
      | .opening s => some (some s)
      | .failed => some none))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- What the adequacy theorem provides: the universal camera. -/
class AbsDiskGpreS (GF : BundledGFunctors) where
  absDiskPreAllG : AllG GF

/-- The ghost names of one generation. -/
structure AbsDiskGS (GF : BundledGFunctors) where
  absDiskAllG : AllG GF
  /-- The ghost variable of the WAL map. -/
  γs : GName
  /-- The program's exclusive token of the WAL map. -/
  γt : GName
  /-- The past states (persistent elements). -/
  γf : GName
  /-- The area (a persistent element at `()`). -/
  γa : GName
  /-- The handles' modes (exclusive elements, keyed by the handle's ghost name). -/
  γh : GName
  /-- The handles' locations and directories (persistent elements, keyed by the handle's ghost
  name). -/
  γhd : GName
  /-- The handles' purge rights (exclusive elements at `()`, keyed by the handle's ghost name). -/
  γhp : GName
  /-- The generation's lock token (`walUnlockedTok`, a `token`): allocated once per generation, at
  its start; every handle carries it. -/
  γu : GName

section ghost
variable {GF : BundledGFunctors}

/-- **The WAL map is `M`** (the program's half, with the token). -/
def walOwnAt (hL : AbsDiskGS GF) (M : GMap GoString WalDur) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(ghostVar hL.γs (1 : Qp).half M ∗ token hL.γt)

/-- **The state was `s` at some point of this generation** (persistent; with its area). -/
def absPastAt (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(s ↪[hL.γf]□ () ∗ () ↪[hL.γa]□ s.area)

instance absPastAt_persistent (hL : AbsDiskGS GF) (s : AbsDiskState) :
    Persistent (absPastAt hL s) := by
  unfold absPastAt; infer_instance

/-- The authority of the past states, all below `s`, and `s`'s area. -/
def absPastAuth (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(∃ F : GMap AbsDiskState Unit, ghostMapAuth hL.γf 1 F ∗
    ([∗map] p ↦ _u ∈ F, p ↪[hL.γf]□ ()) ∗ ⌜∀ p, F !! p = some () → absLe p s⌝ ∗
    () ↪[hL.γa]□ s.area)

/-- The handles' authorities, every ghost name from `n` on unused. Sealed (`@[no_expose]`, WAL W4a
revision round 2, M-1): outside this file only the step specs below allocate a handle or change its
mode (`absHandle_alloc`, `absHandle_set` and their lifted forms are private). -/
@[no_expose] def absHandleAuth (hL : AbsDiskGS GF) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(∃ (n : Nat) (Hh : GMap GName WalMode) (Hd : GMap GName (Loc × GoString))
      (Hp : GMap GName Unit),
    ghostMapAuth hL.γh 1 Hh ∗ ghostMapAuth hL.γhd 1 Hd ∗ ghostMapAuth hL.γhp 1 Hp ∗
    ⌜∀ k, n ≤ k → Hh !! k = none ∧ Hd !! k = none ∧ Hp !! k = none⌝)

/-- **The interpretation of the state `s`**: the WAL map's other half, at a map below `s`'s (each
WAL's mark and `named` lower bounds of the real ones, `walMapLe`; W4a.1 revision 1), the past states
(all below `s`), the handles' authorities, every WAL directory in the area. -/
def absDiskCtx (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop((∃ G : GMap GoString WalDur, ghostVar hL.γs (1 : Qp).half G ∗ ⌜walMapLe G s.wal⌝) ∗
    absPastAuth hL s ∗ absHandleAuth hL ∗ ⌜walKeysInArea s⌝)

/-- What the program starts with: the WAL map, the start state's fact (which gives the area,
`absPast_walArea`) and the generation's lock token (no handle exists yet). -/
def absDiskStart (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(walOwnAt hL s.wal ∗ absPastAt hL s ∗ token hL.γu)

theorem absPast_le (hL : AbsDiskGS GF) (s p : AbsDiskState) :
    ⊢@{IProp GF} absPastAuth hL s -∗ absPastAt hL p -∗ ⌜absLe p s⌝ := by
  letI := hL.absDiskAllG
  unfold absPastAuth absPastAt
  iintro ⟨%F, HA, -, %Hle, -⟩ ⟨#Hp, -⟩
  icases ghost_map_lookup $$ HA Hp with %Hl
  ipureintro; exact Hle p Hl

/-- The past states' authority at a bigger state. -/
theorem absPast_grow (hL : AbsDiskGS GF) (s s' : AbsDiskState) (hle : absLe s s') :
    ⊢@{IProp GF} absPastAuth hL s -∗ absPastAuth hL s' := by
  letI := hL.absDiskAllG
  unfold absPastAuth
  iintro ⟨%F, HA, HE, %Hle, #Ha⟩
  iexists F
  iframe HA HE
  isplitr
  · ipureintro; exact fun p hp => absLe_trans (Hle p hp) hle
  · rw [hle.1]; iexact Ha

/-- The present state's fact. -/
theorem absPast_snap (hL : AbsDiskGS GF) (s : AbsDiskState) :
    ⊢@{IProp GF} absPastAuth hL s ==∗ absPastAuth hL s ∗ absPastAt hL s := by
  letI := hL.absDiskAllG
  unfold absPastAuth absPastAt
  iintro ⟨%F, HA, #HE, %Hle, #Ha⟩
  cases hF : F !! s with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := F)
      (Φ := fun p _ => iprop(p ↪[hL.γf]□ ())) hF).1 $$ HE with ⟨#Hs, -⟩
    imodintro
    isplitl [HA]
    · iexists F; iframe HA HE Ha; ipureintro; exact Hle
    · isplitl; iexact Hs; iexact Ha
  | none =>
    imod ghost_map_insert_persist s () hF $$ HA with ⟨HA, #Hs⟩
    imodintro
    isplitl [HA]
    · iexists (F.insert s ())
      iframe HA Ha
      isplitl
      · iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := F)
          (Φ := fun p _ => iprop(p ↪[hL.γf]□ ())) hF).2
        iframe HE; iexact Hs
      · ipureintro
        intro p hp
        rw [GMap.lookup_insert_eq_iff] at hp
        by_cases hps : s = p
        · subst hps; exact absLe_refl s
        · simp only [hps, ite_false] at hp; exact Hle p hp
    · isplitl; iexact Hs; iexact Ha

/-- **A new handle** of `w` in `dir` in mode `m`, under a fresh ghost name, with its purge right. -/
private theorem absHandle_alloc (hL : AbsDiskGS GF) (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} absHandleAuth hL ==∗ absHandleAuth hL ∗
      ∃ γ : GName, (letI := hL.absDiskAllG; γ ↪[hL.γhd]□ (w, dir)) ∗
        (letI := hL.absDiskAllG; γ ↪[hL.γh] m) ∗ (letI := hL.absDiskAllG; γ ↪[hL.γhp] ()) := by
  letI := hL.absDiskAllG
  unfold absHandleAuth
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩
  obtain ⟨h1, h2, h3⟩ := Hf n (Nat.le_refl n)
  imod ghost_map_insert n m h1 $$ HA with ⟨HA, Hm⟩
  imod ghost_map_insert_persist n (w, dir) h2 $$ HD with ⟨HD, #Hdir⟩
  imod ghost_map_insert n () h3 $$ HP with ⟨HP, Hpt⟩
  imodintro
  isplitl [HA HD HP]
  · iexists (n + 1), (Hh.insert n m), (Hd.insert n (w, dir)), (Hp.insert n ())
    iframe HA HD HP
    ipureintro
    intro k hk
    have hne : n ≠ k := by omega
    obtain ⟨h1', h2', h3'⟩ := Hf k (by omega)
    exact ⟨by rw [GMap.lookup_insert_ne _ _ hne]; exact h1',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h2',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h3'⟩
  · iexists n; iframe Hdir Hm Hpt

/-- **A handle's mode changed.** -/
private theorem absHandle_set (hL : AbsDiskGS GF) (γ : GName) (m m' : WalMode) :
    ⊢@{IProp GF} absHandleAuth hL -∗ (letI := hL.absDiskAllG; γ ↪[hL.γh] m) ==∗ absHandleAuth hL ∗
      (letI := hL.absDiskAllG; γ ↪[hL.γh] m') := by
  letI := hL.absDiskAllG
  unfold absHandleAuth
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩ Hm
  icases ghost_map_lookup $$ HA Hm with %Hl
  imod ghost_map_update m' $$ HA Hm with ⟨HA, Hm⟩
  imodintro
  iframe Hm
  iexists n, (Hh.insert γ m'), Hd, Hp
  iframe HA HD HP
  ipureintro
  intro k hk
  obtain ⟨h1, h2, h3⟩ := Hf k hk
  have hne : γ ≠ k := by
    rintro rfl
    have : Hh !! γ = some m := Hl
    rw [h1] at this; cases this
  exact ⟨by rw [GMap.lookup_insert_ne _ _ hne]; exact h1, h2, h3⟩

theorem absDisk_local_init (hPre : AbsDiskGpreS GF) (s : AbsDiskState) (hk : walKeysInArea s) :
    ⊢@{IProp GF} |==> ∃ hL : AbsDiskGS GF, absDiskCtx hL s ∗ absDiskStart hL s := by
  letI := hPre.absDiskPreAllG
  imod ghostVar_alloc (GF := GF) s.wal with ⟨%γs, Hs⟩
  icases (ghostVar_split_half γs 1 _).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod (ghost_map_alloc (GF := GF) (GMap.singleton s ())) with ⟨%γf, HF, HFe⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Unit) (V := GoString)) with ⟨%γa, Ha⟩
  imod ghost_map_insert_persist (GF := GF) () s.area (GMap.lookup_empty _) $$ Ha with ⟨-, #Ha⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := WalMode)) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Loc × GoString)) with ⟨%γhd, Hhd⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Unit)) with ⟨%γhp, Hhp⟩
  imod token_alloc (GF := GF) with ⟨%γu, Hu⟩
  let hL : AbsDiskGS GF := ⟨hPre.absDiskPreAllG, γs, γt, γf, γa, γh, γhd, γhp, γu⟩
  have hsing : (GMap.singleton s () : GMap AbsDiskState Unit) = (∅ : GMap _ _).insert s () := rfl
  rw [hsing]
  icases (BigSepM.bigSepM_insert (PROP := IProp GF) (m := (∅ : GMap AbsDiskState Unit))
    (Φ := fun p v => iprop(p ↪[γf] v)) rfl).1 $$ HFe with ⟨Hse, -⟩
  imod ghostMapElem_persist $$ Hse with #Hse
  imodintro
  iexists hL
  isplitl [Hs1 HF Hh Hhd Hhp]
  · unfold absDiskCtx absPastAuth absHandleAuth
    isplitl [Hs1]
    · iexists s.wal; iframe Hs1; ipureintro; exact walMapLe_refl _
    isplitl [HF]
    · iexists ((∅ : GMap AbsDiskState Unit).insert s ())
      iframe HF Ha
      isplitl
      · iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := (∅ : GMap AbsDiskState Unit))
          (Φ := fun p _ => iprop(p ↪[γf]□ ())) rfl).2
        iframe Hse
        iapply BigSepM.bigSepM_empty.2; itrivial
      · ipureintro
        intro p hp
        rw [GMap.lookup_insert_eq_iff] at hp
        by_cases hps : s = p
        · subst hps; exact absLe_refl s
        · simp [hps, GMap.lookup_empty] at hp
    · isplitl [Hh Hhd Hhp]
      · iexists 0, ∅, ∅, ∅; iframe Hh Hhd Hhp; ipureintro; intro k _; exact ⟨rfl, rfl, rfl⟩
      · ipureintro; exact hk
  · unfold absDiskStart walOwnAt absPastAt
    iframe Hs2 Ht Hse Ha Hu

end ghost

/-- The ghost state of the abstract disk. The program gets the whole WAL map and the start
state's fact (as the durable extension's `durableOwn`); the adequacy theorem covers only starts
meeting `absDiskInitOk`. -/
instance absDisk_interp : ExtInterp absDiskExt where
  LocalGS := AbsDiskGS
  GlobalGS _ := Unit
  localCtx := absDiskCtx
  globalCtx _ _ := iprop(True)
  PreG := AbsDiskGpreS
  initgP _ := True
  initP s _ := absDiskInitOk s
  globalStart _ _ := iprop(True)
  localStart := absDiskStart
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre s _ h := absDisk_local_init hPre s h.2.1

/-! ## The crash -/

section crash
variable {GF : BundledGFunctors}

/-- **What a crash hands the next generation, but its lock token**: the old generation's half of
the WAL map, below `s`'s, and its past states' authority (all below `s`), the new generation's half of the
map at `s'` and `s'`'s fact, with `s'` a crash of `s`. -/
def absDiskCrashWal (hL hL' : AbsDiskGS GF) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(∃ s s' : AbsDiskState, ⌜absDisk_semantics.crash s s'⌝ ∗
    (∃ G : GMap GoString WalDur, ghostVar hL.γs (1 : Qp).half G ∗ ⌜walMapLe G s.wal⌝) ∗
    absPastAuth hL s ∗
    walOwnAt hL' s'.wal ∗ absPastAt hL' s')

/-- **What a crash hands the next generation**: `absDiskCrashWal` and the new generation's lock
token (the crash ended every handle: the process died). -/
def absDiskCrashStart (hL hL' : AbsDiskGS GF) : IProp GF :=
  iprop(absDiskCrashWal hL hL' ∗ (letI := hL'.absDiskAllG; token hL'.γu))

theorem absDisk_local_crash (hPre : AbsDiskGpreS GF) (hL : AbsDiskGS GF) (s s' : AbsDiskState)
    (hc : absDisk_semantics.crash s s') :
    ⊢@{IProp GF} absDiskCtx hL s ==∗ ∃ hL' : AbsDiskGS GF, absDiskCtx hL' s' ∗
      absDiskCrashStart hL hL' := by
  iintro Hctx
  iunfold absDiskCtx at Hctx
  icases Hctx with ⟨Hs, HP, -, %hk⟩
  imod absDisk_local_init hPre s' (walKeysInArea_crash hc hk) with ⟨%hL', Hctx', Hst'⟩
  imodintro
  iexists hL'
  iframe Hctx'
  unfold absDiskCrashStart absDiskCrashWal absDiskStart
  icases Hst' with ⟨HM', Hp', Hu'⟩
  iframe Hu'
  iexists s, s'
  iframe Hs HP HM' Hp'
  ipureintro; exact hc

/-- The crash interpretation of the abstract disk. -/
instance absDisk_crash_interp : ExtCrashInterp absDiskExt where
  crashStart hL hL' := absDiskCrashStart hL hL'
  local_crash _ hPre hL s s' hc := absDisk_local_crash hPre hL s s' hc

end crash

/-! ## The program's predicates -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {st : Stuckness} {E : CoPset}

abbrev gooseAbsDiskGS : AbsDiskGS GF := extLocalGS absDiskExt

/-- **The program owns the WAL map, which is `M`.** -/
def walOwn (M : GMap GoString WalDur) : IProp GF := walOwnAt (gooseAbsDiskGS (L := L)) M

/-- **The state was `s` at some point of this generation** (persistent). -/
def absPast (s : AbsDiskState) : IProp GF := absPastAt (gooseAbsDiskGS (L := L)) s

instance absPast_persistent (s : AbsDiskState) : Persistent (absPast (L := L) s) := by
  unfold absPast; infer_instance

/-- **The WAL area is `r`** (persistent; the state's `area`, which no step changes). -/
def walArea (r : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, absPast (L := L) s ∗ ⌜s.area = r⌝)

/-- **The WAL directory `dir` holds `o`** (`none`: no WAL; the whole map's ownership, see the
header), **its mark and `named` as lower bounds** (W4a.1 revision 1: `walOptLe`, so the predicate
is closed under lowering them, and a step that raises the real ones needs no program resource). -/
def walDirIs (dir : GoString) (o : Option WalDur) : IProp GF :=
  iprop(∃ M : GMap GoString WalDur, walOwn (L := L) M ∗ ⌜walOptLe o (M !! dir)⌝)

/-- **The WAL in `dir` is in the durable state `d`** (the extension's points-to): `d`'s history,
flag, purge positions, read position and metadata exactly; its synced mark at least `d.m`, and its
entry durable if `d.named` (W4a.1 revision 1: a body syncs and names after its atomic update has
committed, through `wp_WalSyncLen` and `wp_WalNamedLen`, which raise only the real values). -/
def walDiskAt (dir : GoString) (d : WalDur) : IProp GF := walDirIs (L := L) dir (some d)

/-- **`dir` names no WAL.** -/
def walAbsent (dir : GoString) : IProp GF := walDirIs (L := L) dir none

/-- **The first `n` operations of `dir`'s history are synced** (persistent). -/
def walSyncedLb (dir : GoString) (n : Nat) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (d : WalDur), absPast (L := L) s ∗ ⌜s.wal !! dir = some d ∧ n ≤ d.m⌝)

/-- **`dir`'s WAL entry, and its ancestors', are durable** (persistent; `Create`'s post fact). -/
def walNamed (dir : GoString) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (d : WalDur), absPast (L := L) s ∗
    ⌜s.wal !! dir = some d ∧ d.named = true⌝)

/-- **`d`'s entry and its ancestors' are durable** (persistent). -/
def dirDurable (d : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, absPast (L := L) s ∗ ⌜s.dirs !! d = some ()⌝)

/-- **The handle named `γ` is of the `*wal.WAL` `w`, which writes the WAL in `dir`**
(persistent). -/
def walHandleDir (w : Loc) (dir : GoString) (γ : GName) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  γ ↪[(gooseAbsDiskGS (L := L)).γhd]□ (w, dir)

/-- **`w` is a handle of the WAL in `dir`, in mode `m`** (exclusive). -/
def walHandleSt (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(∃ γ : GName, walHandleDir (L := L) w dir γ ∗ γ ↪[(gooseAbsDiskGS (L := L)).γh] m)

/-- **The open WAL `w` has written its directory `dir`'s history up to length `n`** (persistent; per
generation): what `Sync` takes. It names `dir`, so that it agrees with a `walOpenW w dir` without any
freshness of `w` (the handles are keyed by ghost names). -/
def walLenLb (w : Loc) (dir : GoString) (n : Nat) : IProp GF :=
  iprop(∃ (γ : GName) (s : AbsDiskState) (d : WalDur),
    walHandleDir (L := L) w dir γ ∗ absPast (L := L) s ∗ ⌜s.wal !! dir = some d ∧ n ≤ d.H.length⌝)

/-- **The generation's lock token** (exclusive; WAL W4a revision round 3, B2): allocated once per
generation (`absDiskStart`, `absDiskCrashStart`), consumed by a successful `Create` or `Open`,
carried by the handle (`walOpenW`, `walOpening`, `walReadFailed`) and returned only by `Close`. So
at most one handle exists per generation, and a handle the program drops takes the token with it: no
second `Open` or `Create` is provable until a crash. (Go releases a dropped `*WAL`'s locks through
`os.File` finalizers, without `Close`, and its buffered records are lost: Go test
`TestRev3LeakedHandleThenOpen`.) No lemma mints it: `token_alloc` gives a fresh name only. The
token is area-wide, not per directory: at most one WAL handle exists across all the area's
directories (enough for etcd and the tester, one WAL each; several WALs per process need a token
keyed per directory, a rung-3/C6 gate). -/
def walUnlockedTok : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  token (gooseAbsDiskGS (L := L)).γu

instance walUnlockedTok_timeless : Timeless (walUnlockedTok (L := L)) := by
  unfold walUnlockedTok; infer_instance

theorem walUnlockedTok_excl :
    ⊢@{IProp GF} walUnlockedTok (L := L) -∗ walUnlockedTok (L := L) -∗ False := by
  unfold walUnlockedTok
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- **`w` is a handle of the WAL in `dir`, in mode `m`, with its purge right and the generation's
lock token** (exclusive). Sealed (`@[no_expose]`, revision round 3, F1): outside this file the
right and the token are not separable from the handle. -/
@[no_expose] def walHandleP (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(∃ γ : GName, walHandleDir (L := L) w dir γ ∗ γ ↪[(gooseAbsDiskGS (L := L)).γh] m ∗
    γ ↪[(gooseAbsDiskGS (L := L)).γhp] () ∗ walUnlockedTok (L := L))

/-- **The purge's right on the open WAL `w` in `dir`** (exclusive: one per handle, minted with it, and
per generation, so it does not survive a crash; WAL W4a revision round 2, replacing the server's
opaque `walPurgeRight` in the extension's axioms): the purge of old WAL files there may run only
while it is held, and `Close` (which unlocks every file) consumes it with the handle. It is handed
out only with `walOpenW` (by `Create`, by a successful `ReadAll`: the handle predicates that carry it
before that are sealed, revision round 3, F1); while it is held, every record from the WAL's `unl`
on is in a file the handle keeps locked (`Open` raises `unl` to `walOpenPos H s.1`, a position at or after the start of the file `Open` locks from (the smaller of `|H|` if an index may wrap (unreachable), else 0 at index 0, else the snapshot record's last position under `walRelGuard`, else `|H|`, and the last position a file named at most `s.1` can start at; WAL W4a.2),
`ReleaseLockTo` to `walReleasePos` of its index too). With the lock token (`walUnlockedTok`) at most
one handle, so one right, is live per generation; so `Close` and `wp_WalCloseHandle` need not ask
that the `walOpenW` and `walPurgeW` they consume share a ghost name: no other right is outstanding. **W4c gate:** the tester's `purgeRound` spec takes
`walPurgeW w dir` and `walOpenW w dir`, consumed or framed, never derived. -/
def walPurgeW (w : Loc) (dir : GoString) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(∃ γ : GName, walHandleDir (L := L) w dir γ ∗ γ ↪[(gooseAbsDiskGS (L := L)).γhp] ())

/-- **`w` is the WAL opened in `dir`, ready to append** (exclusive; with the generation's lock
token, which only `Close` returns). Sealed (`@[no_expose]`, revision round 3, B2). -/
@[no_expose] def walOpenW (w : Loc) (dir : GoString) : IProp GF :=
  iprop(walHandleSt (L := L) w dir .append ∗ walUnlockedTok (L := L))

/-- **`w` is the WAL opened in `dir` for reading at the snapshot `s`** (exclusive; with the handle's
purge right, which a successful `ReadAll` hands out, and the lock token). Sealed (`@[no_expose]`,
revision round 3, F1). -/
@[no_expose] def walOpening (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  walHandleP (L := L) w dir (.opening s)

/-- **`w`'s `ReadAll` in `dir` failed** (exclusive): only `Close` accepts it. Sealed
(`@[no_expose]`, revision round 3, F1). -/
@[no_expose] def walReadFailed (w : Loc) (dir : GoString) : IProp GF :=
  walHandleP (L := L) w dir .failed

instance walArea_persistent (r : GoString) : Persistent (walArea (L := L) r) := by
  unfold walArea; infer_instance
instance walSyncedLb_persistent (dir : GoString) (n : Nat) :
    Persistent (walSyncedLb (L := L) dir n) := by unfold walSyncedLb; infer_instance
instance walNamed_persistent (dir : GoString) : Persistent (walNamed (L := L) dir) := by
  unfold walNamed; infer_instance
instance dirDurable_persistent (d : GoString) : Persistent (dirDurable (L := L) d) := by
  unfold dirDurable; infer_instance
instance walHandleDir_persistent (w : Loc) (dir : GoString) (γ : GName) :
    Persistent (walHandleDir (L := L) w dir γ) := by unfold walHandleDir; infer_instance
instance walLenLb_persistent (w : Loc) (dir : GoString) (n : Nat) :
    Persistent (walLenLb (L := L) w dir n) := by
  unfold walLenLb; infer_instance

instance walOwn_timeless (M : GMap GoString WalDur) : Timeless (walOwn (L := L) M) := by
  unfold walOwn walOwnAt; infer_instance
instance walDirIs_timeless (dir : GoString) (o : Option WalDur) :
    Timeless (walDirIs (L := L) dir o) := by unfold walDirIs; infer_instance
instance walDiskAt_timeless (dir : GoString) (d : WalDur) : Timeless (walDiskAt (L := L) dir d) := by
  unfold walDiskAt; infer_instance
instance walAbsent_timeless (dir : GoString) : Timeless (walAbsent (L := L) dir) := by
  unfold walAbsent; infer_instance

/-! ### Laws -/

/-- **The program's copy may be lowered** (W4a.1 revision 1): a WAL known above `d'` is known above
`d` when `d` bounds `d'` from below. -/
theorem walDiskAt_weaken (dir : GoString) (d d' : WalDur) (h : walDurLe d d') :
    ⊢@{IProp GF} walDiskAt (L := L) dir d' -∗ walDiskAt (L := L) dir d := by
  unfold walDiskAt walDirIs
  iintro ⟨%M, HM, %HMd⟩
  iexists M; iframe HM; ipureintro
  exact walOptLe_trans (o2 := some d') h HMd

/-- **One owner of the WAL map** (so of any WAL directory). -/
theorem walOwn_excl (M M' : GMap GoString WalDur) :
    ⊢@{IProp GF} walOwn (L := L) M -∗ walOwn (L := L) M' -∗ False := by
  unfold walOwn walOwnAt
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  iapply token_exclusive $$ H1 H2

theorem walDirIs_excl (dir dir' : GoString) (o o' : Option WalDur) :
    ⊢@{IProp GF} walDirIs (L := L) dir o -∗ walDirIs (L := L) dir' o' -∗ False := by
  unfold walDirIs
  iintro ⟨%M, H1, -⟩ ⟨%M', H2, -⟩
  iapply walOwn_excl $$ H1 H2

theorem walSyncedLb_mono (dir : GoString) (n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walSyncedLb (L := L) dir n -∗ walSyncedLb (L := L) dir n' := by
  unfold walSyncedLb
  iintro ⟨%s, %d, Hs, %Hd⟩
  iexists s, d; iframe Hs; ipureintro; exact ⟨Hd.1, Nat.le_trans h Hd.2⟩

theorem walLenLb_mono (w : Loc) (dir : GoString) (n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walLenLb (L := L) w dir n -∗ walLenLb (L := L) w dir n' := by
  unfold walLenLb
  iintro ⟨%γ, %s, %d, Hw, Hs, %Hd⟩
  iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨Hd.1, Nat.le_trans h Hd.2⟩

theorem walHandleDir_agree (w w' : Loc) (dir dir' : GoString) (γ : GName) :
    ⊢@{IProp GF} walHandleDir (L := L) w dir γ -∗ walHandleDir (L := L) w' dir' γ -∗
      ⌜w = w' ∧ dir = dir'⌝ := by
  unfold walHandleDir
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro #H1 #H2
  icases ghostMapElem_agree $$ H1 H2 with %H
  ipureintro; exact Prod.mk.inj H

/-- An open handle's length fact, from a past state of its directory. -/
theorem walOpenW_lenLb (w : Loc) (dir : GoString) (s : AbsDiskState) (d : WalDur) (n : Nat)
    (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpenW (L := L) w dir -∗ absPast (L := L) s -∗
      walOpenW (L := L) w dir ∗ walLenLb (L := L) w dir n := by
  unfold walOpenW walHandleSt walLenLb
  iintro ⟨⟨%γ, #Hw, Hm⟩, Hu⟩ #Hs
  isplitl [Hm Hu]
  · iframe Hu; iexists γ; iframe Hw Hm
  · iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨hd, hn⟩

/-- An opened handle's length fact, from a past state of its directory (W4a.1 revision 1, for an
atomic `ReadAll`'s body: it syncs after its commit from the handle's fact). -/
theorem walOpening_lenLb (w : Loc) (dir : GoString) (sn : w64 × w64) (s : AbsDiskState) (d : WalDur)
    (n : Nat) (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpening (L := L) w dir sn -∗ absPast (L := L) s -∗
      walOpening (L := L) w dir sn ∗ walLenLb (L := L) w dir n := by
  unfold walOpening walHandleP walLenLb
  iintro ⟨%γ, #Hw, Hm, Hp, Hu⟩ #Hs
  isplitl [Hm Hp Hu]
  · iexists γ; iframe Hw Hm Hp Hu
  · iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨hd, hn⟩

/-- Two facts of the area agree. -/
theorem walArea_agree (r r' : GoString) :
    ⊢@{IProp GF} walArea (L := L) r -∗ walArea (L := L) r' -∗ ⌜r = r'⌝ := by
  unfold walArea absPast absPastAt
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨%p, ⟨-, #Hp⟩, %hp⟩ ⟨%q, ⟨-, #Hq⟩, %hq⟩
  icases ghostMapElem_agree $$ Hp Hq with %H
  ipureintro; rw [← hp, ← hq]; exact H

/-- A past state's area. -/
theorem absPast_walArea (s : AbsDiskState) :
    ⊢@{IProp GF} absPast (L := L) s -∗ walArea (L := L) s.area := by
  unfold walArea
  iintro #Hs
  iexists s; iframe Hs; ipureintro; rfl

theorem absDisk_local_ctx_eq (s : AbsDiskState) :
    ExtInterp.localCtx (E := absDiskExt) (extLocalGS absDiskExt) s ⊣⊢
      absDiskCtx (gooseAbsDiskGS (L := L)) s := .rfl

/-- What the program's WAL map says of the interpretation's: it is below the real one. -/
theorem walOwn_agree (s : AbsDiskState) (M : GMap GoString WalDur) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walOwn (L := L) M -∗
      ⌜walMapLe M s.wal⌝ := by
  unfold absDiskCtx walOwn walOwnAt
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨⟨%G, Hs, %HG⟩, -⟩ ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  ipureintro; subst HMG; exact HG

/-- What a past state says of the present one. -/
theorem absPast_ctx_le (s p : AbsDiskState) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ absPast (L := L) p -∗ ⌜absLe p s⌝ := by
  unfold absDiskCtx absPast
  iintro ⟨-, HP, -⟩ Hp
  iapply absPast_le $$ HP Hp

/-- The area under the interpretation. -/
theorem walArea_ctx (s : AbsDiskState) (r : GoString) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walArea (L := L) r -∗ ⌜s.area = r⌝ := by
  unfold walArea
  iintro Hc ⟨%p, Hp, %hp⟩
  icases absPast_ctx_le $$ Hc Hp with %Hle
  ipureintro; rw [Hle.1, hp]

/-- The interpretation's invariant: every WAL directory in the area. -/
theorem absDiskCtx_keys (s : AbsDiskState) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ ⌜walKeysInArea s⌝ := by
  unfold absDiskCtx
  iintro ⟨-, -, -, %hk⟩
  ipureintro; exact hk

/-- **A new handle** with its purge right, taking the generation's lock token (inside a step: the
interpretation holds the handles' authorities). Private: only the step specs of this file allocate
handles. -/
private theorem walHandle_alloc (s : AbsDiskState) (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walUnlockedTok (L := L) ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ walHandleP (L := L) w dir m := by
  unfold absDiskCtx walHandleP walHandleDir
  iintro ⟨Hs, HP, HH, Hk⟩ Hu
  imod absHandle_alloc _ w dir m $$ HH with ⟨HH, ⟨%γ, Hd, Hm, Hp⟩⟩
  imodintro
  iframe Hs HP HH Hk
  iexists γ; iframe Hd Hm Hp Hu

/-- **A handle's mode changed**, its purge right kept (inside a step). Private. -/
private theorem walHandleP_set (s : AbsDiskState) (w : Loc) (dir : GoString) (m m' : WalMode) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walHandleP (L := L) w dir m ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ walHandleP (L := L) w dir m' := by
  unfold absDiskCtx walHandleP
  iintro ⟨Hs, HP, HH, Hk⟩ ⟨%γ, #Hd, Hm, Hp, Hu⟩
  imod absHandle_set _ γ m m' $$ HH Hm with ⟨HH, Hm⟩
  imodintro
  iframe Hs HP HH Hk
  iexists γ; iframe Hd Hm Hp Hu

/-- An append handle with its purge right is the open WAL and the right. Private, and only of mode
`append` (revision round 3, F1: the right is handed out only with `walOpenW`). -/
private theorem walHandleP_split (w : Loc) (dir : GoString) :
    ⊢@{IProp GF} walHandleP (L := L) w dir .append -∗ walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir := by
  unfold walHandleP walOpenW walHandleSt walPurgeW
  iintro ⟨%γ, #Hd, Hm, Hp, Hu⟩
  isplitl [Hm Hu]
  · iframe Hu; iexists γ; iframe Hd Hm
  · iexists γ; iframe Hd Hp

/-- **A closed handle gives back the lock token** (private: only `Close`'s step, `wp_WalCloseHandle`,
does it). -/
private theorem walHandle_close (w : Loc) (dir : GoString) (s : w64 × w64) :
    ⊢@{IProp GF} ((walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir) ∨ walOpening (L := L) w dir s ∨
      walReadFailed (L := L) w dir) -∗ walUnlockedTok (L := L) := by
  unfold walOpenW walOpening walReadFailed walHandleP
  iintro (⟨⟨-, Hu⟩, -⟩ | ⟨%γ, -, -, -, Hu⟩ | ⟨%γ, -, -, -, Hu⟩) <;> iexact Hu

/-- **One purge right per handle.** -/
theorem walPurgeW_excl (w : Loc) (dir : GoString) (γ : GName) :
    ⊢@{IProp GF} (letI := (gooseAbsDiskGS (L := L)).absDiskAllG;
      γ ↪[(gooseAbsDiskGS (L := L)).γhp] ()) -∗
      (letI := (gooseAbsDiskGS (L := L)).absDiskAllG; γ ↪[(gooseAbsDiskGS (L := L)).γhp] ()) -∗
      False := by
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro H1 H2
  icases ghostMapElem_valid_2 γ _ (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2 with %Hv
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- **The interpretation at a bigger state** (a step's ghost update): the WAL map set to the new
state's, the past states kept, and the new state's fact. -/
theorem absDisk_upd (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walOwn (L := L) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ walOwn (L := L) s'.wal ∗
      absPast (L := L) s' := by
  iintro Hc HM
  icases walOwn_agree $$ Hc HM with %HMs
  unfold absDiskCtx walOwn walOwnAt absPast
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro
  icases Hc with ⟨⟨%G, Hs, -⟩, HP, Hh, %Hk⟩
  icases HM with ⟨HM, Ht⟩
  imod ghostVar_update_halves s'.wal _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe HM Ht HP Hh Hp Hs
  isplitr
  · ipureintro; exact HMs
  isplitr
  · ipureintro; exact walMapLe_refl _
  ipureintro; exact hk Hk

/-- **The interpretation at a bigger state, the program's map unchanged** (W4a.1 revision 1): a step
that raises only lower-bounded fields (or the durable directories) needs no WAL map, when the map
below `s`'s stays below `s'`'s. -/
theorem absDisk_upd_lag (s s' : AbsDiskState) (hlag : ∀ G, walMapLe G s.wal → walMapLe G s'.wal)
    (hle : absLe s s') (hk : walKeysInArea s → walKeysInArea s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ absPast (L := L) s' := by
  iintro Hc
  unfold absDiskCtx absPast
  icases Hc with ⟨⟨%G, Hs, %HG⟩, HP, Hh, %Hk⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe HP Hh Hp
  isplitl [Hs]
  · iexists G; iframe Hs; ipureintro; exact hlag G HG
  ipureintro; exact hk Hk

/-- The same for a step that changes only the durable directories. -/
theorem absDisk_upd_dirs (s s' : AbsDiskState) (hw : s'.wal = s.wal) (hle : absLe s s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ absPast (L := L) s' :=
  absDisk_upd_lag s s' (fun G h => by rw [hw]; exact h) hle
    (fun Hk k d h => by rw [hle.1]; rw [hw] at h; exact Hk k d h)

/-! ## The steps -/

/-- **A deterministic step** `op` of `v`, which goes from `s` to `f s` when `P s` holds: its spec
in terms of the interpretation (the client's ghost update at the step). -/
theorem wp_absDisk_step (op : String) (v : val) (P : AbsDiskState → Prop)
    (f : AbsDiskState → AbsDiskState) (hv : v.isPanic = false)
    (Hprog : ∀ h s g, P s → AbsDiskStep op v h s g (Val #()) h (f s) g)
    (Hdet : ∀ h s g e' h' s' g', AbsDiskStep op v h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = f s) (Φ : val → IProp GF) :
    (|={E,∅}=> ∀ s, absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗ ⌜P s⌝ ∗
        absDiskCtx (gooseAbsDiskGS (L := L)) (f s) ∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep op v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  imod HAU with HAU
  icases (absDisk_local_ctx_eq σ).mp $$ Hl with Hl
  imod HAU $$ Hl with ⟨%HP, Hl, Hclose⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, f σ, g, Hprog h σ g HP⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, rfl, rfl⟩ := Hdet _ _ _ _ _ _ _ Hst
  imod Hclose with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (absDisk_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

/-- A WAL step of `dir` that updates its WAL by `upd` (no change if there is none), with a ghost
update `R ==∗ R'` under the interpretation at the step (a handle's allocation or mode change). The
program's copy `d` is a lower bound of the real WAL (W4a.1 revision 1): `upd` keeps the relation
(`hmono`), its precondition `Pd` transfers to the real WAL (`hPd`), and the new state's fact names
a WAL above `upd d`. -/
theorem wp_absDisk_walStepR (op : String) (v : val) (dir : GoString) (upd : WalDur → WalDur)
    (Pd : WalDur → Prop) (hv : v.isPanic = false)
    (hf : ∀ d, d.m ≤ (upd d).m ∧ d.H.length ≤ (upd d).H.length ∧
      (d.named = true → (upd d).named = true))
    (hmono : ∀ d d', walDurLe d d' → walDurLe (upd d) (upd d'))
    (hPd : ∀ d d', walDurLe d d' → Pd d → Pd d')
    (Hprog : ∀ h s g, (∀ d, s.wal !! dir = some d → Pd d) →
      AbsDiskStep op v h s g (Val #()) h (absDiskUpd s dir upd) g)
    (Hdet : ∀ h s g e' h' s' g', AbsDiskStep op v h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir upd)
    (R R' : IProp GF)
    (Hupd : ∀ s, ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ R ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ R')
    (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ d : WalDur, ⌜Pd d⌝ ∗ walDiskAt (L := L) dir d ∗ R ∗
      (walDiskAt (L := L) dir (upd d) -∗ R' -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe (upd d) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  unfold walDiskAt walDirIs
  iintro HAU
  iapply wp_absDisk_step op v (fun s => ∀ d2, s.wal !! dir = some d2 → Pd d2)
    (fun s => absDiskUpd s dir upd) hv Hprog Hdet
  imod HAU with ⟨%d, %Hd, ⟨%M, HM, %HMd⟩, HR, Hk⟩
  imodintro
  iintro %s Hc
  imod absDisk_upd s (absDiskUpd s dir upd) M (absLe_upd s dir upd hf)
    (walKeysInArea_upd s dir upd) $$ Hc HM with ⟨%HMs, Hc, HM, #Hp⟩
  obtain ⟨dg, hdg, hle1⟩ := (walOptLe_some_iff d _).1 HMd
  have h2 := HMs dir
  rw [hdg] at h2
  obtain ⟨dr, hdr, hle2⟩ := (walOptLe_some_iff dg _).1 h2
  have hle := walDurLe_trans hle1 hle2
  imod Hupd _ $$ Hc HR with ⟨Hc, HR⟩
  have hw := absDiskUpd_wal s dir upd dr hdr
  have hl : (absDiskUpd s dir upd).wal !! dir = some (upd dr) := by
    rw [hw]; exact GMap.lookup_insert _ _ _
  imodintro
  isplitr
  · ipureintro; intro d2 hd2; rw [hdr] at hd2; cases hd2; exact hPd d _ hle Hd
  iframe Hc
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗
      ⌜walOptLe (some (upd d)) (M' !! dir)⌝) $$ [HM]
  · iexists (absDiskUpd s dir upd).wal; iframe HM; ipureintro
    rw [hl]; exact hmono _ _ hle
  iapply Hk $$ Hd HR Hp
  ipureintro; exact ⟨upd dr, hl, hmono _ _ hle⟩

/-- `wp_absDisk_walStepR` with the program's copy `d` given. -/
theorem wp_absDisk_walStepR1 (op : String) (v : val) (dir : GoString) (upd : WalDur → WalDur)
    (Pd : WalDur → Prop) (hv : v.isPanic = false)
    (hf : ∀ d, d.m ≤ (upd d).m ∧ d.H.length ≤ (upd d).H.length ∧
      (d.named = true → (upd d).named = true))
    (hmono : ∀ d d', walDurLe d d' → walDurLe (upd d) (upd d'))
    (hPd : ∀ d d', walDurLe d d' → Pd d → Pd d')
    (Hprog : ∀ h s g, (∀ d, s.wal !! dir = some d → Pd d) →
      AbsDiskStep op v h s g (Val #()) h (absDiskUpd s dir upd) g)
    (Hdet : ∀ h s g e' h' s' g', AbsDiskStep op v h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir upd) (d : WalDur) (Hd : Pd d)
    (R R' : IProp GF)
    (Hupd : ∀ s, ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ R ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ R')
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗ R ∗
      (walDiskAt (L := L) dir (upd d) -∗ R' -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe (upd d) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_walStepR op v dir upd Pd hv hf hmono hPd Hprog Hdet R R' Hupd Φ
  imod HAU with ⟨HD, HR, Hk⟩
  imodintro
  iexists d
  isplitr
  · ipureintro; exact Hd
  iframe HD HR Hk

/-- A WAL step of `dir` that updates its WAL by `upd` (no change if there is none). -/
theorem wp_absDisk_walStep (op : String) (v : val) (dir : GoString) (upd : WalDur → WalDur)
    (Pd : WalDur → Prop) (hv : v.isPanic = false)
    (hf : ∀ d, d.m ≤ (upd d).m ∧ d.H.length ≤ (upd d).H.length ∧
      (d.named = true → (upd d).named = true))
    (hmono : ∀ d d', walDurLe d d' → walDurLe (upd d) (upd d'))
    (hPd : ∀ d d', walDurLe d d' → Pd d → Pd d')
    (Hprog : ∀ h s g, (∀ d, s.wal !! dir = some d → Pd d) →
      AbsDiskStep op v h s g (Val #()) h (absDiskUpd s dir upd) g)
    (Hdet : ∀ h s g e' h' s' g', AbsDiskStep op v h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir upd) (d : WalDur) (Hd : Pd d)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir (upd d) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe (upd d) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_walStepR1 op v dir upd Pd hv hf hmono hPd Hprog Hdet d Hd iprop(True) iprop(True)
    (fun s => by iintro Hc -; imodintro; iframe Hc) Φ
  imod HAU with ⟨Hd, Hk⟩
  imodintro
  iframe Hd
  isplitr
  · itrivial
  · iintro Hd -
    iapply Hk $$ Hd

/-- The lower-bound relation is kept by the steps' updates. -/
theorem walDurLe_upd_H (o : WalOpG WalEnt) {d d' : WalDur} (h : walDurLe d d') :
    walDurLe { d with H := d.H ++ [o] } { d' with H := d'.H ++ [o] } :=
  ⟨by simp only [h.1], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem walDurLe_upd_named {d d' : WalDur} (h : walDurLe d d') :
    walDurLe { d with named := true } { d' with named := true } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, fun _ => rfl⟩

theorem walDurLe_upd_m (n : Nat) {d d' : WalDur} (h : walDurLe d d') :
    walDurLe { d with m := max d.m n } { d' with m := max d'.m n } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    Nat.max_le.2 ⟨Nat.le_trans h.2.2.2.2.2.2.1 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩, h.2.2.2.2.2.2.2⟩

theorem walDurLe_upd_unl (p : Nat) {d d' : WalDur} (h : walDurLe d d') :
    walDurLe { d with unl := max d.unl p } { d' with unl := max d'.unl p } :=
  ⟨h.1, by simp only [h.2.1], h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem walDurLe_upd_purge (k : Nat) {d d' : WalDur} (h : walDurLe d d') :
    walDurLe { d with pur := max d.pur d.unl, cut := k } { d' with pur := max d'.pur d'.unl, cut := k } :=
  ⟨h.1, h.2.1, by simp only [h.2.1, h.2.2.1], rfl, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

/-! ### The WAL steps, one by one -/

theorem wp_WalAppend (dir : GoString) (o : WalOpG WalEnt) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir { d with H := d.H ++ [o] } -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe { d with H := d.H ++ [o] } d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalAppend" (Val (PairV (#dir) (#(walCode o))))) @ st; E
      {{ Φ }} := by
  refine wp_absDisk_walStep "WalAppend" _ dir (fun d => { d with H := d.H ++ [o] }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, by simp, id⟩)
    (fun _ _ h => walDurLe_upd_H o h) (fun _ _ _ _ => trivial) ?_ ?_ d trivial Φ
  · intro h s g _
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, o, ?_, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', o', Hv, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩

/-- `"WalAppend"` with the program's copy found at the access (a body that opens an atomic update
at the step: `Save`, `SaveSnapshot`). -/
theorem wp_WalAppendAcc (dir : GoString) (o : WalOpG WalEnt) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ d : WalDur, walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir { d with H := d.H ++ [o] } -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe { d with H := d.H ++ [o] } d'⌝ -∗
          ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalAppend" (Val (PairV (#dir) (#(walCode o))))) @ st; E
      {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_walStepR "WalAppend" _ dir (fun d => { d with H := d.H ++ [o] }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, by simp, id⟩)
    (fun _ _ h => walDurLe_upd_H o h) (fun _ _ _ _ => trivial) ?_ ?_ iprop(True) iprop(True)
    (fun s => by iintro Hc -; imodintro; iframe Hc) Φ
  · intro h s g _
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, o, ?_, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', o', Hv, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩
  · imod HAU with ⟨%d, HD, Hk⟩
    imodintro
    iexists d
    isplitr
    · ipureintro; trivial
    iframe HD
    isplitr
    · itrivial
    · iintro Hd -
      iapply Hk $$ Hd

/-- The `"WalNamed"` step's program and determinism. -/
private theorem walNamed_prog (dir : GoString) :
    (∀ h s g, (∀ d, s.wal !! dir = some d → True) →
      AbsDiskStep "WalNamed" (#dir) h s g (Val #()) h
        (absDiskUpd s dir (fun d => { d with named := true })) g) ∧
    (∀ h s g e' h' s' g', AbsDiskStep "WalNamed" (#dir) h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir (fun d => { d with named := true })) := by
  refine ⟨?_, ?_⟩
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, ?_, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', Hv, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
    exact ⟨rfl, rfl, rfl⟩

theorem wp_WalNamed (dir : GoString) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with named := true }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with named := true }) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} :=
  wp_absDisk_walStep "WalNamed" _ dir (fun d => { d with named := true }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)
    (fun _ _ h => walDurLe_upd_named h) (fun _ _ _ _ => trivial) (walNamed_prog dir).1 (walNamed_prog dir).2 d trivial Φ

/-- `"WalNamed"` of `dir` that also turns the handle `w`, opened for reading at `s`, into one ready
to append (a successful write-mode `ReadAll`'s last step). -/
theorem wp_WalNamedOpen (w : Loc) (dir : GoString) (s : w64 × w64) (d : WalDur)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗ walOpening (L := L) w dir s ∗
      (walDiskAt (L := L) dir ({ d with named := true }) -∗
        (walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir) -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with named := true }) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} :=
  wp_absDisk_walStepR1 "WalNamed" _ dir (fun d => { d with named := true }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)
    (fun _ _ h => walDurLe_upd_named h) (fun _ _ _ _ => trivial) (walNamed_prog dir).1 (walNamed_prog dir).2 d trivial
    (walOpening (L := L) w dir s) iprop(walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir)
    (fun s' => by
      unfold walOpening
      iintro Hc Hh
      imod walHandleP_set s' w dir (.opening s) .append $$ Hc Hh with ⟨Hc, Hh⟩
      imodintro
      iframe Hc
      iapply walHandleP_split $$ Hh) Φ

theorem wp_WalSync (dir : GoString) (n : Nat) (d : WalDur) (Hn : n ≤ d.H.length) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with m := max d.m n }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with m := max d.m n }) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode n))))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalSync" _ dir (fun d => { d with m := max d.m n }) (fun d => n ≤ d.H.length)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_max_left _ _, Nat.le_refl _, id⟩)
    (fun _ _ h => walDurLe_upd_m n h) (fun _ _ h hn => by rw [← h.1]; exact hn) ?_ ?_ d Hn Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, n, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', n', Hv, -, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩

/-- The `"WalUnlock"` step's program and determinism. -/
private theorem walUnlock_prog (dir : GoString) (p : Nat) :
    (∀ h s g, AbsDiskStep "WalUnlock" (PairV (#dir) (#(walCode p))) h s g (Val #()) h
        (absDiskUpd s dir (fun d => { d with unl := max d.unl p })) g) ∧
    (∀ h s g e' h' s' g', AbsDiskStep "WalUnlock" (PairV (#dir) (#(walCode p))) h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir (fun d => { d with unl := max d.unl p })) := by
  refine ⟨?_, ?_⟩
  · intro h s g
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, p, ?_, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', p', Hv, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩

theorem wp_WalUnlock (dir : GoString) (p : Nat) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with unl := max d.unl p }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with unl := max d.unl p }) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode p))))) @ st; E {{ Φ }} :=
  wp_absDisk_walStep "WalUnlock" _ dir (fun d => { d with unl := max d.unl p }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)
    (fun _ _ h => walDurLe_upd_unl p h) (fun _ _ _ _ => trivial)
    (fun h s g _ => (walUnlock_prog dir p).1 h s g) (walUnlock_prog dir p).2 d trivial Φ

/-- **A no-op step** (`"WalUnlock"` of position 0, which changes nothing), with a ghost update
`R ==∗ R'` under the interpretation at the step: what a body that allocates a handle or changes
its mode without another step performs (`Open`, a failed `ReadAll`). -/
theorem wp_WalNoop (dir : GoString) (R R' : IProp GF)
    (Hupd : ∀ s, ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ R ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ R')
    (Φ : val → IProp GF) :
    (|={E,∅}=> R ∗ (R' -∗ ▷ |={∅,E}=> Φ #()))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode (0 : Nat))))))
      @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_step "WalUnlock" _ (fun _ => True)
    (fun s => absDiskUpd s dir (fun d => { d with unl := max d.unl 0 })) (by simp [val.isPanic])
    (fun h s g _ => (walUnlock_prog dir 0).1 h s g) (walUnlock_prog dir 0).2
  imod HAU with ⟨HR, Hk⟩
  imodintro
  iintro %s Hc
  rw [absDiskUpd_unl0]
  imod Hupd s $$ Hc HR with ⟨Hc, HR⟩
  imodintro
  isplitr
  · ipureintro; trivial
  iframe Hc
  iapply Hk $$ HR

/-- **`Open`'s handle** (revision round 3: F1 (b), B2): the `"WalUnlock"` step of `p` (`Open`'s
axiom passes `walOpenPos H s.1`, a position at or after the start of the file `Open` locks from (the smaller of `|H|` if an index may wrap (unreachable), else 0 at index 0, else the snapshot record's last position under `walRelGuard`, else `|H|`, and the last position a file named at most `s.1` can start at; WAL W4a.2); every record from it on is in a file `Open` locks), which
allocates the handle `w`, opened in `dir` for reading at `s`, taking the generation's lock token. -/
theorem wp_WalOpenHandle (w : Loc) (dir : GoString) (s : w64 × w64) (p : Nat) (d : WalDur)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗ walUnlockedTok (L := L) ∗
      (walDiskAt (L := L) dir ({ d with unl := max d.unl p }) -∗ walOpening (L := L) w dir s -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with unl := max d.unl p }) d'⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode p))))) @ st; E
      {{ Φ }} :=
  wp_absDisk_walStepR1 "WalUnlock" _ dir (fun d => { d with unl := max d.unl p }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)
    (fun _ _ h => walDurLe_upd_unl p h) (fun _ _ _ _ => trivial)
    (fun h s g _ => (walUnlock_prog dir p).1 h s g) (walUnlock_prog dir p).2 d trivial
    (walUnlockedTok (L := L)) (walOpening (L := L) w dir s)
    (fun s' => by unfold walOpening; iapply walHandle_alloc s' w dir (.opening s)) Φ

/-- **`Close`'s handle** (revision round 3, B2): a no-op step that consumes the handle `w` (open with
its purge right, opening, or failed) and gives back the generation's lock token. The open WAL and
the purge right need not share a ghost name: the token allows at most one outstanding right per
generation. -/
theorem wp_WalCloseHandle (w : Loc) (dir : GoString) (s : w64 × w64) (Φ : val → IProp GF) :
    (|={E,∅}=> ((walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir) ∨ walOpening (L := L) w dir s ∨
        walReadFailed (L := L) w dir) ∗ (walUnlockedTok (L := L) -∗ ▷ |={∅,E}=> Φ #()))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode (0 : Nat))))))
      @ st; E {{ Φ }} :=
  wp_WalNoop dir _ (walUnlockedTok (L := L))
    (fun s' => by
      iintro Hc Hh
      ihave Hu := walHandle_close w dir s $$ Hh
      imodintro
      iframe Hc Hu) Φ

/-- **A failed `ReadAll`**: a no-op step that turns the handle `w`, opened for reading, into a
failed one. -/
theorem wp_WalReadFail (w : Loc) (dir : GoString) (s : w64 × w64) (Φ : val → IProp GF) :
    (|={E,∅}=> walOpening (L := L) w dir s ∗ (walReadFailed (L := L) w dir -∗ ▷ |={∅,E}=> Φ #()))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode (0 : Nat))))))
      @ st; E {{ Φ }} :=
  wp_WalNoop dir (walOpening (L := L) w dir s) (walReadFailed (L := L) w dir)
    (fun s' => walHandleP_set s' w dir (.opening s) .failed) Φ

/-- `"WalPurge"` of `(dir, k)`: `pur` raised to `unl`, the read position moved to `k`, the start
of the first file the round left. -/
theorem wp_WalPurge (dir : GoString) (k : Nat) (d : WalDur) (Hk : d.cut ≤ k ∧ k ≤ max d.pur d.unl)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with pur := max d.pur d.unl, cut := k }) -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜∃ d', s'.wal !! dir = some d' ∧ walDurLe ({ d with pur := max d.pur d.unl, cut := k }) d'⌝ -∗
            ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalPurge" (Val (PairV (#dir) (#(walCode k))))) @ st; E
      {{ Φ }} := by
  refine wp_absDisk_walStep "WalPurge" _ dir (fun d => { d with pur := max d.pur d.unl, cut := k })
    (fun d => d.cut ≤ k ∧ k ≤ max d.pur d.unl)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)
    (fun _ _ h => walDurLe_upd_purge k h)
    (fun _ _ h hk => by rw [← h.2.2.2.1, ← h.2.2.1, ← h.2.1]; exact hk) ?_ ?_ d Hk Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, k, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', k', Hv, -, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩

/-- `"WalCreate"` of `(dir, md)`, `dir` a directory of the area `r`: a fresh WAL where there was
none (the rest of `Create`'s region is then free too, `walCreateRegion_free`), and the handle `w`
ready to append. -/
theorem wp_WalCreate (w : Loc) (r dir : GoString) (md : List w8) (hdir : walAreaDir r dir)
    (Φ : val → IProp GF) :
    walArea (L := L) r ∗ walUnlockedTok (L := L) ∗
    (|={E,∅}=> walAbsent (L := L) dir ∗
      (walDiskAt (L := L) dir (walDurFresh md) -∗ walOpenW (L := L) w dir -∗ walPurgeW (L := L) w dir -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜s'.wal !! dir = some (walDurFresh md)⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalCreate" (Val (PairV (#dir) (#md)))) @ st; E {{ Φ }} := by
  unfold walAbsent walDiskAt walDirIs
  iintro ⟨#HA, Hu, HAU⟩
  have hle : ∀ s : AbsDiskState, s.wal !! dir = none →
      absLe s { s with wal := <[dir := walDurFresh md]> s.wal } := by
    intro s hs
    refine ⟨rfl, fun _ h => h, fun dir' d h => ⟨d, ?_, Nat.le_refl _, Nat.le_refl _, id⟩⟩
    have hne : dir ≠ dir' := by rintro rfl; rw [hs] at h; cases h
    simp only; rw [GMap.lookup_insert_ne _ _ hne]; exact h
  have hkeys : ∀ s : AbsDiskState, walAreaDir s.area dir → walKeysInArea s →
      walKeysInArea { s with wal := <[dir := walDurFresh md]> s.wal } := by
    intro s hd hk k d h
    simp only at h ⊢
    by_cases hne : dir = k
    · subst hne; exact hd
    · rw [GMap.lookup_insert_ne _ _ hne] at h; exact hk k d h
  iapply wp_absDisk_step "WalCreate" _
    (fun s => walAreaDir s.area dir ∧ ∀ k, walCreateRegion dir k → s.wal !! k = none)
    (fun s => { s with wal := <[dir := walDurFresh md]> s.wal }) (by simp [val.isPanic])
  · intro h s g hs
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, md, ?_, hs.1, hs.2, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', md', Hv, -, -, rfl⟩ := Hst
    obtain ⟨Hd, Hm⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := go.intoVal_inj Hm
    exact ⟨rfl, rfl, rfl⟩
  imod HAU with ⟨⟨%M, HM, %HMd⟩, Hk⟩
  imodintro
  iintro %s Hc
  icases walOwn_agree $$ Hc HM with %HMs
  icases walArea_ctx $$ Hc HA with %Har
  icases absDiskCtx_keys $$ Hc with %Hks
  have hs : s.wal !! dir = none := by
    have h := HMs dir
    rw [(walOptLe_none_iff _).1 HMd] at h
    exact (walOptLe_none_iff _).1 h
  have hds : walAreaDir s.area dir := by rw [Har]; exact hdir
  imod absDisk_upd s _ M (hle s hs) (hkeys s hds) $$ Hc HM with ⟨-, Hc, HM, #Hp⟩
  imod walHandle_alloc _ w dir .append $$ Hc Hu with ⟨Hc, Hw⟩
  icases walHandleP_split $$ Hw with ⟨Hw, Hpw⟩
  have hl : (<[dir := walDurFresh md]> s.wal) !! dir = some (walDurFresh md) := GMap.lookup_insert _ _ _
  imodintro
  isplitr
  · ipureintro; exact ⟨hds, walCreateRegion_free Hks hds hs⟩
  iframe Hc
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗
      ⌜walOptLe (some (walDurFresh md)) (M' !! dir)⌝) $$ [HM]
  · iexists _; iframe HM; ipureintro; rw [hl]; exact walDurLe_refl _
  iapply Hk $$ Hd Hw Hpw Hp
  ipureintro; exact hl

/-- `"DirDurable"` of `d`, a directory not under the area `r`: `d`'s entry and its ancestors'
durable (no WAL map needed). -/
theorem wp_DirDurable (r d : GoString) (hd : ¬ underDir r d) (Φ : val → IProp GF) :
    walArea (L := L) r ∗ (|={E,∅}=> dirDurable (L := L) d -∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "DirDurable" (Val (#d))) @ st; E {{ Φ }} := by
  iintro ⟨#HA, HAU⟩
  iapply wp_absDisk_step "DirDurable" _ (fun s => ¬ underDir s.area d)
    (fun s => { s with dirs := <[d := ()]> s.dirs }) (by simp [val.isPanic])
  · intro h s g hs
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, d, ?_, hs, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, d', Hv, -, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
    exact ⟨rfl, rfl, rfl⟩
  imod HAU with Hk
  imodintro
  iintro %s Hc
  icases walArea_ctx $$ Hc HA with %Har
  have hle : absLe s { s with dirs := <[d := ()]> s.dirs } := by
    refine ⟨rfl, fun d' h => ?_, fun dir dd h => ⟨dd, h, Nat.le_refl _, Nat.le_refl _, id⟩⟩
    simp only
    by_cases hd : d = d'
    · subst hd; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ hd]; exact h
  imod absDisk_upd_dirs s { s with dirs := <[d := ()]> s.dirs } rfl hle $$ Hc with ⟨Hc, #Hp⟩
  imodintro
  isplitr
  · ipureintro; rw [Har]; exact hd
  iframe Hc
  iapply Hk
  unfold dirDurable
  iexists _; iframe Hp; ipureintro; exact GMap.lookup_insert _ _ _

/-! ### Steps from a handle's facts alone (W4a.1 revision 1, the review's M1)

A body whose atomic update has committed holds no `walDiskAt`: the client's update took it. Go's
`Save` syncs after it has written (the commit), and `Create` fsyncs the parent after the rename (the
commit). These two steps raise only fields the program's copy bounds from below (the mark,
`named`), so they need no program resource: only a persistent fact that the WAL exists and is long
enough (`walLenLb`, which the handle gives, `walOpenW_lenLb`). -/

/-- The real WAL in `dir` raised by `f` keeps the program's map below it, and the state grows. -/
private theorem absDisk_raise (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur)
    (hf : ∀ d0 d, walDurLe d0 d → walDurLe d0 (f d))
    (hg : ∀ d, d.m ≤ (f d).m ∧ d.H.length ≤ (f d).H.length ∧
      (d.named = true → (f d).named = true)) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) (absDiskUpd s dir f) ∗
      absPast (L := L) (absDiskUpd s dir f) :=
  absDisk_upd_lag s _ (fun G hG => walMapLe_upd G s dir f hf hG) (absLe_upd s dir f hg)
    (walKeysInArea_upd s dir f)

/-- **`"WalSync"` of `n` from a handle's length fact alone**: what `Save`'s and `SaveSnapshot`'s
bodies perform after their commit, and `Sync`'s body. -/
theorem wp_WalSyncLen (w : Loc) (dir : GoString) (n : Nat) (Φ : val → IProp GF) :
    walLenLb (L := L) w dir n ∗ (|={E,∅}=> walSyncedLb (L := L) dir n -∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode n))))) @ st; E
      {{ Φ }} := by
  unfold walLenLb
  iintro ⟨⟨%γ, %p, %dp, -, #Hp, %Hdp⟩, HAU⟩
  iapply wp_absDisk_step "WalSync" _ (fun s => ∃ d, s.wal !! dir = some d ∧ n ≤ d.H.length)
    (fun s => absDiskUpd s dir (fun d => { d with m := max d.m n })) (by simp [val.isPanic])
  · intro h s g ⟨d, hs, hn⟩
    simp only [AbsDiskStep]
    refine ⟨trivial, trivial, dir, n, rfl, fun d' hd' => ?_, rfl⟩
    rw [hs] at hd'; cases hd'; exact hn
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', n', Hv, -, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩
  imod HAU with HAU
  imodintro
  iintro %s Hc
  icases absPast_ctx_le $$ Hc Hp with %Hle
  obtain ⟨d, hd, -, hlen, -⟩ := Hle.2.2 dir dp Hdp.1
  imod absDisk_raise s dir (fun d => { d with m := max d.m n })
    (fun d0 d h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      Nat.le_trans h.2.2.2.2.2.2.1 (Nat.le_max_left _ _), h.2.2.2.2.2.2.2⟩)
    (fun d => ⟨Nat.le_max_left _ _, Nat.le_refl _, id⟩) $$ Hc with ⟨Hc, #Hp'⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨d, hd, Nat.le_trans Hdp.2 hlen⟩
  iframe Hc
  iapply HAU
  unfold walSyncedLb
  iexists _, { d with m := max d.m n }
  iframe Hp'
  ipureintro
  refine ⟨?_, Nat.le_max_right _ _⟩
  rw [absDiskUpd_wal s dir _ d hd]; exact GMap.lookup_insert _ _ _

/-- **`"WalNamed"` from a handle's fact alone**: what `Create`'s body performs after its commit (the
parent's fsync after the rename). -/
theorem wp_WalNamedLen (w : Loc) (dir : GoString) (n : Nat) (Φ : val → IProp GF) :
    walLenLb (L := L) w dir n ∗ (|={E,∅}=> walNamed (L := L) dir -∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} := by
  unfold walLenLb
  iintro ⟨⟨%γ, %p, %dp, -, #Hp, %Hdp⟩, HAU⟩
  iapply wp_absDisk_step "WalNamed" _ (fun _ => True)
    (fun s => absDiskUpd s dir (fun d => { d with named := true })) (by simp [val.isPanic])
    (fun h s g _ => (walNamed_prog dir).1 h s g (fun _ _ => trivial)) (walNamed_prog dir).2
  imod HAU with HAU
  imodintro
  iintro %s Hc
  icases absPast_ctx_le $$ Hc Hp with %Hle
  obtain ⟨d, hd, -, -, -⟩ := Hle.2.2 dir dp Hdp.1
  imod absDisk_raise s dir (fun d => { d with named := true })
    (fun d0 d h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, fun _ => rfl⟩)
    (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩) $$ Hc with ⟨Hc, #Hp'⟩
  imodintro
  isplitr
  · ipureintro; trivial
  iframe Hc
  iapply HAU
  unfold walNamed
  iexists _, { d with named := true }
  iframe Hp'
  ipureintro
  refine ⟨?_, rfl⟩
  rw [absDiskUpd_wal s dir _ d hd]; exact GMap.lookup_insert _ _ _

/-! ## The crash, in a generation's terms -/

section crashGen
variable (L' : GooseLocalGS GF)

/-- **The crash start is the WAL part and the new generation's lock token.** -/
theorem absDiskCrashStart_split :
    absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) ⊣⊢
      absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) ∗
        walUnlockedTok (L := L') := by
  unfold absDiskCrashStart walUnlockedTok; exact .rfl

/-- What the crash start says of the old generation's WAL map: it is below the crashed state's
(W4a.1 revision 1: the mark and `named` lower bounds, `walMapLe`). -/
theorem absDisk_crash_view (M : GMap GoString WalDur) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walOwn (L := L) M -∗ ∃ s s' : AbsDiskState, ⌜absDisk_semantics.crash s s' ∧ walMapLe M s.wal⌝ ∗
        absPastAuth (gooseAbsDiskGS (L := L)) s ∗ walOwn (L := L') s'.wal ∗ absPast (L := L') s' := by
  unfold absDiskCrashWal walOwn absPast
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨%s, %s', %hc, ⟨%G, Hs, %HG⟩, HP, HM', Hp'⟩ HM
  unfold walOwnAt
  icases HM with ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMs
  iexists s, s'
  iframe HP HM' Hp'
  ipureintro; subst HMs; exact ⟨hc, HG⟩

/-- The program's copy of the WAL in `dir` is below a real one (from the crash view). -/
theorem walDiskAt_crash_real {M : GMap GoString WalDur} {s : AbsDiskState} {dir : GoString}
    {d : WalDur} (HMd : walOptLe (some d) (M !! dir)) (HMs : walMapLe M s.wal) :
    ∃ dr, s.wal !! dir = some dr ∧ walDurLe d dr := by
  obtain ⟨dg, hdg, hle1⟩ := (walOptLe_some_iff d _).1 HMd
  have h2 := HMs dir
  rw [hdg] at h2
  obtain ⟨dr, hdr, hle2⟩ := (walOptLe_some_iff dg _).1 h2
  exact ⟨dr, hdr, walDurLe_trans hle1 hle2⟩

/-- A crash's new WAL is above the program's copy with the crash's fields. -/
theorem walDurLe_crash {d dr : WalDur} {I : List (WalOpG WalEnt)} {k : Nat} (hle : walDurLe d dr) :
    walDurLe { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
      { dr with H := I, cut := k, unl := min dr.unl I.length, pur := min dr.pur I.length } :=
  ⟨rfl, by simp only [hle.2.1], by simp only [hle.2.2.1], rfl, hle.2.2.2.2.1, hle.2.2.2.2.2.1,
    hle.2.2.2.2.2.2.1, hle.2.2.2.2.2.2.2⟩

/-- **The Draft's `walDisk_crash`**: the old generation's WAL in `dir` at `d`, synced to `n`, its
entry durable, is the new generation's at an image of its history at or past `n`, with a purged
prefix `k ≤ min pur |I|` to read from (`unl`, `pur` clamped to `|I|`), still synced to `n` and named (`named` kept: it is `true`). -/
theorem walDiskAt_crash (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗ walNamed (L := L) dir -∗
      ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (L := L') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (L := L') dir n ∗ walNamed (L := L') dir := by
  unfold walDiskAt walDirIs walSyncedLb walNamed absPast
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩ ⟨%q, %dq, Hq, %Hdq⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  iunfold absPast at Hp'
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  icases absPast_le _ s p $$ HP Hp with %Hlp
  icases absPast_le _ s q $$ HP Hq with %Hlq
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  obtain ⟨d2, h2, -, -, hn2⟩ := Hlq.2.2 dir dq Hdq.1
  rw [hdr] at h1 h2; cases h1; cases h2
  have hn : n ≤ dr.m := Nat.le_trans Hdp.2 hm1
  have hnamed : dr.named = true := hn2 Hdq.2
  obtain ⟨-, -, hcw, -⟩ := hc
  rcases hcw dir dr hdr with ⟨hnf, -⟩ | ⟨I, k, hI, hk, hs'⟩
  · rw [hnamed] at hnf; cases hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨⟨j, Nat.le_trans hn hj1, ?_, ?_⟩, ?_⟩
    · rw [hle.1]; exact hj2
    · rw [hle.1]; exact hj3
    · rw [hle.2.2.1]; exact hk
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle
  isplitr
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hnamed⟩

/-- **The crash of a WAL whose entry may not be durable**: it vanishes (only if its entry was not
durable), or it is the new generation's as in `walDiskAt_crash`. -/
theorem walDiskAt_crash_any (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗
      ((walAbsent (L := L') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (L := L') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗ walSyncedLb (L := L') dir n) := by
  unfold walDiskAt walAbsent walDirIs walSyncedLb absPast
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  iunfold absPast at Hp'
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  icases absPast_le _ s p $$ HP Hp with %Hlp
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  rw [hdr] at h1; cases h1
  have hn : n ≤ dr.m := Nat.le_trans Hdp.2 hm1
  obtain ⟨-, -, hcw, -⟩ := hc
  rcases hcw dir dr hdr with ⟨hnf, hnone⟩ | ⟨I, k, hI, hk, hs'⟩
  · ileft
    isplitl [HM']
    · iexists s'.wal; iframe HM'; ipureintro; rw [hnone]; trivial
    · ipureintro
      cases hdn : d.named
      · rfl
      · rw [hle.2.2.2.2.2.2.2 hdn] at hnf; cases hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  iright
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨⟨j, Nat.le_trans hn hj1, ?_, ?_⟩, ?_⟩
    · rw [hle.1]; exact hj2
    · rw [hle.1]; exact hj3
    · rw [hle.2.2.1]; exact hk
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩

/-- A directory with no WAL has none after the crash. -/
theorem walAbsent_crash (dir : GoString) :
    ⊢@{IProp GF} absDiskCrashWal (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walAbsent (L := L) dir -∗ walAbsent (L := L') dir := by
  unfold walAbsent walDirIs
  iintro Hcs ⟨%M, HM, %HMd⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, -, HM', -⟩
  have hs : s.wal !! dir = none := by
    have h := HMs dir
    rw [(walOptLe_none_iff _).1 HMd] at h
    exact (walOptLe_none_iff _).1 h
  iexists s'.wal; iframe HM'; ipureintro; rw [hc.2.2.2 dir hs]; trivial

/-- A durable directory stays durable (from the old generation's past states' authority, which
`absDisk_crash_view` returns). -/
theorem dirDurable_crash (s s' : AbsDiskState) (hc : absDisk_semantics.crash s s') (d : GoString) :
    ⊢@{IProp GF} absPastAuth (gooseAbsDiskGS (L := L)) s -∗ absPast (L := L') s' -∗
      dirDurable (L := L) d -∗ dirDurable (L := L') d := by
  unfold dirDurable absPast
  iintro HP #Hp' ⟨%p, Hp, %Hd⟩
  icases absPast_le _ s p $$ HP Hp with %Hlp
  iexists s'; iframe Hp'; ipureintro; rw [hc.2.1]; exact Hlp.2.1 d Hd

/-- The area stays the area (as `dirDurable_crash`). -/
theorem walArea_crash (s s' : AbsDiskState) (hc : absDisk_semantics.crash s s') (r : GoString) :
    ⊢@{IProp GF} absPastAuth (gooseAbsDiskGS (L := L)) s -∗ absPast (L := L') s' -∗
      walArea (L := L) r -∗ walArea (L := L') r := by
  unfold walArea absPast
  iintro HP #Hp' ⟨%p, Hp, %Hr⟩
  icases absPast_le _ s p $$ HP Hp with %Hlp
  iexists s'; iframe Hp'; ipureintro; rw [hc.1, Hlp.1, Hr]

end crashGen

end lifting

end Perennial
