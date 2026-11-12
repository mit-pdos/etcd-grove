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
* **The WAL area** (`walArea r`, persistent): the state's fixed `area`. The interpretation keeps
  every WAL key in the area (`walKeysInArea`), so `walAbsent dir` of an area directory gives the
  whole of `Create`'s region free (`walCreateRegion_free`): nothing in `Create(area/n)`'s region can
  be a WAL key (`area/n.tmp` and `area/n.broken.*` contain `.`, `area/n/…` has a `/` in the name),
  and no durable directory or durable file is under the area. So the whole-map ownership is no
  longer what makes `Create` sound (cross-key effects are gone, M2 of the Freeze review's aliasing
  lens): a per-directory split (rung 3) would only need the invariant.
* **The start** (`absDiskInitOk`, the adequacy theorem's premise through `initP`): the area clean,
  the WAL keys in it, no durable directory under it; `absDiskStart` still hands `walOwn s0.wal` for
  a concrete `s0`. **W4c gate:** the tester's adequacy quantifies `s0` universally, constrained only
  at its own directories (`s0.area = root/data/member`, `s0.wal !! (area/wal) = none`, the real disk
  empty under the area), never fixing `s0.wal = ∅`. **C6 gate:** a restart start with a WAL present
  names its directories by premise (B3-1), and hands the durable reservation from the start or
  proves that no durable operation precedes it.
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
  through the step specs `wp_WalCreate` (`"WalCreate"`), `wp_WalOpenHandle` (`"WalUnlock"` of 0),
  `wp_WalReadFail` (`"WalUnlock"` of 0) and `wp_WalNamedOpen` (`"WalNamed"`), so no freshness of
  `w` is needed. **W4c gate:** a trusted model that performs one of these operations (today only
  the WAL's axiomatized bodies do; the tester's `purgeRound` performs only `"WalPurge"`) is reviewed
  against these specs. Each handle carries one purge right (`walPurgeW`, exclusive), minted with
  it, handed out with `walOpenW` (by `Create`, or by a successful `ReadAll`), consumed by `Close`.
  Per generation: a crash allocates fresh ghost names, so no handle or right survives it.
* **The steps** (`wp_WalCreate`, ...): one spec per external operation, logically atomic, each
  returning the new state's fact.
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

/-- **The interpretation of the state `s`**: the WAL map's other half, the past states (all below
`s`), the handles' authorities, every WAL directory in the area. -/
def absDiskCtx (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(ghostVar hL.γs (1 : Qp).half s.wal ∗ absPastAuth hL s ∗ absHandleAuth hL ∗
    ⌜walKeysInArea s⌝)

/-- What the program starts with: the WAL map and the start state's fact (which gives the area,
`absPast_walArea`). -/
def absDiskStart (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  iprop(walOwnAt hL s.wal ∗ absPastAt hL s)

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
  let hL : AbsDiskGS GF := ⟨hPre.absDiskPreAllG, γs, γt, γf, γa, γh, γhd, γhp⟩
  have hsing : (GMap.singleton s () : GMap AbsDiskState Unit) = (∅ : GMap _ _).insert s () := rfl
  rw [hsing]
  icases (BigSepM.bigSepM_insert (PROP := IProp GF) (m := (∅ : GMap AbsDiskState Unit))
    (Φ := fun p v => iprop(p ↪[γf] v)) rfl).1 $$ HFe with ⟨Hse, -⟩
  imod ghostMapElem_persist $$ Hse with #Hse
  imodintro
  iexists hL
  isplitl [Hs1 HF Hh Hhd Hhp]
  · unfold absDiskCtx absPastAuth absHandleAuth
    iframe Hs1
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
    iframe Hs2 Ht Hse Ha

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

/-- **What a crash hands the next generation**: the old generation's half of the WAL map at `s`
and its past states' authority (all below `s`), the new generation's half of the map at `s'` and
`s'`'s fact, with `s'` a crash of `s`. -/
def absDiskCrashStart (hL hL' : AbsDiskGS GF) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(∃ s s' : AbsDiskState, ⌜absDisk_semantics.crash s s'⌝ ∗
    ghostVar hL.γs (1 : Qp).half s.wal ∗ absPastAuth hL s ∗
    walOwnAt hL' s'.wal ∗ absPastAt hL' s')

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
  unfold absDiskCrashStart absDiskStart
  iexists s, s'
  iframe Hs HP Hst'
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
header). -/
def walDirIs (dir : GoString) (o : Option WalDur) : IProp GF :=
  iprop(∃ M : GMap GoString WalDur, walOwn (L := L) M ∗ ⌜M !! dir = o⌝)

/-- **The WAL in `dir` is in the durable state `d`** (the extension's points-to). -/
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

/-- **`w` is a handle of the WAL in `dir`, in mode `m`, with its purge right** (exclusive). -/
def walHandleP (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(∃ γ : GName, walHandleDir (L := L) w dir γ ∗ γ ↪[(gooseAbsDiskGS (L := L)).γh] m ∗
    γ ↪[(gooseAbsDiskGS (L := L)).γhp] ())

/-- **The purge's right on the open WAL `w` in `dir`** (exclusive: one per handle, minted with it, and
per generation, so it does not survive a crash; WAL W4a revision round 2, replacing the server's
opaque `walPurgeRight` in the extension's axioms): the purge of old WAL files there may run only
while it is held, and `Close` (which unlocks every file) consumes it with the handle. -/
def walPurgeW (w : Loc) (dir : GoString) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(∃ γ : GName, walHandleDir (L := L) w dir γ ∗ γ ↪[(gooseAbsDiskGS (L := L)).γhp] ())

/-- **`w` is the WAL opened in `dir`, ready to append** (exclusive). -/
def walOpenW (w : Loc) (dir : GoString) : IProp GF := walHandleSt (L := L) w dir .append

/-- **`w` is the WAL opened in `dir` for reading at the snapshot `s`** (exclusive; with the handle's
purge right, which a successful `ReadAll` hands out). -/
def walOpening (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  walHandleP (L := L) w dir (.opening s)

/-- **`w`'s `ReadAll` in `dir` failed** (exclusive): only `Close` accepts it. -/
def walReadFailed (w : Loc) (dir : GoString) : IProp GF := walHandleP (L := L) w dir .failed

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
  iintro ⟨%γ, #Hw, Hm⟩ #Hs
  isplitl [Hm]
  · iexists γ; iframe Hw Hm
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

/-- What the program's WAL map says of the interpretation's. -/
theorem walOwn_agree (s : AbsDiskState) (M : GMap GoString WalDur) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walOwn (L := L) M -∗ ⌜M = s.wal⌝ := by
  unfold absDiskCtx walOwn walOwnAt
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨Hs, -⟩ ⟨HM, -⟩
  iapply ghostVar_agree $$ HM Hs

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

/-- The synced mark is at most the history's length. -/
theorem walDiskAt_syncedLb_le (s : AbsDiskState) (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walDiskAt (L := L) dir d -∗
      walSyncedLb (L := L) dir n -∗ ⌜n ≤ d.m⌝ := by
  unfold walDiskAt walDirIs walSyncedLb
  iintro Hc ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩
  icases walOwn_agree $$ Hc HM with %HM
  icases absPast_ctx_le $$ Hc Hp with %Hle
  subst HM
  ipureintro
  obtain ⟨d', h', hm, -⟩ := Hle.2.2 dir dp Hdp.1
  rw [HMd] at h'; cases h'
  exact Nat.le_trans Hdp.2 hm

/-- **A new handle** with its purge right (inside a step: the interpretation holds the handles'
authorities). Private: only the step specs of this file allocate handles. -/
private theorem walHandle_alloc (s : AbsDiskState) (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ walHandleP (L := L) w dir m := by
  unfold absDiskCtx walHandleP walHandleDir
  iintro ⟨Hs, HP, HH, Hk⟩
  imod absHandle_alloc _ w dir m $$ HH with ⟨HH, Hh⟩
  imodintro
  iframe Hs HP HH Hk Hh

/-- **A handle's mode changed**, its purge right kept (inside a step). Private. -/
private theorem walHandleP_set (s : AbsDiskState) (w : Loc) (dir : GoString) (m m' : WalMode) :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walHandleP (L := L) w dir m ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s ∗ walHandleP (L := L) w dir m' := by
  unfold absDiskCtx walHandleP
  iintro ⟨Hs, HP, HH, Hk⟩ ⟨%γ, #Hd, Hm, Hp⟩
  imod absHandle_set _ γ m m' $$ HH Hm with ⟨HH, Hm⟩
  imodintro
  iframe Hs HP HH Hk
  iexists γ; iframe Hd Hm Hp

/-- A handle with its purge right is the handle and the right. -/
theorem walHandleP_split (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} walHandleP (L := L) w dir m -∗ walHandleSt (L := L) w dir m ∗ walPurgeW (L := L) w dir := by
  unfold walHandleP walHandleSt walPurgeW
  iintro ⟨%γ, #Hd, Hm, Hp⟩
  isplitl [Hm]
  · iexists γ; iframe Hd Hm
  · iexists γ; iframe Hd Hp

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
      ⌜M = s.wal⌝ ∗ absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ walOwn (L := L) s'.wal ∗
      absPast (L := L) s' := by
  iintro Hc HM
  icases walOwn_agree $$ Hc HM with %HMs
  subst HMs
  unfold absDiskCtx walOwn walOwnAt absPast
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro
  icases Hc with ⟨Hs, HP, Hh, %Hk⟩
  icases HM with ⟨HM, Ht⟩
  imod ghostVar_update_halves s'.wal _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe Hs HM Ht HP Hh Hp
  ipureintro; exact ⟨rfl, hk Hk⟩

/-- The same for a step that changes only the durable directories (no WAL map needed). -/
theorem absDisk_upd_dirs (s s' : AbsDiskState) (hw : s'.wal = s.wal) (hle : absLe s s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ absPast (L := L) s' := by
  iintro Hc
  unfold absDiskCtx absPast
  icases Hc with ⟨Hs, HP, Hh, %Hk⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  rw [hw]
  iframe Hs HP Hh Hp
  ipureintro
  intro k d h
  rw [hle.1]; rw [hw] at h; exact Hk k d h

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
update `R ==∗ R'` under the interpretation at the step (a handle's allocation or mode change). -/
theorem wp_absDisk_walStepR (op : String) (v : val) (dir : GoString) (upd : WalDur → WalDur)
    (Pd : WalDur → Prop) (hv : v.isPanic = false)
    (hf : ∀ d, d.m ≤ (upd d).m ∧ d.H.length ≤ (upd d).H.length ∧
      (d.named = true → (upd d).named = true))
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
        ⌜s'.wal !! dir = some (upd d)⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  unfold walDiskAt walDirIs
  iintro HAU
  iapply wp_absDisk_step op v (fun s => s.wal !! dir = some d) (fun s => absDiskUpd s dir upd) hv
    (fun h s g hs => Hprog h s g (fun d' hd' => by rw [hs] at hd'; cases hd'; exact Hd)) Hdet
  imod HAU with ⟨⟨%M, HM, %HMd⟩, HR, Hk⟩
  imodintro
  iintro %s Hc
  imod absDisk_upd s (absDiskUpd s dir upd) M (absLe_upd s dir upd hf)
    (walKeysInArea_upd s dir upd) $$ Hc HM with ⟨%HMs, Hc, HM, #Hp⟩
  subst HMs
  imod Hupd _ $$ Hc HR with ⟨Hc, HR⟩
  have hw := absDiskUpd_wal s dir upd d HMd
  imodintro
  isplitr
  · ipureintro; exact HMd
  iframe Hc
  have hl : (absDiskUpd s dir upd).wal !! dir = some (upd d) := by
    rw [hw]; exact GMap.lookup_insert _ _ _
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗ ⌜M' !! dir = some (upd d)⌝) $$ [HM]
  · iexists (absDiskUpd s dir upd).wal; iframe HM; ipureintro; exact hl
  iapply Hk $$ Hd HR Hp
  ipureintro; exact hl

/-- A WAL step of `dir` that updates its WAL by `upd` (no change if there is none). -/
theorem wp_absDisk_walStep (op : String) (v : val) (dir : GoString) (upd : WalDur → WalDur)
    (Pd : WalDur → Prop) (hv : v.isPanic = false)
    (hf : ∀ d, d.m ≤ (upd d).m ∧ d.H.length ≤ (upd d).H.length ∧
      (d.named = true → (upd d).named = true))
    (Hprog : ∀ h s g, (∀ d, s.wal !! dir = some d → Pd d) →
      AbsDiskStep op v h s g (Val #()) h (absDiskUpd s dir upd) g)
    (Hdet : ∀ h s g e' h' s' g', AbsDiskStep op v h s g e' h' s' g' →
      h' = h ∧ e' = Val #() ∧ s' = absDiskUpd s dir upd) (d : WalDur) (Hd : Pd d)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir (upd d) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some (upd d)⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name op (Val v)) @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_walStepR op v dir upd Pd hv hf Hprog Hdet d Hd iprop(True) iprop(True)
    (fun s => by iintro Hc -; imodintro; iframe Hc) Φ
  imod HAU with ⟨Hd, Hk⟩
  imodintro
  iframe Hd
  isplitr
  · itrivial
  · iintro Hd -
    iapply Hk $$ Hd

/-! ### The WAL steps, one by one -/

theorem wp_WalAppend (dir : GoString) (o : WalOpG WalEnt) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir { d with H := d.H ++ [o] } -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some { d with H := d.H ++ [o] }⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalAppend" (Val (PairV (#dir) (#(walCode o))))) @ st; E
      {{ Φ }} := by
  refine wp_absDisk_walStep "WalAppend" _ dir (fun d => { d with H := d.H ++ [o] }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, by simp, id⟩) ?_ ?_ d trivial Φ
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
        ⌜s'.wal !! dir = some ({ d with named := true })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} :=
  wp_absDisk_walStep "WalNamed" _ dir (fun d => { d with named := true }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)
    (walNamed_prog dir).1 (walNamed_prog dir).2 d trivial Φ

/-- `"WalNamed"` of `dir` that also turns the handle `w`, opened for reading at `s`, into one ready
to append (a successful write-mode `ReadAll`'s last step). -/
theorem wp_WalNamedOpen (w : Loc) (dir : GoString) (s : w64 × w64) (d : WalDur)
    (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗ walOpening (L := L) w dir s ∗
      (walDiskAt (L := L) dir ({ d with named := true }) -∗
        (walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir) -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜s'.wal !! dir = some ({ d with named := true })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} :=
  wp_absDisk_walStepR "WalNamed" _ dir (fun d => { d with named := true }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)
    (walNamed_prog dir).1 (walNamed_prog dir).2 d trivial
    (walOpening (L := L) w dir s) iprop(walOpenW (L := L) w dir ∗ walPurgeW (L := L) w dir)
    (fun s' => by
      unfold walOpening walOpenW
      iintro Hc Hh
      imod walHandleP_set s' w dir (.opening s) .append $$ Hc Hh with ⟨Hc, Hh⟩
      imodintro
      iframe Hc
      iapply walHandleP_split $$ Hh) Φ

theorem wp_WalSync (dir : GoString) (n : Nat) (d : WalDur) (Hn : n ≤ d.H.length) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with m := max d.m n }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some ({ d with m := max d.m n })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode n))))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalSync" _ dir (fun d => { d with m := max d.m n }) (fun d => n ≤ d.H.length)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_max_left _ _, Nat.le_refl _, id⟩) ?_ ?_ d Hn Φ
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
        ⌜s'.wal !! dir = some ({ d with unl := max d.unl p })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode p))))) @ st; E {{ Φ }} :=
  wp_absDisk_walStep "WalUnlock" _ dir (fun d => { d with unl := max d.unl p }) (fun _ => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)
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

/-- **`Open`'s handle**: a no-op step that allocates the handle `w`, opened in `dir` for reading at
`s`. -/
theorem wp_WalOpenHandle (w : Loc) (dir : GoString) (s : w64 × w64) (Φ : val → IProp GF) :
    (|={E,∅}=> walOpening (L := L) w dir s -∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode (0 : Nat))))))
      @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_WalNoop dir iprop(True) (walOpening (L := L) w dir s)
    (fun s' => by unfold walOpening; iintro Hc -; iapply walHandle_alloc s' w dir (.opening s) $$ Hc) Φ
  imod HAU with Hk
  imodintro
  isplitr
  · itrivial
  · iexact Hk

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
          ⌜s'.wal !! dir = some ({ d with pur := max d.pur d.unl, cut := k })⌝ -∗
            ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalPurge" (Val (PairV (#dir) (#(walCode k))))) @ st; E
      {{ Φ }} := by
  refine wp_absDisk_walStep "WalPurge" _ dir (fun d => { d with pur := max d.pur d.unl, cut := k })
    (fun d => d.cut ≤ k ∧ k ≤ max d.pur d.unl)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩) ?_ ?_ d Hk Φ
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

theorem wp_WalUnsize (dir : GoString) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with sized := false }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some ({ d with sized := false })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnsize" (Val (#dir))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalUnsize" _ dir (fun d => { d with sized := false }) (fun d => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩) ?_ ?_ d trivial Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', Hv, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
    exact ⟨rfl, rfl, rfl⟩

/-- `"WalCreate"` of `(dir, md)`, `dir` a directory of the area `r`: a fresh WAL where there was
none (the rest of `Create`'s region is then free too, `walCreateRegion_free`), and the handle `w`
ready to append. -/
theorem wp_WalCreate (w : Loc) (r dir : GoString) (md : List w8) (hdir : walAreaDir r dir)
    (Φ : val → IProp GF) :
    walArea (L := L) r ∗
    (|={E,∅}=> walAbsent (L := L) dir ∗
      (walDiskAt (L := L) dir (walDurFresh md) -∗ walOpenW (L := L) w dir -∗ walPurgeW (L := L) w dir -∗
        (∀ s', absPast (L := L) s' -∗
          ⌜s'.wal !! dir = some (walDurFresh md)⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalCreate" (Val (PairV (#dir) (#md)))) @ st; E {{ Φ }} := by
  unfold walAbsent walDiskAt walDirIs walOpenW
  iintro ⟨#HA, HAU⟩
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
  subst HMs
  have hds : walAreaDir s.area dir := by rw [Har]; exact hdir
  imod absDisk_upd s _ s.wal (hle s HMd) (hkeys s hds) $$ Hc HM with ⟨-, Hc, HM, #Hp⟩
  imod walHandle_alloc _ w dir .append $$ Hc with ⟨Hc, Hw⟩
  icases walHandleP_split $$ Hw with ⟨Hw, Hpw⟩
  have hl : (<[dir := walDurFresh md]> s.wal) !! dir = some (walDurFresh md) := GMap.lookup_insert _ _ _
  imodintro
  isplitr
  · ipureintro; exact ⟨hds, walCreateRegion_free Hks hds HMd⟩
  iframe Hc
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗ ⌜M' !! dir = some (walDurFresh md)⌝) $$ [HM]
  · iexists _; iframe HM; ipureintro; exact hl
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

/-! ## The crash, in a generation's terms -/

section crashGen
variable (L' : GooseLocalGS GF)

/-- What the crash start says of the old generation's WAL map. -/
theorem absDisk_crash_view (M : GMap GoString WalDur) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walOwn (L := L) M -∗ ∃ s s' : AbsDiskState, ⌜absDisk_semantics.crash s s' ∧ M = s.wal⌝ ∗
        absPastAuth (gooseAbsDiskGS (L := L)) s ∗ walOwn (L := L') s'.wal ∗ absPast (L := L') s' := by
  unfold absDiskCrashStart walOwn absPast
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨%s, %s', %hc, Hs, HP, HM', Hp'⟩ HM
  unfold walOwnAt
  icases HM with ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMs
  iexists s, s'
  iframe HP HM' Hp'
  ipureintro; exact ⟨hc, HMs⟩

/-- **The Draft's `walDisk_crash`**: the old generation's WAL in `dir` at `d`, synced to `n`, its
entry durable, is the new generation's at an image of its history at or past `n`, with a purged
prefix `k ≤ min pur |I|` to read from (`unl`, `pur` clamped to `|I|`), still synced to `n` and named (`named` kept: it is `true`). -/
theorem walDiskAt_crash (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗ walNamed (L := L) dir -∗
      ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (L := L') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (L := L') dir n ∗ walNamed (L := L') dir := by
  unfold walDiskAt walDirIs walSyncedLb walNamed absPast
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩ ⟨%q, %dq, Hq, %Hdq⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  iunfold absPast at Hp'
  subst HMs
  icases absPast_le _ s p $$ HP Hp with %Hlp
  icases absPast_le _ s q $$ HP Hq with %Hlq
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  obtain ⟨d2, h2, -, -, hn2⟩ := Hlq.2.2 dir dq Hdq.1
  rw [HMd] at h1 h2; cases h1; cases h2
  have hn : n ≤ d.m := Nat.le_trans Hdp.2 hm1
  have hnamed : d.named = true := hn2 Hdq.2
  obtain ⟨-, -, hcw, -⟩ := hc
  rcases hcw dir d HMd with ⟨hnf, -⟩ | ⟨I, k, hI, hk, hs'⟩
  · rw [hnamed] at hnf; cases hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  iexists I, k
  isplitr
  · ipureintro; exact ⟨⟨j, Nat.le_trans hn hj1, hj2, hj3⟩, hk⟩
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; exact hs'
  isplitr
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hnamed⟩

/-- **The crash of a WAL whose entry may not be durable**: it vanishes (only if its entry was not
durable), or it is the new generation's as in `walDiskAt_crash`. -/
theorem walDiskAt_crash_any (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗
      ((walAbsent (L := L') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (L := L') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗ walSyncedLb (L := L') dir n) := by
  unfold walDiskAt walAbsent walDirIs walSyncedLb absPast
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  iunfold absPast at Hp'
  subst HMs
  icases absPast_le _ s p $$ HP Hp with %Hlp
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  rw [HMd] at h1; cases h1
  have hn : n ≤ d.m := Nat.le_trans Hdp.2 hm1
  obtain ⟨-, -, hcw, -⟩ := hc
  rcases hcw dir d HMd with ⟨hnf, hnone⟩ | ⟨I, k, hI, hk, hs'⟩
  · ileft
    isplitl [HM']
    · iexists s'.wal; iframe HM'; ipureintro; exact hnone
    · ipureintro; exact hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  iright
  iexists I, k
  isplitr
  · ipureintro; exact ⟨⟨j, Nat.le_trans hn hj1, hj2, hj3⟩, hk⟩
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; exact hs'
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩

/-- A directory with no WAL has none after the crash. -/
theorem walAbsent_crash (dir : GoString) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walAbsent (L := L) dir -∗ walAbsent (L := L') dir := by
  unfold walAbsent walDirIs
  iintro Hcs ⟨%M, HM, %HMd⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, -, HM', -⟩
  subst HMs
  iexists s'.wal; iframe HM'; ipureintro; exact hc.2.2.2 dir HMd

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
