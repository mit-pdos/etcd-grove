/-
Iris reasoning principles for the abstract-disk extension (`Impl.lean`; WAL W4a, 2026-11-11, the
approved W4 Draft's §1.2, `notes/decisions.md`, "WAL W4a"). Proved: nothing here is trusted.

* **The WALs' state**: one ghost variable of the whole map of WAL directories (`GMap GoString
  WalDur`), half of it in the state interpretation and half the program's, with an exclusive
  token (`walOwn M`), as the durable extension's `durableOwn`: it says which directories hold no
  WAL, which `Create` needs. The per-directory predicates (`walDirIs`, `walDiskAt`, `walAbsent`)
  each hold the whole map (so two of them, even of two directories, are exclusive): the program
  has one WAL directory (the tester's, the server's); a claim operation would be needed to own
  directories separately, since the map has no fragments for the infinitely many directories
  without a WAL.
* **Facts** (persistent): `absPast s`, the extension's state was `s` at some point of this
  generation; the state only grows (`absLe`: marks, lengths, `named` and the durable directories
  do not decrease, no WAL disappears), so a past state bounds the present one. `walSyncedLb`,
  `walNamed`, `dirDurable` are facts about a past state; `walLenLb w n` also names `w`'s directory
  (a persistent handle fact).
* **Handles**: `walOpenW w dir` / `walOpening w dir s`, exclusive ghost-map elements keyed by the
  `*wal.WAL` location, in maps whose authority is in the state interpretation (only the
  extension's steps could allocate them; the WAL's axioms give them). Per generation.
* **The steps** (`wp_WalCreate`, ...): one spec per external operation, logically atomic, each
  returning the new state's fact.
* **The crash** (`absDisk_crash_interp`): the new generation's ghost state is allocated from the
  crashed state; `absDiskCrashStart old new` holds the old generation's half of the WAL map and its
  facts' authority, and the new generation's half and start fact, with the crash relation between
  them. `walDiskAt_crash` is the Draft's `walDisk_crash` in these terms.
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
  .ofInjective (fun s => Pos.Countable.encode (s.wal, s.dirs))
    (by intro a b h; cases a; cases b; simp_all)

/-- **The state only grows**: no durable directory or WAL disappears, and a WAL's synced mark,
length and `named` do not decrease. -/
def absLe (s s' : AbsDiskState) : Prop :=
  (∀ d, s.dirs !! d = some () → s'.dirs !! d = some ()) ∧
  ∀ dir d, s.wal !! dir = some d → ∃ d', s'.wal !! dir = some d' ∧
    d.m ≤ d'.m ∧ d.H.length ≤ d'.H.length ∧ (d.named = true → d'.named = true)

theorem absLe_refl (s : AbsDiskState) : absLe s s :=
  ⟨fun _ h => h, fun _ d h => ⟨d, h, Nat.le_refl _, Nat.le_refl _, id⟩⟩

theorem absLe_trans {s1 s2 s3 : AbsDiskState} (h12 : absLe s1 s2) (h23 : absLe s2 s3) :
    absLe s1 s3 := by
  refine ⟨fun d h => h23.1 d (h12.1 d h), fun dir d h => ?_⟩
  obtain ⟨d2, h2, hm2, hl2, hn2⟩ := h12.2 dir d h
  obtain ⟨d3, h3, hm3, hl3, hn3⟩ := h23.2 dir d2 h2
  exact ⟨d3, h3, Nat.le_trans hm2 hm3, Nat.le_trans hl2 hl3, fun x => hn3 (hn2 x)⟩

/-- An update of one WAL that keeps its marks, length and `named` from decreasing. -/
theorem absLe_upd (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur)
    (hf : ∀ d, d.m ≤ (f d).m ∧ d.H.length ≤ (f d).H.length ∧ (d.named = true → (f d).named = true)) :
    absLe s (absDiskUpd s dir f) := by
  unfold absDiskUpd
  cases hd : s.wal !! dir with
  | none => exact absLe_refl s
  | some d0 =>
    refine ⟨fun _ h => h, fun dir' d h => ?_⟩
    simp only
    by_cases hdir : dir = dir'
    · subst hdir
      rw [hd] at h; cases h
      exact ⟨f d0, by simp [GMap.lookup_insert_eq_iff], hf d0⟩
    · exact ⟨d, by rw [GMap.lookup_insert_eq_iff]; simp [hdir, h], Nat.le_refl _, Nat.le_refl _, id⟩

theorem absDiskUpd_wal (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur) (d : WalDur)
    (hd : s.wal !! dir = some d) : (absDiskUpd s dir f).wal = <[dir := f d]> s.wal := by
  unfold absDiskUpd; rw [hd]

/-! ## Ghost state -/

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
  /-- The handles' modes (exclusive elements): `none` ready to append, `some s` opened at `s`. -/
  γh : GName
  /-- The handles' directories (persistent elements). -/
  γhd : GName

section ghost
variable {GF : BundledGFunctors}

/-- **The WAL map is `M`** (the program's half, with the token). -/
def walOwnAt (hL : AbsDiskGS GF) (M : GMap GoString WalDur) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(ghostVar hL.γs (1 : Qp).half M ∗ token hL.γt)

/-- **The state was `s` at some point of this generation** (persistent). -/
def absPastAt (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  s ↪[hL.γf]□ ()

instance absPastAt_persistent (hL : AbsDiskGS GF) (s : AbsDiskState) :
    Persistent (absPastAt hL s) := by
  unfold absPastAt; infer_instance

/-- The authority of the past states, all below `s`. -/
def absPastAuth (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(∃ F : GMap AbsDiskState Unit, ghostMapAuth hL.γf 1 F ∗
    ([∗map] p ↦ _u ∈ F, p ↪[hL.γf]□ ()) ∗ ⌜∀ p, F !! p = some () → absLe p s⌝)

/-- **The interpretation of the state `s`**: the WAL map's other half, the past states (all below
`s`), the handles' authorities. -/
def absDiskCtx (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  letI := hL.absDiskAllG
  iprop(ghostVar hL.γs (1 : Qp).half s.wal ∗ absPastAuth hL s ∗
    (∃ Hh : GMap Loc (Option (w64 × w64)), ghostMapAuth hL.γh 1 Hh) ∗
    (∃ Hd : GMap Loc GoString, ghostMapAuth hL.γhd 1 Hd))

/-- What the program starts with: the WAL map and the start state's fact. -/
def absDiskStart (hL : AbsDiskGS GF) (s : AbsDiskState) : IProp GF :=
  iprop(walOwnAt hL s.wal ∗ absPastAt hL s)

theorem absPast_le (hL : AbsDiskGS GF) (s p : AbsDiskState) :
    ⊢@{IProp GF} absPastAuth hL s -∗ absPastAt hL p -∗ ⌜absLe p s⌝ := by
  letI := hL.absDiskAllG
  unfold absPastAuth absPastAt
  iintro ⟨%F, HA, -, %Hle⟩ #Hp
  icases ghost_map_lookup $$ HA Hp with %Hl
  ipureintro; exact Hle p Hl

/-- The past states' authority at a bigger state. -/
theorem absPast_grow (hL : AbsDiskGS GF) (s s' : AbsDiskState) (hle : absLe s s') :
    ⊢@{IProp GF} absPastAuth hL s -∗ absPastAuth hL s' := by
  letI := hL.absDiskAllG
  unfold absPastAuth
  iintro ⟨%F, HA, HE, %Hle⟩
  iexists F
  iframe HA HE
  ipureintro; exact fun p hp => absLe_trans (Hle p hp) hle

/-- The present state's fact. -/
theorem absPast_snap (hL : AbsDiskGS GF) (s : AbsDiskState) :
    ⊢@{IProp GF} absPastAuth hL s ==∗ absPastAuth hL s ∗ absPastAt hL s := by
  letI := hL.absDiskAllG
  unfold absPastAuth absPastAt
  iintro ⟨%F, HA, #HE, %Hle⟩
  cases hF : F !! s with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := F)
      (Φ := fun p _ => iprop(p ↪[hL.γf]□ ())) hF).1 $$ HE with ⟨#Hs, -⟩
    imodintro
    isplitl [HA]
    · iexists F; iframe HA HE; ipureintro; exact Hle
    · iexact Hs
  | none =>
    imod ghost_map_insert_persist s () hF $$ HA with ⟨HA, #Hs⟩
    imodintro
    isplitl [HA]
    · iexists (F.insert s ())
      iframe HA
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
    · iexact Hs

theorem absDisk_local_init (hPre : AbsDiskGpreS GF) (s : AbsDiskState) :
    ⊢@{IProp GF} |==> ∃ hL : AbsDiskGS GF, absDiskCtx hL s ∗ absDiskStart hL s := by
  letI := hPre.absDiskPreAllG
  imod ghostVar_alloc (GF := GF) s.wal with ⟨%γs, Hs⟩
  icases (ghostVar_split_half γs 1 _).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod (ghost_map_alloc (GF := GF) (GMap.singleton s ())) with ⟨%γf, HF, HFe⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Option (w64 × w64))) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := GoString)) with ⟨%γhd, Hhd⟩
  let hL : AbsDiskGS GF := ⟨hPre.absDiskPreAllG, γs, γt, γf, γh, γhd⟩
  have hsing : (GMap.singleton s () : GMap AbsDiskState Unit) = (∅ : GMap _ _).insert s () := rfl
  rw [hsing]
  icases (BigSepM.bigSepM_insert (PROP := IProp GF) (m := (∅ : GMap AbsDiskState Unit))
    (Φ := fun p v => iprop(p ↪[γf] v)) rfl).1 $$ HFe with ⟨Hse, -⟩
  imod ghostMapElem_persist $$ Hse with #Hse
  imodintro
  iexists hL
  isplitl [Hs1 HF Hh Hhd]
  · unfold absDiskCtx absPastAuth
    iframe Hs1
    isplitl [HF]
    · iexists ((∅ : GMap AbsDiskState Unit).insert s ())
      iframe HF
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
    · isplitl [Hh]
      · iexists ∅; iexact Hh
      · iexists ∅; iexact Hhd
  · unfold absDiskStart walOwnAt absPastAt
    iframe Hs2 Ht Hse

end ghost

/-- The ghost state of the abstract disk. The program gets the whole WAL map and the start
state's fact (as the durable extension's `durableOwn`). -/
instance absDisk_interp : ExtInterp absDiskExt where
  LocalGS := AbsDiskGS
  GlobalGS _ := Unit
  localCtx := absDiskCtx
  globalCtx _ _ := iprop(True)
  PreG := AbsDiskGpreS
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart := absDiskStart
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre s _ _ := absDisk_local_init hPre s

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
  icases Hctx with ⟨Hs, HP, -, -⟩
  imod absDisk_local_init hPre s' with ⟨%hL', Hctx', Hst'⟩
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

/-- **The `*wal.WAL` `w` writes the WAL in `dir`** (persistent). -/
def walHandleDir (w : Loc) (dir : GoString) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  w ↪[(gooseAbsDiskGS (L := L)).γhd]□ dir

/-- **The open WAL `w` has written its directory's history up to length `n`** (persistent; per
generation): what `Sync` takes. -/
def walLenLb (w : Loc) (n : Nat) : IProp GF :=
  iprop(∃ (dir : GoString) (s : AbsDiskState) (d : WalDur), walHandleDir (L := L) w dir ∗
    absPast (L := L) s ∗ ⌜s.wal !! dir = some d ∧ n ≤ d.H.length⌝)

/-- **`w` is the WAL opened in `dir`, ready to append** (exclusive). -/
def walOpenW (w : Loc) (dir : GoString) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(walHandleDir (L := L) w dir ∗ w ↪[(gooseAbsDiskGS (L := L)).γh] (none : Option (w64 × w64)))

/-- **`w` is the WAL opened in `dir` for reading at the snapshot `s`** (exclusive). -/
def walOpening (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iprop(walHandleDir (L := L) w dir ∗ w ↪[(gooseAbsDiskGS (L := L)).γh] (some s))

instance walSyncedLb_persistent (dir : GoString) (n : Nat) :
    Persistent (walSyncedLb (L := L) dir n) := by unfold walSyncedLb; infer_instance
instance walNamed_persistent (dir : GoString) : Persistent (walNamed (L := L) dir) := by
  unfold walNamed; infer_instance
instance dirDurable_persistent (d : GoString) : Persistent (dirDurable (L := L) d) := by
  unfold dirDurable; infer_instance
instance walHandleDir_persistent (w : Loc) (dir : GoString) :
    Persistent (walHandleDir (L := L) w dir) := by unfold walHandleDir; infer_instance
instance walLenLb_persistent (w : Loc) (n : Nat) : Persistent (walLenLb (L := L) w n) := by
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

theorem walLenLb_mono (w : Loc) (n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walLenLb (L := L) w n -∗ walLenLb (L := L) w n' := by
  unfold walLenLb
  iintro ⟨%dir, %s, %d, Hw, Hs, %Hd⟩
  iexists dir, s, d; iframe Hw Hs; ipureintro; exact ⟨Hd.1, Nat.le_trans h Hd.2⟩

theorem walHandleDir_agree (w : Loc) (dir dir' : GoString) :
    ⊢@{IProp GF} walHandleDir (L := L) w dir -∗ walHandleDir (L := L) w dir' -∗ ⌜dir = dir'⌝ := by
  unfold walHandleDir
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro #H1 #H2
  iapply ghostMapElem_agree $$ H1 H2

theorem walOpenW_excl (w : Loc) (dir dir' : GoString) :
    ⊢@{IProp GF} walOpenW (L := L) w dir -∗ walOpenW (L := L) w dir' -∗ False := by
  unfold walOpenW
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  icases ghostMapElem_ne _ _ _ _ _ _ $$ H1 H2 with %Hne
  exact absurd rfl Hne

theorem walOpenW_handleDir (w : Loc) (dir : GoString) :
    ⊢@{IProp GF} walOpenW (L := L) w dir -∗ walHandleDir (L := L) w dir := by
  unfold walOpenW; iintro ⟨#H, -⟩; iexact H

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
  obtain ⟨d', h', hm, -⟩ := Hle.2 dir dp Hdp.1
  rw [HMd] at h'; cases h'
  exact Nat.le_trans Hdp.2 hm

/-- **The interpretation at a bigger state** (a step's ghost update): the WAL map set to the new
state's, the past states kept, and the new state's fact. -/
theorem absDisk_upd (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s -∗ walOwn (L := L) M ==∗
      ⌜M = s.wal⌝ ∗ absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ walOwn (L := L) s'.wal ∗
      absPast (L := L) s' := by
  iintro Hc HM
  icases walOwn_agree $$ Hc HM with %HMs
  subst HMs
  unfold absDiskCtx walOwn walOwnAt absPast
  letI := (gooseAbsDiskGS (L := L)).absDiskAllG
  iintro
  icases Hc with ⟨Hs, HP, Hh, Hhd⟩
  icases HM with ⟨HM, Ht⟩
  imod ghostVar_update_halves s'.wal _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe Hs HM Ht HP Hh Hhd Hp
  ipureintro; rfl

/-- The same for a step that changes only the durable directories (no WAL map needed). -/
theorem absDisk_upd_dirs (s s' : AbsDiskState) (hw : s'.wal = s.wal) (hle : absLe s s') :
    ⊢@{IProp GF} absDiskCtx (gooseAbsDiskGS (L := L)) s ==∗
      absDiskCtx (gooseAbsDiskGS (L := L)) s' ∗ absPast (L := L) s' := by
  iintro Hc
  unfold absDiskCtx absPast
  icases Hc with ⟨Hs, HP, Hh, Hhd⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  rw [hw]
  iframe Hs HP Hh Hhd Hp

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
  unfold walDiskAt walDirIs
  iintro HAU
  iapply wp_absDisk_step op v (fun s => s.wal !! dir = some d) (fun s => absDiskUpd s dir upd) hv
    (fun h s g hs => Hprog h s g (fun d' hd' => by rw [hs] at hd'; cases hd'; exact Hd)) Hdet
  imod HAU with ⟨⟨%M, HM, %HMd⟩, Hk⟩
  imodintro
  iintro %s Hc
  imod absDisk_upd s (absDiskUpd s dir upd) M (absLe_upd s dir upd hf) $$ Hc HM
    with ⟨%HMs, Hc, HM, #Hp⟩
  subst HMs
  have hw := absDiskUpd_wal s dir upd d HMd
  imodintro
  isplitr
  · ipureintro; exact HMd
  iframe Hc
  have hl : (absDiskUpd s dir upd).wal !! dir = some (upd d) := by
    rw [hw]; exact GMap.lookup_insert _ _ _
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗ ⌜M' !! dir = some (upd d)⌝) $$ [HM]
  · iexists (absDiskUpd s dir upd).wal; iframe HM; ipureintro; exact hl
  iapply Hk $$ Hd Hp
  ipureintro; exact hl

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

theorem wp_WalNamed (dir : GoString) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with named := true }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some ({ d with named := true })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalNamed" _ dir (fun d => { d with named := true }) (fun d => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩) ?_ ?_ d trivial Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', Hv, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
    exact ⟨rfl, rfl, rfl⟩

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

theorem wp_WalUnlock (dir : GoString) (p : Nat) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with unl := max d.unl p }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some ({ d with unl := max d.unl p })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalUnlock" (Val (PairV (#dir) (#(walCode p))))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalUnlock" _ dir (fun d => { d with unl := max d.unl p }) (fun d => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩) ?_ ?_ d trivial Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, p, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', p', Hv, rfl⟩ := Hst
    obtain ⟨Hd, Ho⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := walCode_inj (go.intoVal_inj Ho)
    exact ⟨rfl, rfl, rfl⟩

theorem wp_WalPurge (dir : GoString) (d : WalDur) (Φ : val → IProp GF) :
    (|={E,∅}=> walDiskAt (L := L) dir d ∗
      (walDiskAt (L := L) dir ({ d with pur := max d.pur d.unl }) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some ({ d with pur := max d.pur d.unl })⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalPurge" (Val (#dir))) @ st; E {{ Φ }} := by
  refine wp_absDisk_walStep "WalPurge" _ dir (fun d => { d with pur := max d.pur d.unl }) (fun d => True)
    (by simp [val.isPanic]) (fun d => ⟨Nat.le_refl _, Nat.le_refl _, id⟩) ?_ ?_ d trivial Φ
  · intro h s g hP
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, ?_, ?_⟩ <;> first | trivial | rfl | exact hP
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', Hv, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
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

/-- `"WalCreate"` of `(dir, md)`: a fresh WAL where there was none. -/
theorem wp_WalCreate (dir : GoString) (md : List w8) (Φ : val → IProp GF) :
    (|={E,∅}=> walAbsent (L := L) dir ∗
      (walDiskAt (L := L) dir (walDurFresh md) -∗ (∀ s', absPast (L := L) s' -∗
        ⌜s'.wal !! dir = some (walDurFresh md)⌝ -∗ ▷ |={∅,E}=> Φ #())))
    ⊢ WP (ExternalOp absDiskExt.name "WalCreate" (Val (PairV (#dir) (#md)))) @ st; E {{ Φ }} := by
  unfold walAbsent walDiskAt walDirIs
  iintro HAU
  have hle : ∀ s : AbsDiskState, s.wal !! dir = none →
      absLe s { s with wal := <[dir := walDurFresh md]> s.wal } := by
    intro s hs
    refine ⟨fun _ h => h, fun dir' d h => ⟨d, ?_, Nat.le_refl _, Nat.le_refl _, id⟩⟩
    have hne : dir ≠ dir' := by rintro rfl; rw [hs] at h; cases h
    simp only; rw [GMap.lookup_insert_ne _ _ hne]; exact h
  iapply wp_absDisk_step "WalCreate" _ (fun s => s.wal !! dir = none)
    (fun s => { s with wal := <[dir := walDurFresh md]> s.wal }) (by simp [val.isPanic])
  · intro h s g hs
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, dir, md, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hs
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, dir', md', Hv, -, rfl⟩ := Hst
    obtain ⟨Hd, Hm⟩ := val.PairV.inj Hv
    obtain rfl := go.intoVal_inj Hd
    obtain rfl := go.intoVal_inj Hm
    exact ⟨rfl, rfl, rfl⟩
  imod HAU with ⟨⟨%M, HM, %HMd⟩, Hk⟩
  imodintro
  iintro %s Hc
  icases walOwn_agree $$ Hc HM with %HMs
  subst HMs
  imod absDisk_upd s _ s.wal (hle s HMd) $$ Hc HM with ⟨-, Hc, HM, #Hp⟩
  have hl : (<[dir := walDurFresh md]> s.wal) !! dir = some (walDurFresh md) := GMap.lookup_insert _ _ _
  imodintro
  isplitr
  · ipureintro; exact HMd
  iframe Hc
  ihave Hd : (∃ M' : GMap GoString WalDur, walOwn (L := L) M' ∗ ⌜M' !! dir = some (walDurFresh md)⌝) $$ [HM]
  · iexists _; iframe HM; ipureintro; exact hl
  iapply Hk $$ Hd Hp
  ipureintro; exact hl

/-- `"DirDurable"` of `d`: `d`'s entry and its ancestors' durable (no WAL map needed). -/
theorem wp_DirDurable (d : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> dirDurable (L := L) d -∗ ▷ |={∅,E}=> Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "DirDurable" (Val (#d))) @ st; E {{ Φ }} := by
  iintro HAU
  iapply wp_absDisk_step "DirDurable" _ (fun _ => True)
    (fun s => { s with dirs := <[d := ()]> s.dirs }) (by simp [val.isPanic])
  · intro h s g _
    simp only [AbsDiskStep]
    refine ⟨?_, ?_, d, ?_, ?_⟩ <;> first | trivial | rfl
  · intro h s g e' h' s' g' Hst
    simp only [AbsDiskStep] at Hst
    obtain ⟨rfl, rfl, d', Hv, rfl⟩ := Hst
    obtain rfl := go.intoVal_inj Hv
    exact ⟨rfl, rfl, rfl⟩
  imod HAU with Hk
  imodintro
  iintro %s Hc
  have hle : absLe s { s with dirs := <[d := ()]> s.dirs } := by
    refine ⟨fun d' h => ?_, fun dir dd h => ⟨dd, h, Nat.le_refl _, Nat.le_refl _, id⟩⟩
    simp only
    by_cases hd : d = d'
    · subst hd; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ hd]; exact h
  imod absDisk_upd_dirs s { s with dirs := <[d := ()]> s.dirs } rfl hle $$ Hc with ⟨Hc, #Hp⟩
  imodintro
  isplitr
  · ipureintro; trivial
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
prefix `k ≤ d.pur` to read from, still synced to `n` and named. -/
theorem walDiskAt_crash (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walDiskAt (L := L) dir d -∗ walSyncedLb (L := L) dir n -∗ walNamed (L := L) dir -∗
      ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ d.pur⌝ ∗
        walDiskAt (L := L') dir { d with H := I, cut := k, named := true } ∗
        walSyncedLb (L := L') dir n ∗ walNamed (L := L') dir := by
  unfold walDiskAt walDirIs walSyncedLb walNamed absPast
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩ ⟨%q, %dq, Hq, %Hdq⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  iunfold absPast at Hp'
  subst HMs
  icases absPast_le _ s p $$ HP Hp with %Hlp
  icases absPast_le _ s q $$ HP Hq with %Hlq
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2 dir dp Hdp.1
  obtain ⟨d2, h2, -, -, hn2⟩ := Hlq.2 dir dq Hdq.1
  rw [HMd] at h1 h2; cases h1; cases h2
  have hn : n ≤ d.m := Nat.le_trans Hdp.2 hm1
  have hnamed : d.named = true := hn2 Hdq.2
  obtain ⟨-, hcw, -⟩ := hc
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
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', rfl⟩

/-- A directory with no WAL has none after the crash. -/
theorem walAbsent_crash (dir : GoString) :
    ⊢@{IProp GF} absDiskCrashStart (gooseAbsDiskGS (L := L)) (gooseAbsDiskGS (L := L')) -∗
      walAbsent (L := L) dir -∗ walAbsent (L := L') dir := by
  unfold walAbsent walDirIs
  iintro Hcs ⟨%M, HM, %HMd⟩
  icases absDisk_crash_view (L := L) L' M $$ Hcs HM with ⟨%s, %s', ⟨%hc, %HMs⟩, -, HM', -⟩
  subst HMs
  iexists s'.wal; iframe HM'; ipureintro; exact hc.2.2 dir HMd

/-- A durable directory stays durable (from the old generation's past states' authority, which
`absDisk_crash_view` returns). -/
theorem dirDurable_crash (s s' : AbsDiskState) (hc : absDisk_semantics.crash s s') (d : GoString) :
    ⊢@{IProp GF} absPastAuth (gooseAbsDiskGS (L := L)) s -∗ absPast (L := L') s' -∗
      dirDurable (L := L) d -∗ dirDurable (L := L') d := by
  unfold dirDurable absPast
  iintro HP #Hp' ⟨%p, Hp, %Hd⟩
  icases absPast_le _ s p $$ HP Hp with %Hlp
  iexists s'; iframe Hp'; ipureintro; rw [hc.1]; exact Hlp.1 d Hd

end crashGen

end lifting

end Perennial
