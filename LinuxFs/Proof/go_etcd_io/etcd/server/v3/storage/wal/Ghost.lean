/- Lean-first (no Rocq counterpart).

# The WAL layer's ghost state over `fsExt` (`notes/wal-fsext-plan.md`, §2.1; W1)

The abstract-disk extension's client vocabulary (`GooseLang/Ext/AbsDisk/Specs.lean`) rebuilt as a
proof layer: the same predicates with the same laws, over ghost state the WAL's invariant
(`Inv.lean`, `walInv`) holds instead of an extension's state interpretation. Untrusted.

* **The names** (`WalGS`, a typeclass instance per generation, as `gooseAbsDiskGS` was): the WAL
  map's ghost variable and token, the past states, the area, the handles' modes, directories and
  purge rights, the lock token. A crash allocates new ones (`walGhost_init`, used by
  `Crash.lean`'s `walInv_crash`).
* **What the invariant holds** (`walGhost s`, `s` the real WAL state, an `AbsDiskState`: the area,
  each WAL directory's `WalDur`, the durable directories): the map's other half below `s`'s
  (`walMapLe`), the past states' authority (all below `s`), the handles' authorities (sealed), every
  WAL key in the area. Exactly `absDiskCtx` with the handles' authority of this layer.
* **The vocabulary** (`walOwn`, `walDirIs`, `walDiskAt`, `walAbsent`, `walSyncedLb`, `walNamed`,
  `dirDurable`, `walArea`, `walLenLb`, `walUnlockedTok`, `walPurgeW`, `walOpenW`, `walOpening`,
  `walReadFailed`): the bodies of `AbsDisk/Specs.lean`'s, over these names.

**Reuse (W1 implementation log, `notes/wal-fsext-plan.md`).** The generic parts of `AbsDisk/Specs.lean`
are imported (through the part's generated copy, `LinuxFs/GooseLang/Ext/AbsDisk/Specs.lean`,
`etc/gen-part-copies.py`), not restated: the state's order (`AbsDiskState`, `absLe`, `walMapLe`, `walDurLe`,
`walOptLe`, `walKeysInArea`, `WalMode`) and the generation-generic ghost pieces stated for any
`hL : AbsDiskGS GF` (`walOwnAt`, `absPastAt`, `absPastAuth`, `absPast_le`/`_grow`/`_snap`,
`absDisk_local_init`). Nothing of the extension's steps or interpretation is used. When `AbsDisk/`
is deleted, these move here.
-/
module

public import LinuxFs.GooseLang.Ext.AbsDisk.Specs
public import GooseLang.Ext.Fs.NamesGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The WAL state's crash relation (the abstract disk's `walCrash` of each directory, the area and
the durable directories kept, no WAL appearing): now a *conclusion* of `walInv_crash`, not a trusted
relation. -/
def walStCrash (s s' : AbsDiskState) : Prop := absDisk_semantics.crash s s'

/-- **The ghost names of one generation of the WAL layer.** `hA`: the map's variable and token, the
past states, the area, the lock token (its handle fields unused); `γh`, `γhd`, `γhp`: the handles'
modes, directories and purge rights. -/
class WalGS (GF : BundledGFunctors) where
  hA : AbsDiskGS GF
  γh : GName
  γhd : GName
  γhp : GName
  /-- The generation's crash token (`walCrashTok`): the WAL invariant holds its contents or it. -/
  γc : GName
  /-- The WALs being created (`walCreating`): a ghost map from a WAL directory to the key and
  history of the area claim `Create` renames in, which the invariant holds half of. -/
  γcr : GName
  /-- The open handles' tails (`walTailsRes`, `Inv.lean`): each WAL directory with an open
  handle to the ghost name of what the handle and the invariant share of its tail. -/
  γt : GName
  /-- Whether the program's halves of the WALs' files and directory claims are all parked in the
  invariant (`walParked`, `Inv.lean`): a ghost variable of a `Bool`, half the invariant's, half
  the lock token's (`true`, `walUnlockedTok`) or an open handle's (`false`, `walLockedTok`). -/
  γpk : GName

section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- The universal camera. -/
abbrev walAllG : AllG GF := W.hA.absDiskAllG

/-- **The program owns the WAL map, which is `M`** (half of the ghost variable, and the token). -/
def walOwn (M : GMap GoString WalDur) : IProp GF := walOwnAt W.hA M

/-- **The WAL state was `s` at some point of this generation** (persistent). -/
def walPast (s : AbsDiskState) : IProp GF := absPastAt W.hA s

instance walPast_persistent (s : AbsDiskState) : Persistent (walPast (W := W) s) := by
  unfold walPast; infer_instance

/-- The handles' authorities, every ghost name from `n` on unused. Sealed: only the WAL's own
proofs allocate a handle or change its mode (`walHandle_alloc`, `walHandleP_set`). -/
@[no_expose] def walHandleAuth : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (n : Nat) (Hh : GMap GName WalMode) (Hd : GMap GName (Loc × GoString))
      (Hp : GMap GName Unit),
    ghostMapAuth W.γh 1 Hh ∗ ghostMapAuth W.γhd 1 Hd ∗ ghostMapAuth W.γhp 1 Hp ∗
    ⌜∀ k, n ≤ k → Hh !! k = none ∧ Hd !! k = none ∧ Hp !! k = none⌝)

/-- **What the WAL invariant holds of the ghost state, the real WAL state being `s`**: the map's
other half, below `s`'s (`walMapLe`), the past states' authority, the handles' authorities, every
WAL key in the area. -/
def walGhost (s : AbsDiskState) : IProp GF :=
  letI := walAllG (W := W)
  iprop((∃ G : GMap GoString WalDur, ghostVar W.hA.γs (1 : Qp).half G ∗ ⌜walMapLe G s.wal⌝) ∗
    absPastAuth W.hA s ∗ walHandleAuth (W := W) ∗ ⌜walKeysInArea s⌝)

instance walHandleAuth_timeless : Timeless (walHandleAuth (W := W)) := by
  unfold walHandleAuth; infer_instance

instance walGhost_timeless (s : AbsDiskState) : Timeless (walGhost (W := W) s) := by
  unfold walGhost absPastAuth; infer_instance

/-- **The WAL area is `r`** (persistent). -/
def walArea (r : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, walPast (W := W) s ∗ ⌜s.area = r⌝)

/-- **The WAL directory `dir` holds `o`** (the whole map's ownership; the mark and `named` lower
bounds). -/
def walDirIs (dir : GoString) (o : Option WalDur) : IProp GF :=
  iprop(∃ M : GMap GoString WalDur, walOwn (W := W) M ∗ ⌜walOptLe o (M !! dir)⌝)

/-- **The WAL in `dir` is in the durable state `d`.** -/
def walDiskAt (dir : GoString) (d : WalDur) : IProp GF := walDirIs (W := W) dir (some d)

/-- **`dir` names no WAL.** -/
def walAbsent (dir : GoString) : IProp GF := walDirIs (W := W) dir none

/-- **The first `n` operations of `dir`'s history are synced** (persistent). -/
def walSyncedLb (dir : GoString) (n : Nat) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (d : WalDur), walPast (W := W) s ∗ ⌜s.wal !! dir = some d ∧ n ≤ d.m⌝)

/-- **`dir`'s WAL entry, and its ancestors', are durable** (persistent). -/
def walNamed (dir : GoString) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (d : WalDur), walPast (W := W) s ∗
    ⌜s.wal !! dir = some d ∧ d.named = true⌝)

/-- **`d`'s entry and its ancestors' are durable** (persistent). -/
def dirDurable (d : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, walPast (W := W) s ∗ ⌜s.dirs !! d = some ()⌝)

/-- **The handle named `γ` is of the `*wal.WAL` `w`, which writes the WAL in `dir`** (persistent). -/
def walHandleDir (w : Loc) (dir : GoString) (γ : GName) : IProp GF :=
  letI := walAllG (W := W)
  γ ↪[W.γhd]□ (w, dir)

/-- **`w` is a handle of the WAL in `dir`, in mode `m`** (exclusive). -/
def walHandleSt (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ γ : GName, walHandleDir (W := W) w dir γ ∗ γ ↪[W.γh] m)

/-- **The open WAL `w` has written its directory `dir`'s history up to length `n`** (persistent). -/
def walLenLb (w : Loc) (dir : GoString) (n : Nat) : IProp GF :=
  iprop(∃ (γ : GName) (s : AbsDiskState) (d : WalDur),
    walHandleDir (W := W) w dir γ ∗ walPast (W := W) s ∗ ⌜s.wal !! dir = some d ∧ n ≤ d.H.length⌝)

/-- The program's half of the parking flag (`WalGS.γpk`). -/
def walParkFrag (b : Bool) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γpk (1 : Qp).half b

/-- The invariant's half of the parking flag (`walParked`, `Inv.lean`). -/
def walParkAuth (b : Bool) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γpk (1 : Qp).half b

instance walParkAuth_timeless (b : Bool) : Timeless (walParkAuth (W := W) b) := by
  unfold walParkAuth; infer_instance

/-- **The generation's lock token** (exclusive; as `AbsDisk`'s), with the parking flag at `true`:
no handle holds the program's halves of the WALs' files (the invariant parks them all, `walParked`),
so that `Open`, holding it, can take them. -/
def walUnlockedTok : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) true)

/-- **The lock token as an open handle holds it**: the parking flag at `false` (the handle may hold
program halves the invariant would otherwise park). `walHandleP` and `walOpenW` carry it; `Close`
returns `walUnlockedTok` after parking what the handle holds (`walPark_set`). -/
def walLockedTok : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) false)

/-- **The generation's crash token** (exclusive): `walInv_crash` takes it, to keep the old
generation's invariant closed with it in place of its contents. -/
def walCrashTok : IProp GF :=
  letI := walAllG (W := W)
  token W.γc

instance walCrashTok_timeless : Timeless (walCrashTok (W := W)) := by
  unfold walCrashTok; infer_instance

theorem walCrashTok_excl :
    ⊢@{IProp GF} walCrashTok (W := W) -∗ walCrashTok (W := W) -∗ False := by
  unfold walCrashTok
  letI := walAllG (W := W)
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- **`w` is a handle of `dir` in mode `m`, with its purge right and the lock token.** Sealed. -/
@[no_expose] def walHandleP (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ γ : GName, walHandleDir (W := W) w dir γ ∗ γ ↪[W.γh] m ∗ γ ↪[W.γhp] () ∗
    walLockedTok (W := W))

/-- **The authority of the WALs being created** (the invariant's): each directory `Create` works on,
with the names `N` and history `h` of the area directory's claim it renames in. -/
def walCreatingAuth (CR : GMap GoString (Fs.NameSet × Fs.NamesH)) : IProp GF :=
  letI := walAllG (W := W)
  ghostMapAuth W.γcr 1 CR

instance walCreatingAuth_timeless (CR : GMap GoString (Fs.NameSet × Fs.NamesH)) :
    Timeless (walCreatingAuth (W := W) CR) := by
  unfold walCreatingAuth; infer_instance

/-- **`Create` of `dir` is renaming in the area claim of names `N`, history `h`** (exclusive, the
program's): the invariant holds half of that claim (`walInvBody`'s `CreatingOk`), so a client update
opened at the rename's step, where the file system's shared invariant cannot be opened to compare
claim keys, finds it. -/
def walCreating (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γcr] (N, h)

instance walCreating_timeless (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) :
    Timeless (walCreating (W := W) dir N h) := by
  unfold walCreating; infer_instance

/-- **The purge's right on the open WAL `w` in `dir`** (exclusive; as `AbsDisk`'s). -/
def walPurgeW (w : Loc) (dir : GoString) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ γ : GName, walHandleDir (W := W) w dir γ ∗ γ ↪[W.γhp] ())

/-- **The tails' authority** (the WAL invariant's): the directories with an open handle, each to
the ghost name of its tail (`walTailsRes`, `Inv.lean`). -/
def walTailsAuth (T : GMap GoString GName) : IProp GF :=
  letI := walAllG (W := W)
  ghostMapAuth W.γt 1 T

instance walTailsAuth_timeless (T : GMap GoString GName) : Timeless (walTailsAuth (W := W) T) := by
  unfold walTailsAuth; infer_instance

/-- **The open handle of `dir` names its tail `γ`** (the handle's, exclusive). -/
def walTailKey (dir : GoString) (γ : GName) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γt] γ

/-- **`w` is the WAL opened in `dir`, ready to append.** Sealed. -/
@[no_expose] def walOpenW (w : Loc) (dir : GoString) : IProp GF :=
  iprop(walHandleSt (W := W) w dir .append ∗ walLockedTok (W := W))

/-- **`w` is the WAL opened in `dir` for reading at the snapshot `s`.** Sealed. -/
@[no_expose] def walOpening (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  walHandleP (W := W) w dir (.opening s)

/-- **`w`'s `ReadAll` in `dir` failed.** Sealed. -/
@[no_expose] def walReadFailed (w : Loc) (dir : GoString) : IProp GF :=
  walHandleP (W := W) w dir .failed

instance walArea_persistent (r : GoString) : Persistent (walArea (W := W) r) := by
  unfold walArea; infer_instance
instance walSyncedLb_persistent (dir : GoString) (n : Nat) :
    Persistent (walSyncedLb (W := W) dir n) := by unfold walSyncedLb; infer_instance
instance walNamed_persistent (dir : GoString) : Persistent (walNamed (W := W) dir) := by
  unfold walNamed; infer_instance
instance dirDurable_persistent (d : GoString) : Persistent (dirDurable (W := W) d) := by
  unfold dirDurable; infer_instance
instance walHandleDir_persistent (w : Loc) (dir : GoString) (γ : GName) :
    Persistent (walHandleDir (W := W) w dir γ) := by unfold walHandleDir; infer_instance
instance walLenLb_persistent (w : Loc) (dir : GoString) (n : Nat) :
    Persistent (walLenLb (W := W) w dir n) := by unfold walLenLb; infer_instance

instance walPast_timeless (s : AbsDiskState) : Timeless (walPast (W := W) s) := by
  unfold walPast absPastAt; infer_instance
instance walArea_timeless (r : GoString) : Timeless (walArea (W := W) r) := by
  unfold walArea; infer_instance
instance walSyncedLb_timeless (dir : GoString) (n : Nat) :
    Timeless (walSyncedLb (W := W) dir n) := by unfold walSyncedLb; infer_instance
instance walNamed_timeless (dir : GoString) : Timeless (walNamed (W := W) dir) := by
  unfold walNamed; infer_instance
instance dirDurable_timeless (d : GoString) : Timeless (dirDurable (W := W) d) := by
  unfold dirDurable; infer_instance
instance walOwn_timeless (M : GMap GoString WalDur) : Timeless (walOwn (W := W) M) := by
  unfold walOwn walOwnAt; infer_instance
instance walDirIs_timeless (dir : GoString) (o : Option WalDur) :
    Timeless (walDirIs (W := W) dir o) := by unfold walDirIs; infer_instance
instance walDiskAt_timeless (dir : GoString) (d : WalDur) : Timeless (walDiskAt (W := W) dir d) := by
  unfold walDiskAt; infer_instance
instance walAbsent_timeless (dir : GoString) : Timeless (walAbsent (W := W) dir) := by
  unfold walAbsent; infer_instance
instance walUnlockedTok_timeless : Timeless (walUnlockedTok (W := W)) := by
  unfold walUnlockedTok walParkFrag; infer_instance
instance walLockedTok_timeless : Timeless (walLockedTok (W := W)) := by
  unfold walLockedTok walParkFrag; infer_instance

/-! ## Laws (as `AbsDisk/Specs.lean`'s, same statements) -/

theorem walDiskAt_weaken (dir : GoString) (d d' : WalDur) (h : walDurLe d d') :
    ⊢@{IProp GF} walDiskAt (W := W) dir d' -∗ walDiskAt (W := W) dir d := by
  unfold walDiskAt walDirIs
  iintro ⟨%M, HM, %HMd⟩
  iexists M; iframe HM; ipureintro
  exact walOptLe_trans (o2 := some d') h HMd

theorem walOwn_excl (M M' : GMap GoString WalDur) :
    ⊢@{IProp GF} walOwn (W := W) M -∗ walOwn (W := W) M' -∗ False := by
  unfold walOwn walOwnAt
  letI := walAllG (W := W)
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  iapply token_exclusive $$ H1 H2

theorem walDirIs_excl (dir dir' : GoString) (o o' : Option WalDur) :
    ⊢@{IProp GF} walDirIs (W := W) dir o -∗ walDirIs (W := W) dir' o' -∗ False := by
  unfold walDirIs
  iintro ⟨%M, H1, -⟩ ⟨%M', H2, -⟩
  iapply walOwn_excl $$ H1 H2

theorem walDiskAt_excl (dir dir' : GoString) (d d' : WalDur) :
    ⊢@{IProp GF} walDiskAt (W := W) dir d -∗ walDiskAt (W := W) dir' d' -∗ False :=
  walDirIs_excl dir dir' _ _

theorem walUnlockedTok_excl :
    ⊢@{IProp GF} walUnlockedTok (W := W) -∗ walUnlockedTok (W := W) -∗ False := by
  unfold walUnlockedTok
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The parking flag's halves agree. -/
theorem walPark_agree (b b' : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walParkFrag (W := W) b' -∗ ⌜b = b'⌝ := by
  unfold walParkAuth walParkFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **Setting the parking flag** (both halves). -/
theorem walPark_set (b1 b2 b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b1 -∗ walParkFrag (W := W) b2 ==∗
      walParkAuth (W := W) b ∗ walParkFrag (W := W) b := by
  unfold walParkAuth walParkFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-- **Taking the lock** (`Open`, `Create`): with the invariant's half of the flag, the lock token
becomes the handles' (the flag `false`); the invariant's half was `true`. -/
theorem walUnlockedTok_lock (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walUnlockedTok (W := W) ==∗
      ⌜b = true⌝ ∗ walParkAuth (W := W) false ∗ walLockedTok (W := W) := by
  unfold walUnlockedTok walLockedTok
  iintro Ha ⟨Ht, Hf⟩
  icases walPark_agree (W := W) b true $$ Ha Hf with %hb
  imod walPark_set (W := W) b true false $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf
  ipureintro; exact hb

/-- **Releasing the lock** (`Close`, an `Open` that failed after taking it): the flag back to `true`. -/
theorem walLockedTok_unlock (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walLockedTok (W := W) ==∗
      ⌜b = false⌝ ∗ walParkAuth (W := W) true ∗ walUnlockedTok (W := W) := by
  unfold walUnlockedTok walLockedTok
  iintro Ha ⟨Ht, Hf⟩
  icases walPark_agree (W := W) b false $$ Ha Hf with %hb
  imod walPark_set (W := W) b false true $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf
  ipureintro; exact hb

theorem walSyncedLb_mono (dir : GoString) (n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walSyncedLb (W := W) dir n -∗ walSyncedLb (W := W) dir n' := by
  unfold walSyncedLb
  iintro ⟨%s, %d, Hs, %Hd⟩
  iexists s, d; iframe Hs; ipureintro; exact ⟨Hd.1, Nat.le_trans h Hd.2⟩

theorem walLenLb_mono (w : Loc) (dir : GoString) (n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walLenLb (W := W) w dir n -∗ walLenLb (W := W) w dir n' := by
  unfold walLenLb
  iintro ⟨%γ, %s, %d, Hw, Hs, %Hd⟩
  iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨Hd.1, Nat.le_trans h Hd.2⟩

theorem walHandleDir_agree (w w' : Loc) (dir dir' : GoString) (γ : GName) :
    ⊢@{IProp GF} walHandleDir (W := W) w dir γ -∗ walHandleDir (W := W) w' dir' γ -∗
      ⌜w = w' ∧ dir = dir'⌝ := by
  unfold walHandleDir
  letI := walAllG (W := W)
  iintro #H1 #H2
  icases ghostMapElem_agree $$ H1 H2 with %H
  ipureintro; exact Prod.mk.inj H

theorem walOpenW_lenLb (w : Loc) (dir : GoString) (s : AbsDiskState) (d : WalDur) (n : Nat)
    (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpenW (W := W) w dir -∗ walPast (W := W) s -∗
      walOpenW (W := W) w dir ∗ walLenLb (W := W) w dir n := by
  unfold walOpenW walHandleSt walLenLb
  iintro ⟨⟨%γ, #Hw, Hm⟩, Hu⟩ #Hs
  isplitl [Hm Hu]
  · iframe Hu; iexists γ; iframe Hw Hm
  · iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨hd, hn⟩

theorem walOpening_lenLb (w : Loc) (dir : GoString) (sn : w64 × w64) (s : AbsDiskState) (d : WalDur)
    (n : Nat) (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpening (W := W) w dir sn -∗ walPast (W := W) s -∗
      walOpening (W := W) w dir sn ∗ walLenLb (W := W) w dir n := by
  unfold walOpening walHandleP walLenLb
  iintro ⟨%γ, #Hw, Hm, Hp, Hu⟩ #Hs
  isplitl [Hm Hp Hu]
  · iexists γ; iframe Hw Hm Hp Hu
  · iexists γ, s, d; iframe Hw Hs; ipureintro; exact ⟨hd, hn⟩

theorem walArea_agree (r r' : GoString) :
    ⊢@{IProp GF} walArea (W := W) r -∗ walArea (W := W) r' -∗ ⌜r = r'⌝ := by
  unfold walArea walPast absPastAt
  letI := walAllG (W := W)
  iintro ⟨%p, ⟨-, #Hp⟩, %hp⟩ ⟨%q, ⟨-, #Hq⟩, %hq⟩
  icases ghostMapElem_agree $$ Hp Hq with %H
  ipureintro; rw [← hp, ← hq]; exact H

theorem walPast_walArea (s : AbsDiskState) :
    ⊢@{IProp GF} walPast (W := W) s -∗ walArea (W := W) s.area := by
  unfold walArea
  iintro #Hs
  iexists s; iframe Hs; ipureintro; rfl

/-- What the program's WAL map says of the invariant's: it is below the real one. -/
theorem walOwn_agree (s : AbsDiskState) (M : GMap GoString WalDur) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walOwn (W := W) M -∗ ⌜walMapLe M s.wal⌝ := by
  unfold walGhost walOwn walOwnAt
  letI := walAllG (W := W)
  iintro ⟨⟨%G, Hs, %HG⟩, -⟩ ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  ipureintro; subst HMG; exact HG

/-- What a past state says of the present one. -/
theorem walPast_ghost_le (s p : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walPast (W := W) p -∗ ⌜absLe p s⌝ := by
  unfold walGhost walPast
  iintro ⟨-, HP, -⟩ Hp
  iapply absPast_le $$ HP Hp

theorem walArea_ghost (s : AbsDiskState) (r : GoString) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walArea (W := W) r -∗ ⌜s.area = r⌝ := by
  unfold walArea
  iintro Hc ⟨%p, Hp, %hp⟩
  icases walPast_ghost_le $$ Hc Hp with %Hle
  ipureintro; rw [Hle.1, hp]

theorem walGhost_keys (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ ⌜walKeysInArea s⌝ := by
  unfold walGhost
  iintro ⟨-, -, -, %hk⟩
  ipureintro; exact hk

/-- **One purge right per handle.** -/
theorem walGhost_keys_keep (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walGhost (W := W) s ∗ ⌜walKeysInArea s⌝ := by
  unfold walGhost
  iintro ⟨Hs, HP, Hh, %hk⟩
  iframe Hs HP Hh
  isplitl <;> ipureintro <;> exact hk

theorem walPurgeW_excl (γ : GName) :
    ⊢@{IProp GF} (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗
      (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗ False := by
  letI := walAllG (W := W)
  iintro H1 H2
  icases ghostMapElem_valid_2 γ _ (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2 with %Hv
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- **The ghost state at a bigger real state** (a step's update): the map set to the new state's,
the past states kept, and the new state's fact. -/
theorem walGhost_upd (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhost (W := W) s' ∗ walOwn (W := W) s'.wal ∗ walPast (W := W) s' := by
  iintro Hc HM
  icases walOwn_agree $$ Hc HM with %HMs
  unfold walGhost walOwn walOwnAt walPast
  letI := walAllG (W := W)
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

/-- **The ghost state at a bigger real state, the program's map unchanged.** -/
theorem walGhost_upd_lag (s s' : AbsDiskState) (hlag : ∀ G, walMapLe G s.wal → walMapLe G s'.wal)
    (hle : absLe s s') (hk : walKeysInArea s → walKeysInArea s') :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s' ∗ walPast (W := W) s' := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨⟨%G, Hs, %HG⟩, HP, Hh, %Hk⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe HP Hh Hp
  isplitl [Hs]
  · iexists G; iframe Hs; ipureintro; exact hlag G HG
  ipureintro; exact hk Hk

/-- A past state's fact, from the authority. -/
theorem walGhost_past (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s ∗ walPast (W := W) s := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨Hs, HP, Hh, Hk⟩
  imod absPast_snap _ s $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe Hs HP Hh Hk Hp

end ghost

/-! ## A generation's start -/

section init
variable {GF : BundledGFunctors}

/-- **A new generation's ghost state** at the real state `s` (every WAL key in the area): the
invariant's part, the program's map at `s.wal`, `s`'s fact, the lock token and the crash token. -/
theorem walGhost_init (hPre : AbsDiskGpreS GF) (s : AbsDiskState) (hk : walKeysInArea s) :
    ⊢@{IProp GF} |==> ∃ W : WalGS GF, walGhost (W := W) s ∗ walOwn (W := W) s.wal ∗
      walPast (W := W) s ∗ walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗
      walCreatingAuth (W := W) ∅ ∗ walTailsAuth (W := W) ∅ ∗ walParkAuth (W := W) true := by
  imod absDisk_local_init hPre s hk with ⟨%hA, Hctx, Hst⟩
  letI := hA.absDiskAllG
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := WalMode)) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Loc × GoString)) with ⟨%γhd, Hhd⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Unit)) with ⟨%γhp, Hhp⟩
  imod token_alloc (GF := GF) with ⟨%γc, Hc⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Fs.NameSet × Fs.NamesH))
    with ⟨%γcr, Hcr⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GName)) with ⟨%γt, Ht⟩
  imod (ghostVar_alloc (GF := GF) true) with ⟨%γpk, Hpk⟩
  iexists ⟨hA, γh, γhd, γhp, γc, γcr, γt, γpk⟩
  icases (ghostVar_split_half (GF := GF) γpk 1 true).1 $$ Hpk with ⟨Hpk1, Hpk2⟩
  imodintro
  iunfold absDiskCtx at Hctx
  icases Hctx with ⟨Hs, HP, -, -⟩
  iunfold absDiskStart at Hst
  icases Hst with ⟨HM, Hp, Hu⟩
  unfold walGhost walOwn walPast walUnlockedTok walCrashTok walHandleAuth walCreatingAuth walTailsAuth
    walParkFrag walParkAuth walAllG
  iframe Hs HP HM Hp Hu Hc Hcr Ht Hpk1 Hpk2
  isplitl [Hh Hhd Hhp]
  · iexists 0, ∅, ∅, ∅
    iframe Hh Hhd Hhp
    ipureintro; intro k _; exact ⟨rfl, rfl, rfl⟩
  · ipureintro; exact hk

end init

end WalFs
end EtcdGrove
end Perennial

end
