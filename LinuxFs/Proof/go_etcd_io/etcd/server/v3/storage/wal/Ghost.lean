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

/-- **What is out of the parked state** (`walParked`, `Inv.lean`; W3/W5's gap A): the segments' inodes
`O` whose program halves a handle holds, the WAL directories' claims `D` whose program half it holds
(by key: the directory's inode and the claim's names, so that a step changing the claim's history does
not change the record), the WAL directories `T` whose pipeline names it holds. The invariant holds
half of the record (`walOutAuth`), the lock token the empty record's other half (`walUnlockedTok`),
an open handle (`Open`'s pin on) or `Create` (from its commit) the other half, with what it took. -/
structure WalOut where
  O : List Fs.Ino
  D : List (Fs.Ino × Fs.NameSet)
  T : List GoString

/-- Nothing out. -/
def WalOut.empty : WalOut := ⟨[], [], []⟩

/-- The segment of inode `i` taken out. -/
def WalOut.addSeg (o : WalOut) (i : Fs.Ino) : WalOut := ⟨i :: o.O, o.D, o.T⟩
/-- The segment of inode `i` put back. -/
def WalOut.delSeg (o : WalOut) (i : Fs.Ino) : WalOut := ⟨o.O.filter (· ≠ i), o.D, o.T⟩
/-- The claim of key `k` taken out. -/
def WalOut.addClaim (o : WalOut) (k : Fs.Ino × Fs.NameSet) : WalOut := ⟨o.O, k :: o.D, o.T⟩
/-- The claim of key `k` put back. -/
def WalOut.delClaim (o : WalOut) (k : Fs.Ino × Fs.NameSet) : WalOut := ⟨o.O, o.D.filter (· ≠ k), o.T⟩
/-- The pipeline names of the WAL directory `dir` taken out. -/
def WalOut.addTmp (o : WalOut) (dir : GoString) : WalOut := ⟨o.O, o.D, dir :: o.T⟩
/-- The pipeline names of the WAL directory `dir` put back. -/
def WalOut.delTmp (o : WalOut) (dir : GoString) : WalOut := ⟨o.O, o.D, o.T.filter (· ≠ dir)⟩

instance : Pos.Countable WalOut :=
  .ofInjective (fun o => Pos.Countable.encode (o.O, o.D, o.T)) (by
    intro a b h
    have h' := Pos.encode_inj h
    cases a; cases b
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    rfl)

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
  /-- The WAL directories' claim keys (`walDirKey`; `Inv.lean`'s `DirKeysOk`): a ghost map from a
  WAL directory to its directory's inode and the names its claim leaves out (`.except X`), with
  persistent elements, so that an open handle's half of its directory's claim is known to be the
  invariant's other half's (W2 log, "the directory-claim map"). -/
  γdk : GName
  /-- Whether a cut's rename is pending (`walCutAuth`/`walCutFrag`): a ghost variable of an
  `Option GoString` (the WAL directory whose cut renamed a segment in and has not yet synced its
  directory), half the invariant's, half the lock token's (`none`) or a cut's in progress. -/
  γcp : GName
  /-- What is out of the parked state (`walOutAuth`/`walOutFrag`): a ghost variable of a `WalOut`,
  half the invariant's (`walParked`), half the lock token's (empty, `walUnlockedTok`) or the
  holder's of what is out (a handle's body, `Create`'s). -/
  γpo : GName
  /-- The WAL directory `Create` has committed and whose name it has not yet registered (`walNamesAuth`/
  `walNamesFrag`, `Inv.lean`'s `walNamesRes`; G-spine, W1 log): a ghost variable of an `Option GoString`,
  half the invariant's, half the lock token's (`none`: every present WAL registered) or that `Create`'s
  (`some dir`, from its commit, which takes the lock, to its registration). -/
  γnm : GName
  /-- The WAL names split out of the area claim (`walSplitAuth`/`walSplitFrag`): a ghost variable of a
  `List GoString`, half the invariant's (each a present WAL's name, its own claim `.only [nm]`), half
  the area's program part's (`walAreaRes`: its claim holds every WAL name but these). -/
  γnw : GName
  /-- The lent tails (`walLentAuth`/`walLentTok`; `Inv.lean`'s `walLentRes`, I3b, `wal-tc14`): a ghost
  map from a WAL directory to its tail record's name and the length of its layout's `old`, the
  authority the invariant's, each element (exclusive) the holder's of the lent tail. -/
  γl : GName

/-! ## The WALs' step bound (`notes/bounds-plan.md`, "The WAL's segment sequence") -/

section steps
variable {GF : BundledGFunctors} {hlc : HasLC} [GooseExts] [GooseInterp] [G : GooseGlobalGS hlc GF]

/-- **Every WAL's history at most `n` operations long.** -/
def WalsStepped (s : AbsDiskState) (n : Nat) : Prop :=
  ∀ dir d, s.wal !! dir = some d → d.H.length ≤ n

/-- **The WALs' step bound** (persistent; `notes/bounds-plan.md`, "The WAL's segment sequence"): at
least as many counted steps (`⧖ n`, Perennial's persistent time receipt; the counter is global across
generations, so the receipt is crash-stable) as any WAL's history has operations. `Save` and
`SaveSnapshot` take one counted step before their commit (`walHandleIn_steps`, then
`walHandleIn_append`), a crash keeps a prefix of each history, `Create` starts one empty; so every
WAL's history, hence its cuts and its last segment's sequence number (`WalAbsD.seqName`), is below the
receipts' bound, which the adequacy theorem fixes (`walAreaOk`'s `ReceiptBoundLe GF (2 ^ 62)`):
`ReadAll`'s `walDirH` bound. -/
def walStepsLb (s : AbsDiskState) : IProp GF := iprop(∃ n : Nat, ⧖ n ∗ ⌜WalsStepped s n⌝)

instance walStepsLb_persistent (s : AbsDiskState) : Persistent (walStepsLb (G := G) s) := by
  unfold walStepsLb; infer_instance

instance walStepsLb_timeless (s : AbsDiskState) : Timeless (walStepsLb (G := G) s) := by
  unfold walStepsLb; infer_instance

theorem WalsStepped.mono {s : AbsDiskState} {n n' : Nat} (h : WalsStepped s n) (hn : n ≤ n') :
    WalsStepped s n' := fun dir d hd => Nat.le_trans (h dir d hd) hn

/-- `WalsStepped` with one WAL set to a state whose history is within the bound. -/
theorem WalsStepped.insert {s s' : AbsDiskState} {dir : GoString} {d' : WalDur} {n : Nat}
    (h : WalsStepped s n) (hw : s'.wal = <[dir := d']> s.wal) (hd' : d'.H.length ≤ n) :
    WalsStepped s' n := by
  intro k e he
  rw [hw] at he
  by_cases hk : k = dir
  · subst hk; rw [GMap.lookup_insert_eq] at he; cases he; exact hd'
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at he; exact h k e he

/-- `WalsStepped` across an update of one WAL keeping its history (`absDiskUpd`). -/
theorem WalsStepped.upd {s : AbsDiskState} {dir : GoString} {f : WalDur → WalDur} {n : Nat}
    (h : WalsStepped s n) (hH : ∀ d, (f d).H = d.H) : WalsStepped (absDiskUpd s dir f) n := by
  unfold absDiskUpd
  cases hd : s.wal !! dir with
  | none => exact h
  | some d => exact h.insert rfl (by rw [hH]; exact h dir d hd)

/-- The step bound at a new state, given the receipt `⧖ n'`: each of its WALs' histories no longer
than the old bound or than `n'`. -/
theorem walStepsLb_upd (s s' : AbsDiskState) (n' : Nat)
    (hH : ∀ n, WalsStepped s n → WalsStepped s' (max n n')) :
    ⊢@{IProp GF} ⧖ n' -∗ walStepsLb (G := G) s -∗ walStepsLb (G := G) s' := by
  unfold walStepsLb
  iintro #Hn' ⟨%n, #Hn, %hn⟩
  iexists max n n'
  isplitl
  · iapply (preceipt_max n n').2
    iframe Hn Hn'
  ipureintro; exact hH n hn

/-- The step bound at a new state whose WALs' histories are within the old bound. -/
theorem walStepsLb_mono (s s' : AbsDiskState) (hH : ∀ n, WalsStepped s n → WalsStepped s' n) :
    ⊢@{IProp GF} walStepsLb (G := G) s -∗ walStepsLb (G := G) s' := by
  unfold walStepsLb
  iintro ⟨%n, #Hn, %hn⟩
  iexists n
  iframe Hn
  ipureintro; exact hH n hn

/-- One WAL's history within the bound: `⧖` of its length. -/
theorem walStepsLb_at (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) :
    ⊢@{IProp GF} walStepsLb (G := G) s -∗ ⧖ d.H.length := by
  unfold walStepsLb
  iintro ⟨%n, #Hn, %hn⟩
  iapply preceipt_mono (hn dir d hd)
  iexact Hn

end steps

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

instance walHandleAuth_timeless : Timeless (walHandleAuth (W := W)) := by
  unfold walHandleAuth; infer_instance

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

/-- **What is out of the parked state is `o`**, the program's half (`WalGS.γpo`): the lock token's
(`o` empty) or the holder's of what is out. -/
def walOutFrag (o : WalOut) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γpo (1 : Qp).half o

/-- The invariant's half of the record of what is out (`walParked`, `Inv.lean`). -/
def walOutAuth (o : WalOut) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γpo (1 : Qp).half o

instance walOutAuth_timeless (o : WalOut) : Timeless (walOutAuth (W := W) o) := by
  unfold walOutAuth; infer_instance

instance walOutFrag_timeless (o : WalOut) : Timeless (walOutFrag (W := W) o) := by
  unfold walOutFrag; infer_instance

/-- **The WAL directory committed and not yet registered is `o`**, the program's half (`WalGS.γnm`):
the lock token's (`none`) or the committing `Create`'s. -/
def walNamesFrag (o : Option GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γnm (1 : Qp).half o

/-- The invariant's half of the pending registration (`walNamesRes`, `Inv.lean`). -/
def walNamesAuth (o : Option GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γnm (1 : Qp).half o

instance walNamesFrag_timeless (o : Option GoString) : Timeless (walNamesFrag (W := W) o) := by
  unfold walNamesFrag; infer_instance

instance walNamesAuth_timeless (o : Option GoString) : Timeless (walNamesAuth (W := W) o) := by
  unfold walNamesAuth; infer_instance

/-- **The WAL names split out of the area claim are `Wn`**, the area's program part's half
(`WalGS.γnw`, `walAreaRes`). -/
def walSplitFrag (Wn : List GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γnw (1 : Qp).half Wn

/-- The invariant's half of the split names (`walNamesRes`, `Inv.lean`). -/
def walSplitAuth (Wn : List GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γnw (1 : Qp).half Wn

instance walSplitFrag_timeless (Wn : List GoString) : Timeless (walSplitFrag (W := W) Wn) := by
  unfold walSplitFrag; infer_instance

instance walSplitAuth_timeless (Wn : List GoString) : Timeless (walSplitAuth (W := W) Wn) := by
  unfold walSplitAuth; infer_instance

/-- The program's half of the pending-cut flag (`WalGS.γcp`). -/
def walCutFrag (c : Option GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γcp (1 : Qp).half c

/-- The invariant's half of the pending-cut flag (`Inv.lean`'s `walDirKeys`). -/
def walCutAuth (c : Option GoString) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γcp (1 : Qp).half c

instance walCutAuth_timeless (c : Option GoString) : Timeless (walCutAuth (W := W) c) := by
  unfold walCutAuth; infer_instance

/-- **The tails' authority, the program's half** (`WalGS.γt`; the invariant's half is `walTailsAuth`,
in `walTailsRes`, `Inv.lean`): the lock token's (`T` empty: no open handle has a tail record while the
lock is free) or the lock holder's, with the tails it registered. A change is in flight only on a
registered tail (`TailsOnly`, `Inv.lean`), so a holder whose half is empty knows that none is in flight
(`walTailsRes_none`): it can put back every segment it took (`openAtIndex`'s error arms, a failed
`ReadAll`). Registering or removing a tail takes both halves. -/
def walTailsFrag (T : GMap GoString GName) : IProp GF :=
  letI := walAllG (W := W)
  ghostMapAuth W.γt (1 : Qp).half T

instance walTailsFrag_timeless (T : GMap GoString GName) : Timeless (walTailsFrag (W := W) T) := by
  unfold walTailsFrag; infer_instance

/-- **The generation's lock token** (exclusive; as `AbsDisk`'s), with the parking flag at `true`:
no handle holds the program's halves of the WALs' files (the invariant parks them all, `walParked`),
so that `Open`, holding it, can take them; no cut's rename pending (`walCutFrag none`); and the
empty record of what is out (`walOutFrag`: taking the lock hands it to the taker, who updates it with
what it takes and must bring it back empty to release the lock); and the program's half of the tails'
authority, empty (`walTailsFrag`: no tail registered; the taker likewise); and no WAL name's registration
pending (`walNamesFrag none`: every present WAL's name registered, so paths to its directory can be
built, `NameClaims.lean`; the taker likewise; G-spine, W1 log). -/
def walUnlockedTok : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) true ∗ walCutFrag (W := W) none ∗
    walOutFrag (W := W) WalOut.empty ∗ walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none)

/-- **The lock token as an open handle holds it**: the parking flag at `false` (the handle may hold
program halves the invariant would otherwise park), no cut's rename pending (a cut sets the flag to
its directory at the rename and back to `none` at the directory's sync: `walCut_begin`/`_end`).
`walHandleP` and `walOpenW` carry it; `Close` returns `walUnlockedTok` after parking what the
handle holds (`walPark_set`). -/
def walLockedTok : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) false ∗ walCutFrag (W := W) none)

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
with the names `N` and history `h` of the area directory's claim it renames in. **At most one**, and
while there is one the invariant holds the free lock token (`walUnlockedTok`: the parking flag stays
`true`, so every program half stays parked), which `Create` deposits where it makes the entry
(`walCreating_mint`) and gets back where the entry goes (`walCreating_delete`: the commit, which then
takes the lock, or the abort, which gives it back free with nothing out). So the map is empty wherever
a program holds the lock token, free or taken: at the minting (no other entry, so none with the same
directory, `CreatingNew`), at the drop, and at `Close`'s unparking (W4 log, eighth and tenth
sessions; the tenth moved the token from the taken one to the free one, for the abort). -/
def walCreatingAuth (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) : IProp GF :=
  letI := walAllG (W := W)
  iprop(ghostMapAuth W.γcr 1 CR ∗
    (⌜CR = ∅⌝ ∨ ⌜∃ d x, CR = <[d := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))⌝ ∗
      walUnlockedTok (W := W)))

instance walCreatingAuth_timeless (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) :
    Timeless (walCreatingAuth (W := W) CR) := by
  unfold walCreatingAuth walUnlockedTok walParkFrag walCutFrag walOutFrag walTailsFrag walNamesFrag
  infer_instance

/-- **`Create` of `dir` is renaming in the area claim of names `N`, history `h`** (exclusive, the
program's): the invariant holds half of that claim (`walInvBody`'s `CreatingOk`), so a client update
opened at the rename's step, where the file system's shared invariant cannot be opened to compare
claim keys, finds it; `J` is the new WAL's directory, renamed in. -/
def walCreating (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γcr] (N, h, J)

instance walCreating_timeless (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    Timeless (walCreating (W := W) dir N h J) := by
  unfold walCreating; infer_instance

/-- **The authority of the WAL directories' claim keys** (the invariant's, `DirKeysOk`), with a
copy of every key (persistent), so that a holder of the lock finds the key of a WAL keyed earlier in
the generation (`walDirKeysAuth_get`: `Open`'s pin, after a `Close`). -/
def walDirKeysAuth (K : GMap GoString (Fs.Ino × List GoString)) : IProp GF :=
  letI := walAllG (W := W)
  iprop(ghostMapAuth W.γdk 1 K ∗ [∗map] dir ↦ x ∈ K, dir ↪[W.γdk]□ x)

instance walDirKeysAuth_timeless (K : GMap GoString (Fs.Ino × List GoString)) :
    Timeless (walDirKeysAuth (W := W) K) := by
  unfold walDirKeysAuth; infer_instance

/-- **The WAL in `dir` has its directory `j`, claimed on all names but `X`** (persistent): the
invariant holds half of that claim, once among its claims, the only claim of `j` holding a `.wal`
name (`DirKeysOk`); an open handle holds the other half, which it can then match to the invariant's
at an update's opening, where the file system's shared invariant cannot be opened. Made by
`Create`'s commit and by `ReadAll`; fixed for the generation. -/
def walDirKey (dir : GoString) (j : Fs.Ino) (X : List GoString) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γdk]□ (j, X)

instance walDirKey_persistent (dir : GoString) (j : Fs.Ino) (X : List GoString) :
    Persistent (walDirKey (W := W) dir j X) := by
  unfold walDirKey; infer_instance

instance walDirKey_timeless (dir : GoString) (j : Fs.Ino) (X : List GoString) :
    Timeless (walDirKey (W := W) dir j X) := by
  unfold walDirKey; infer_instance

/-- **The purge's right on the open WAL `w` in `dir`** (exclusive; as `AbsDisk`'s). -/
def walPurgeW (w : Loc) (dir : GoString) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ γ : GName, walHandleDir (W := W) w dir γ ∗ γ ↪[W.γhp] ())

/-- **The tails' authority** (the WAL invariant's): the directories with an open handle, each to
the ghost name of its tail (`walTailsRes`, `Inv.lean`); half of it, the other the program's
(`walTailsFrag`). -/
def walTailsAuth (T : GMap GoString GName) : IProp GF :=
  letI := walAllG (W := W)
  ghostMapAuth W.γt (1 : Qp).half T

instance walTailsAuth_timeless (T : GMap GoString GName) : Timeless (walTailsAuth (W := W) T) := by
  unfold walTailsAuth; infer_instance

/-- The two halves of the tails' authority agree. -/
theorem walTails_agree (T T' : GMap GoString GName) :
    ⊢@{IProp GF} walTailsAuth (W := W) T -∗ walTailsFrag (W := W) T' -∗ ⌜T = T'⌝ := by
  unfold walTailsAuth walTailsFrag
  letI := walAllG (W := W)
  exact ghostMapAuth_agree _ _ _ _ _

/-- **The open handle of `dir` names its tail `γ`** (the handle's, exclusive). -/
def walTailKey (dir : GoString) (γ : GName) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γt] γ

/-- **The lent tails' authority** (the invariant's, `walLentRes`): each lent directory to its tail
record's name, the length of its `old`, and whether it is registered, not yet zeroed (`true`, I3b,
`wal-tc15`) or lent by its key's holder (`false`). -/
def walLentAuth (M : GMap GoString (GName × Nat × Bool)) : IProp GF :=
  letI := walAllG (W := W)
  ghostMapAuth W.γl 1 M

instance walLentAuth_timeless (M : GMap GoString (GName × Nat × Bool)) :
    Timeless (walLentAuth (W := W) M) := by
  unfold walLentAuth; infer_instance

/-- **The tail of `dir`, record `γ`, lent to the invariant, its `old` `k` long** (exclusive; I3b,
`wal-tc14`), of kind `p`: while it is out, the invariant holds the tail's key (`walTailKey dir γ`), so
no step that needs the key (an append, a cut, `Close`) runs on the tail, and the layout's `old` stays
`k` long; the steps of a resize (`walInvBody_tailW`) take this token in place of the key. Kind `false`
(`walLentTok`): lent by the key's holder, F-Z (`TailZeros`) holds; kind `true` (`walPendTok`, `wal-tc15`):
registered, not yet zeroed, F-Z or nothing written past the start's frames (`TailZ0`). -/
def walLentTokB (dir : GoString) (γ : GName) (k : Nat) (p : Bool) : IProp GF :=
  letI := walAllG (W := W)
  dir ↪[W.γl] (γ, k, p)

/-- A tail lent by its key's holder (`walLentTokB`, kind `false`). -/
abbrev walLentTok (dir : GoString) (γ : GName) (k : Nat) : IProp GF := walLentTokB (W := W) dir γ k false

/-- **A tail registered, not yet zeroed** (`walLentTokB`, kind `true`; I3b, `wal-tc15`): `ReadAll`'s
registration of an idle tail hands it out in place of the key; the fdatasync after `ZeroToEnd` turns
it into the key (`walLentRes_unpend`). -/
abbrev walPendTok (dir : GoString) (γ : GName) (k : Nat) : IProp GF := walLentTokB (W := W) dir γ k true

instance walLentTokB_timeless (dir : GoString) (γ : GName) (k : Nat) (p : Bool) :
    Timeless (walLentTokB (W := W) dir γ k p) := by
  unfold walLentTokB; infer_instance

theorem walLentTok_lookup (M : GMap GoString (GName × Nat × Bool)) (dir : GoString) (γ : GName) (k : Nat)
    (p : Bool) :
    ⊢@{IProp GF} walLentAuth (W := W) M -∗ walLentTokB (W := W) dir γ k p -∗
      ⌜M !! dir = some (γ, k, p)⌝ := by
  unfold walLentAuth walLentTokB
  letI := walAllG (W := W)
  iintro Ha Hk
  iapply ghost_map_lookup $$ Ha Hk

theorem walLentTok_insert (M : GMap GoString (GName × Nat × Bool)) (dir : GoString) (γ : GName) (k : Nat)
    (p : Bool) (hM : M !! dir = none) :
    ⊢@{IProp GF} walLentAuth (W := W) M ==∗
      walLentAuth (W := W) (<[dir := (γ, k, p)]> M) ∗ walLentTokB (W := W) dir γ k p := by
  unfold walLentAuth walLentTokB
  letI := walAllG (W := W)
  iintro Ha
  iapply ghost_map_insert dir (γ, k, p) hM $$ Ha

theorem walLentTok_delete (M : GMap GoString (GName × Nat × Bool)) (dir : GoString) (γ : GName) (k : Nat)
    (p : Bool) :
    ⊢@{IProp GF} walLentAuth (W := W) M -∗ walLentTokB (W := W) dir γ k p ==∗
      walLentAuth (W := W) (GMap.delete dir M) := by
  unfold walLentAuth walLentTokB
  letI := walAllG (W := W)
  iintro Ha Hk
  iapply ghost_map_delete $$ Ha Hk

/-- Two keys of the same tail directory: impossible (the key is exclusive). -/
theorem walTailKey_excl (dir : GoString) (γ γ' : GName) :
    ⊢@{IProp GF} walTailKey (W := W) dir γ -∗ walTailKey (W := W) dir γ' -∗ False := by
  unfold walTailKey
  letI := walAllG (W := W)
  iintro H1 H2
  icases ghostMapElem_valid_2 _ _ _ _ _ _ $$ H1 H2 with %h
  exfalso
  exact dfrac_own_one_op_invalid _ h.1

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
  unfold walUnlockedTok walParkFrag walCutFrag walOutFrag walTailsFrag walNamesFrag; infer_instance
instance walLockedTok_timeless : Timeless (walLockedTok (W := W)) := by
  unfold walLockedTok walParkFrag walCutFrag; infer_instance

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

/-- The halves of the record of what is out agree. -/
theorem walOut_agree (o o' : WalOut) :
    ⊢@{IProp GF} walOutAuth (W := W) o -∗ walOutFrag (W := W) o' -∗ ⌜o = o'⌝ := by
  unfold walOutAuth walOutFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **Updating the record of what is out** (both halves). -/
theorem walOut_set (o1 o2 o : WalOut) :
    ⊢@{IProp GF} walOutAuth (W := W) o1 -∗ walOutFrag (W := W) o2 ==∗
      walOutAuth (W := W) o ∗ walOutFrag (W := W) o := by
  unfold walOutAuth walOutFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-- **Taking the lock** (`Open`, `Create`): with the invariant's half of the flag, the lock token
becomes the handles' (the flag `false`); the invariant's half was `true`. The taker gets the empty
record of what is out (`walOutFrag`), which it updates with what it takes out, and the program's half
of the tails' authority, empty (`walTailsFrag`), and the pending registration, `none`
(`walNamesFrag`). -/
theorem walUnlockedTok_lock (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walUnlockedTok (W := W) ==∗
      ⌜b = true⌝ ∗ walParkAuth (W := W) false ∗ walLockedTok (W := W) ∗
        walOutFrag (W := W) WalOut.empty ∗ walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none := by
  unfold walUnlockedTok walLockedTok
  iintro Ha ⟨Ht, Hf, Hc, Ho, Htf, Hn⟩
  icases walPark_agree (W := W) b true $$ Ha Hf with %hb
  imod walPark_set (W := W) b true false $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf Hc Ho Htf Hn
  ipureintro; exact hb

/-- **Releasing the lock** (`Close`, an `Open` that failed after taking it): the flag back to `true`,
with the empty record of what is out (everything put back first), no tail registered and no name
claim's program half out. -/
theorem walLockedTok_unlock (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walLockedTok (W := W) -∗
      walOutFrag (W := W) WalOut.empty -∗ walTailsFrag (W := W) ∅ -∗ walNamesFrag (W := W) none ==∗
      ⌜b = false⌝ ∗ walParkAuth (W := W) true ∗ walUnlockedTok (W := W) := by
  unfold walUnlockedTok walLockedTok
  iintro Ha ⟨Ht, Hf, Hc⟩ Ho Htf Hn
  icases walPark_agree (W := W) b false $$ Ha Hf with %hb
  imod walPark_set (W := W) b false true $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf Hc Ho Htf Hn
  ipureintro; exact hb

/-- The halves of the pending registration agree. -/
theorem walNames_agree (o o' : Option GoString) :
    ⊢@{IProp GF} walNamesAuth (W := W) o -∗ walNamesFrag (W := W) o' -∗ ⌜o = o'⌝ := by
  unfold walNamesAuth walNamesFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **Updating the pending registration** (both halves). -/
theorem walNames_set (o1 o2 o : Option GoString) :
    ⊢@{IProp GF} walNamesAuth (W := W) o1 -∗ walNamesFrag (W := W) o2 ==∗
      walNamesAuth (W := W) o ∗ walNamesFrag (W := W) o := by
  unfold walNamesAuth walNamesFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-- The halves of the split names agree. -/
theorem walSplit_agree (Wn Wn' : List GoString) :
    ⊢@{IProp GF} walSplitAuth (W := W) Wn -∗ walSplitFrag (W := W) Wn' -∗ ⌜Wn = Wn'⌝ := by
  unfold walSplitAuth walSplitFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **Updating the split names** (both halves). -/
theorem walSplit_set (Wn1 Wn2 Wn : List GoString) :
    ⊢@{IProp GF} walSplitAuth (W := W) Wn1 -∗ walSplitFrag (W := W) Wn2 ==∗
      walSplitAuth (W := W) Wn ∗ walSplitFrag (W := W) Wn := by
  unfold walSplitAuth walSplitFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-- The lock token held twice: impossible (one token). -/
theorem walLockedTok_unlocked_excl :
    ⊢@{IProp GF} walLockedTok (W := W) -∗ walUnlockedTok (W := W) -∗ False := by
  unfold walUnlockedTok walLockedTok
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The lock token held twice: impossible (one token). -/
theorem walLockedTok_excl :
    ⊢@{IProp GF} walLockedTok (W := W) -∗ walLockedTok (W := W) -∗ False := by
  unfold walLockedTok
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- **Minting `Create`'s creating token** (W4 log, eighth and tenth sessions): with the lock token
free (`walUnlockedTok`), the creating map is empty (a non-empty one holds that token); the token is
deposited with the map's one entry `dir ↦ (N, h, J)`. -/
theorem walCreating_mint (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))
    (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walUnlockedTok (W := W) ==∗
      ⌜CR = ∅⌝ ∗
      walCreatingAuth (W := W) (<[dir := (N, h, J)]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) ∗
      walCreating (W := W) dir N h J := by
  unfold walCreatingAuth
  iintro ⟨Ha, Hor⟩ Hu
  icases Hor with (%hCR | ⟨-, Hl⟩)
  · subst hCR
    unfold walCreating
    letI := walAllG (W := W)
    imod ghost_map_insert (γ := W.γcr) dir (N, h, J) (by rfl) $$ Ha with ⟨Ha, Ht⟩
    imodintro
    iframe Ht
    isplitr
    · ipureintro; rfl
    iframe Ha
    iright
    iframe Hu
    ipureintro; exact ⟨dir, (N, h, J), rfl⟩
  · iexfalso
    iapply walUnlockedTok_excl $$ Hl Hu

/-- The creating token's entry in the authority. -/
theorem walCreating_lookup (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) (dir : GoString)
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h J -∗
      ⌜CR !! dir = some (N, h, J)⌝ ∗ walCreatingAuth (W := W) CR ∗ walCreating (W := W) dir N h J := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ Ht
  icases ghost_map_lookup $$ Ha Ht with %H
  iframe Ha Ht Hor
  ipureintro; exact H

/-- **Deleting the creating token's entry** (`Create`'s commit, or its abort before the rename):
the map's one entry, so the map is empty again; the lock token back, with the empty record of what is
out. -/
theorem walCreating_delete (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) (dir : GoString)
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h J ==∗
      ⌜GMap.delete dir CR = ∅⌝ ∗ walCreatingAuth (W := W) (GMap.delete dir CR) ∗ walUnlockedTok (W := W) := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ Ht
  icases ghost_map_lookup $$ Ha Ht with %Hl
  icases Hor with (%hCR | ⟨%hs, Hk⟩)
  · subst hCR; simp at Hl
  · obtain ⟨d, x, rfl⟩ := hs
    have hd : d = dir := by
      by_cases hne : d = dir
      · exact hne
      · rw [GMap.lookup_insert_ne _ _ hne] at Hl
        simp at Hl
    subst hd
    have he : GMap.delete d (<[d := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) = ∅ :=
      GMap.delete_insert _ _ _ (by rfl)
    imod ghost_map_delete $$ Ha Ht with Ha
    imodintro
    rw [he]
    iframe Ha Hk
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl

/-- The pending-cut flag's halves agree. -/
theorem walCut_agree (c c' : Option GoString) :
    ⊢@{IProp GF} walCutAuth (W := W) c -∗ walCutFrag (W := W) c' -∗ ⌜c = c'⌝ := by
  unfold walCutAuth walCutFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **Setting the pending-cut flag** (both halves): a cut's rename sets it to its directory, the
directory's sync back to `none`. -/
theorem walCut_set (c1 c2 c : Option GoString) :
    ⊢@{IProp GF} walCutAuth (W := W) c1 -∗ walCutFrag (W := W) c2 ==∗
      walCutAuth (W := W) c ∗ walCutFrag (W := W) c := by
  unfold walCutAuth walCutFrag
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-- A directory's key is in the keys' authority. -/
theorem walDirKey_lookup (K : GMap GoString (Fs.Ino × List GoString)) (dir : GoString) (j : Fs.Ino)
    (X : List GoString) :
    ⊢@{IProp GF} walDirKeysAuth (W := W) K -∗ walDirKey (W := W) dir j X -∗ ⌜K !! dir = some (j, X)⌝ := by
  unfold walDirKeysAuth walDirKey
  letI := walAllG (W := W)
  iintro ⟨Ha, -⟩ Hk
  iapply ghost_map_lookup $$ Ha Hk

/-- **A new directory key** (`Create`'s commit, `ReadAll`), the directory without one. -/
theorem walDirKey_insert (K : GMap GoString (Fs.Ino × List GoString)) (dir : GoString) (j : Fs.Ino)
    (X : List GoString) (hK : K !! dir = none) :
    ⊢@{IProp GF} walDirKeysAuth (W := W) K ==∗
      walDirKeysAuth (W := W) (<[dir := (j, X)]> K) ∗ walDirKey (W := W) dir j X := by
  unfold walDirKeysAuth walDirKey
  letI := walAllG (W := W)
  iintro ⟨Ha, Hm⟩
  imod ghost_map_insert_persist dir (j, X) hK $$ Ha with ⟨Ha, #Hk⟩
  imodintro
  iframe Ha Hk
  iapply (BigSepM.bigSepM_insert (Φ := fun (k : GoString) (x : Fs.Ino × List GoString) =>
    iprop(k ↪[W.γdk]□ x)) hK).2
  iframe Hk Hm

/-- **A key of the generation, found in the authority** (its copy). -/
theorem walDirKeysAuth_get (K : GMap GoString (Fs.Ino × List GoString)) (dir : GoString) (j : Fs.Ino)
    (X : List GoString) (hK : K !! dir = some (j, X)) :
    ⊢@{IProp GF} walDirKeysAuth (W := W) K -∗ walDirKeysAuth (W := W) K ∗ walDirKey (W := W) dir j X := by
  unfold walDirKeysAuth walDirKey
  letI := walAllG (W := W)
  iintro ⟨Ha, #Hm⟩
  iframe Ha Hm
  iapply (BigSepM.bigSepM_lookup (Φ := fun (k : GoString) (x : Fs.Ino × List GoString) =>
    iprop(k ↪[W.γdk]□ x)) hK) $$ Hm

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

/-- **`walOpenW` without its flags** (sealed): what a cut holds of the ghost handle while its rename
is pending (`walOpenW_cut`). -/
@[no_expose] def walOpenWC (w : Loc) (dir : GoString) : IProp GF :=
  letI := walAllG (W := W)
  iprop(walHandleSt (W := W) w dir .append ∗ token W.hA.γu)

/-- **The parking and pending-cut flags out of the ghost handle** (W2's `cut`: the parking flag
`false` tells the rename's update that the handle has taken its WAL's halves out of `walParked`;
`walCut_set` to `some dir` at the rename's commit, back to `none` at the directory's sync). -/
theorem walOpenW_cut (w : Loc) (dir : GoString) :
    walOpenW (W := W) w dir ⊣⊢
      walOpenWC (W := W) w dir ∗ walParkFrag (W := W) false ∗ walCutFrag (W := W) none := by
  unfold walOpenW walOpenWC walLockedTok
  constructor
  · iintro ⟨Hs, Ht, Hf, Hc⟩; iframe Hs Ht Hf Hc
  · iintro ⟨⟨Hs, Ht⟩, Hf, Hc⟩; iframe Hs Ht Hf Hc

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

end ghost

section ghostInv
variable {GF : BundledGFunctors} [W : WalGS GF] {hlc : HasLC} [GooseExts] [GooseInterp]
  [G : GooseGlobalGS hlc GF]

/-- **What the WAL invariant holds of the ghost state, the real WAL state being `s`**: the map's
other half, below `s`'s (`walMapLe`), the past states' authority, the handles' authorities, every
WAL key in the area, and the WALs' step bound (`walStepsLb`). -/
def walGhost (s : AbsDiskState) : IProp GF :=
  letI := walAllG (W := W)
  iprop((∃ G : GMap GoString WalDur, ghostVar W.hA.γs (1 : Qp).half G ∗ ⌜walMapLe G s.wal⌝) ∗
    absPastAuth W.hA s ∗ walHandleAuth (W := W) ∗ ⌜walKeysInArea s⌝ ∗ walStepsLb s)

instance walGhost_timeless (s : AbsDiskState) : Timeless (walGhost (W := W) s) := by
  letI := walAllG (W := W)
  unfold walGhost absPastAuth; infer_instance

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
  iintro ⟨-, -, -, %hk, -⟩
  ipureintro; exact hk

/-- **One purge right per handle.** -/
theorem walGhost_keys_keep (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walGhost (W := W) s ∗ ⌜walKeysInArea s⌝ := by
  unfold walGhost
  iintro ⟨Hs, HP, Hh, %hk, #Hst⟩
  iframe Hs HP Hh Hst
  isplitl <;> ipureintro <;> exact hk

/-- **The WALs' step bound, read off the ghost state** (persistent). -/
theorem walGhost_steps (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walGhost (W := W) s ∗ walStepsLb s := by
  unfold walGhost
  iintro ⟨Hs, HP, Hh, %hk, #Hst⟩
  iframe Hs HP Hh Hst
  ipureintro; exact hk

theorem walPurgeW_excl (γ : GName) :
    ⊢@{IProp GF} (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗
      (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗ False := by
  letI := walAllG (W := W)
  iintro H1 H2
  icases ghostMapElem_valid_2 γ _ (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2 with %Hv
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- **The ghost state at a bigger real state, a counted step's receipt `⧖ n'` deposited** (an
append's commit: the WAL's history one longer, within `n'`): the map set to the new state's, the past
states kept, and the new state's fact. -/
theorem walGhost_updR (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (n' : Nat)
    (hst : ∀ n, WalsStepped s n → WalsStepped s' (max n n')) :
    ⊢@{IProp GF} ⧖ n' -∗ walGhost (W := W) s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhost (W := W) s' ∗ walOwn (W := W) s'.wal ∗ walPast (W := W) s' := by
  iintro #Hn' Hc HM
  icases walOwn_agree $$ Hc HM with %HMs
  unfold walGhost walOwn walOwnAt walPast
  letI := walAllG (W := W)
  icases Hc with ⟨⟨%G, Hs, -⟩, HP, Hh, %Hk, #Hst⟩
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
  isplitr
  · ipureintro; exact hk Hk
  iapply walStepsLb_upd s s' n' hst $$ Hn' Hst

/-- **The ghost state at a bigger real state** (a step's update, no WAL's history longer than the
bound): the map set to the new state's, the past states kept, and the new state's fact. -/
theorem walGhost_upd (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (hst : ∀ n, WalsStepped s n → WalsStepped s' n) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhost (W := W) s' ∗ walOwn (W := W) s'.wal ∗ walPast (W := W) s' := by
  iintro Hc HM
  imod preceipt_zero (GF := GF) with #H0
  iapply walGhost_updR s s' M hle hk 0 (fun n hn => by rw [Nat.max_zero]; exact hst n hn) $$ H0 Hc HM

/-- **The ghost state at a bigger real state, the program's map unchanged.** -/
theorem walGhost_upd_lag (s s' : AbsDiskState) (hlag : ∀ G, walMapLe G s.wal → walMapLe G s'.wal)
    (hle : absLe s s') (hk : walKeysInArea s → walKeysInArea s')
    (hst : ∀ n, WalsStepped s n → WalsStepped s' n) :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s' ∗ walPast (W := W) s' := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨⟨%G, Hs, %HG⟩, HP, Hh, %Hk, #Hst⟩
  ihave HP := absPast_grow _ s s' hle $$ HP
  imod absPast_snap _ s' $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe HP Hh Hp
  isplitl [Hs]
  · iexists G; iframe Hs; ipureintro; exact hlag G HG
  isplitr
  · ipureintro; exact hk Hk
  iapply walStepsLb_mono s s' hst $$ Hst

/-- A past state's fact, from the authority. -/
theorem walGhost_past (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s ∗ walPast (W := W) s := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨Hs, HP, Hh, Hk⟩
  imod absPast_snap _ s $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe Hs HP Hh Hk Hp

end ghostInv

/-! ## A generation's start -/

section init
variable {GF : BundledGFunctors} {hlc : HasLC} [GooseExts] [GooseInterp] [G : GooseGlobalGS hlc GF]

/-- **A new generation's ghost state** at the real state `s` (every WAL key in the area): the
invariant's part, the program's map at `s.wal`, `s`'s fact, the lock token and the crash token; the
WALs' step bound carried over (`walStepsLb`: a crash keeps a prefix of each history). -/
theorem walGhost_init (hPre : AbsDiskGpreS GF) (s : AbsDiskState) (hk : walKeysInArea s) :
    ⊢@{IProp GF} walStepsLb s -∗ |==> ∃ W : WalGS GF, walGhost (W := W) s ∗ walOwn (W := W) s.wal ∗
      walPast (W := W) s ∗ walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗
      walCreatingAuth (W := W) ∅ ∗ walTailsAuth (W := W) ∅ ∗ walParkAuth (W := W) true ∗
      walDirKeysAuth (W := W) ∅ ∗ walCutAuth (W := W) none ∗ walOutAuth (W := W) WalOut.empty ∗
      walNamesAuth (W := W) none ∗ walSplitAuth (W := W) [] ∗ walSplitFrag (W := W) [] ∗
      walLentAuth (W := W) ∅ := by
  iintro #Hstp
  imod absDisk_local_init hPre s hk with ⟨%hA, Hctx, Hst⟩
  letI := hA.absDiskAllG
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := WalMode)) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Loc × GoString)) with ⟨%γhd, Hhd⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Unit)) with ⟨%γhp, Hhp⟩
  imod token_alloc (GF := GF) with ⟨%γc, Hc⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Fs.NameSet × Fs.NamesH × Fs.Ino))
    with ⟨%γcr, Hcr⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GName)) with ⟨%γt, Ht⟩
  imod (ghostVar_alloc (GF := GF) true) with ⟨%γpk, Hpk⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Fs.Ino × List GoString))
    with ⟨%γdk, Hdk⟩
  imod (ghostVar_alloc (GF := GF) (none : Option GoString)) with ⟨%γcp, Hcp⟩
  imod (ghostVar_alloc (GF := GF) WalOut.empty) with ⟨%γpo, Hpo⟩
  imod (ghostVar_alloc (GF := GF) (none : Option GoString)) with ⟨%γnm, Hnm⟩
  imod (ghostVar_alloc (GF := GF) ([] : List GoString)) with ⟨%γnw, Hnw⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := GName × Nat × Bool)) with ⟨%γl, Hl⟩
  iexists ⟨hA, γh, γhd, γhp, γc, γcr, γt, γpk, γdk, γcp, γpo, γnm, γnw, γl⟩
  icases (ghostVar_split_half (GF := GF) γnm 1 (none : Option GoString)).1 $$ Hnm with ⟨Hnm1, Hnm2⟩
  icases (ghostVar_split_half (GF := GF) γnw 1 ([] : List GoString)).1 $$ Hnw with ⟨Hnw1, Hnw2⟩
  icases (ghostVar_split_half (GF := GF) γpo 1 WalOut.empty).1 $$ Hpo with ⟨Hpo1, Hpo2⟩
  icases (ghostMapAuth_halves (GF := GF) γt (∅ : GMap GoString GName)).1 $$ Ht with ⟨Ht1, Ht2⟩
  icases (ghostVar_split_half (GF := GF) γpk 1 true).1 $$ Hpk with ⟨Hpk1, Hpk2⟩
  icases (ghostVar_split_half (GF := GF) γcp 1 (none : Option GoString)).1 $$ Hcp with ⟨Hcp1, Hcp2⟩
  imodintro
  iunfold absDiskCtx at Hctx
  icases Hctx with ⟨Hs, HP, -, -⟩
  iunfold absDiskStart at Hst
  icases Hst with ⟨HM, Hp, Hu⟩
  unfold walGhost walOwn walPast walUnlockedTok walCrashTok walHandleAuth walCreatingAuth walTailsAuth
    walParkFrag walParkAuth walDirKeysAuth walCutFrag walCutAuth walOutFrag walOutAuth walTailsFrag
    walNamesFrag walNamesAuth walSplitFrag walSplitAuth walLentAuth walAllG
  iframe Hs HP HM Hp Hu Hc Hcr Ht1 Ht2 Hpk1 Hpk2 Hdk Hcp1 Hcp2 Hpo1 Hpo2 Hnm1 Hnm2 Hnw1 Hnw2 Hl
  isplitl [Hh Hhd Hhp]
  · isplitl [Hh Hhd Hhp]
    · iexists 0, ∅, ∅, ∅
      iframe Hh Hhd Hhp
      ipureintro; intro k _; exact ⟨rfl, rfl, rfl⟩
    · isplitr
      · ipureintro; exact hk
      · iexact Hstp
  · isplitr
    · ileft; ipureintro; rfl
    · iapply BigSepM.bigSepM_empty.2; iempintro

end init

end WalFs
end EtcdGrove
end Perennial

end
