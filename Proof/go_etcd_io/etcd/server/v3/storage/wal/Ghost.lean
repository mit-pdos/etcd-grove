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
are imported (through the part's generated copy, `GooseLang/Ext/AbsDisk/Specs.lean`,
`etc/gen-part-copies.py`), not restated: the state's order (`AbsDiskState`, `absLe`, `walMapLe`, `walDurLe`,
`walOptLe`, `walKeysInArea`, `WalMode`) and the generation-generic ghost pieces stated for any
`hL : AbsDiskGS GF` (`walOwnAt`, `absPastAt`, `absPastAuth`, `absPast_le`/`_grow`/`_snap`,
`absDisk_local_init`). Nothing of the extension's steps or interpretation is used. When `AbsDisk/`
is deleted, these move here.
-/
module

public import GooseLang.Ext.AbsDisk.Specs
public import GooseLang.Ext.Fs.NamesGhost
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpNames

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
  /-- The open handles' locked ranges (`walLksAuth`/`walLkFrag`; unit `locks`, session 4): a ghost map
  from a WAL directory with an open handle to a history position `b` at most the WAL's `unl`
  (`LksOk`), the authority in `walGhost`, each element (exclusive) the handle's: every `.wal` name of
  the directory whose segment the handle does not keep locked ends at or before `b`. -/
  γlk : GName
  /-- **The WALs' incarnations** (P6b, `notes/wal-p6b-design.md`, v2): a ghost variable of a
  `GMap GoString Nat`, each WAL directory to its incarnation (`incOf`, absent = 0), bumped when the WAL
  in it is discarded (`DiscardUnsaved`). Allocated at `∅`; not yet used (the swap is P6b's next step). -/
  γI : GName
  /-- **The past states with their incarnations** (`walPastI`/`walPastIAuth`, P6b v2): persistent
  elements of a ghost map keyed by `(s, I)`, all below the present under `walLeI`. Not yet used. -/
  γpi : GName
  /-- The generation's roots (the shared invariant's, `osSharedInv R`; `walAreaOk` says they are its `R`):
  the call permission a WAL handle holds is of its directory's key, `osCallPerm (callKey W.roots dir) q`
  (the key of the area's root, which holds the WAL directories), so that a sealed handle predicate,
  which names no roots, names its key. -/
  roots : List (GoString × Fs.Ino)

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

/-! ## Incarnations (P6b v2, `notes/wal-p6b-design.md`; not yet used by `walGhost`)

A WAL directory's incarnation is a ghost counter, bumped when its WAL is discarded
(`DiscardUnsaved`), so that the persistent facts of a discarded WAL (keyed by the incarnation) say
nothing of a WAL `Create` makes later at the same directory. The past states are paired with the
incarnations (`walPastI`), ordered by `walLeI`: a WAL may go (or anything happen to it) only where its
incarnation grows; where it stays, the WAL stays and grows as `absLe` has it. -/

/-- **The incarnation of `dir`** in `I` (0 where `I` has none). -/
def incOf (I : GMap GoString Nat) (dir : GoString) : Nat := (I !! dir).getD 0

@[simp] theorem incOf_empty (dir : GoString) : incOf (∅ : GMap GoString Nat) dir = 0 := by
  unfold incOf; rw [GMap.lookup_empty]; rfl

/-- **The order on past states with incarnations**: the area and the durable directories kept,
every incarnation at least as high, and every WAL whose incarnation is unchanged kept and grown. -/
def walLeI (p p' : AbsDiskState × GMap GoString Nat) : Prop :=
  p'.1.area = p.1.area ∧
  (∀ d, p.1.dirs !! d = some () → p'.1.dirs !! d = some ()) ∧
  (∀ dir, incOf p.2 dir ≤ incOf p'.2 dir) ∧
  ∀ dir d, p.1.wal !! dir = some d → incOf p'.2 dir = incOf p.2 dir →
    ∃ d', p'.1.wal !! dir = some d' ∧
      d.m ≤ d'.m ∧ d.H.length ≤ d'.H.length ∧ (d.named = true → d'.named = true)

theorem walLeI_refl (p : AbsDiskState × GMap GoString Nat) : walLeI p p :=
  ⟨rfl, fun _ h => h, fun _ => Nat.le_refl _, fun _ d h _ => ⟨d, h, Nat.le_refl _, Nat.le_refl _, id⟩⟩

theorem walLeI_trans {p1 p2 p3 : AbsDiskState × GMap GoString Nat} (h12 : walLeI p1 p2)
    (h23 : walLeI p2 p3) : walLeI p1 p3 := by
  refine ⟨h23.1.trans h12.1, fun d h => h23.2.1 d (h12.2.1 d h),
    fun dir => Nat.le_trans (h12.2.2.1 dir) (h23.2.2.1 dir), fun dir d h he => ?_⟩
  have e12 : incOf p2.2 dir = incOf p1.2 dir :=
    Nat.le_antisymm (he ▸ h23.2.2.1 dir) (h12.2.2.1 dir)
  have e23 : incOf p3.2 dir = incOf p2.2 dir := by rw [he, e12]
  obtain ⟨d2, h2, hm2, hl2, hn2⟩ := h12.2.2.2 dir d h e12
  obtain ⟨d3, h3, hm3, hl3, hn3⟩ := h23.2.2.2 dir d2 h2 e23
  exact ⟨d3, h3, Nat.le_trans hm2 hm3, Nat.le_trans hl2 hl3, fun x => hn3 (hn2 x)⟩

/-- A step of `absLe`, the incarnations unchanged. -/
theorem walLeI_of_absLe {s s' : AbsDiskState} (I : GMap GoString Nat) (h : absLe s s') :
    walLeI (s, I) (s', I) :=
  ⟨h.1, h.2.1, fun _ => Nat.le_refl _, fun dir d hd _ => h.2.2 dir d hd⟩

/-- **The discard of `dir`'s WAL** (`DiscardUnsaved`'s commit): the WAL gone, its incarnation bumped. -/
theorem walLeI_discard (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) :
    walLeI (s, I) ({ s with wal := GMap.delete dir s.wal }, <[dir := incOf I dir + 1]> I) := by
  have hinc : ∀ k, incOf (<[dir := incOf I dir + 1]> I) k =
      if k = dir then incOf I dir + 1 else incOf I k := by
    intro k
    unfold incOf
    by_cases e : k = dir
    · subst e; rw [GMap.lookup_insert_eq]; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; simp [e]
  refine ⟨rfl, fun _ h => h, fun k => ?_, fun k d hd he => ?_⟩
  · show incOf I k ≤ _
    rw [hinc k]
    by_cases e : k = dir
    · subst e; simp
    · simp [e]
  · rw [hinc k] at he
    by_cases e : k = dir
    · simp [e] at he
    · simp only [e, ite_false] at he
      refine ⟨d, ?_, Nat.le_refl _, Nat.le_refl _, id⟩
      show (GMap.delete dir s.wal) !! k = some d
      rw [GMap.lookup_delete_ne _ (Ne.symm e)]; exact hd

instance : DecidableEq (AbsDiskState × GMap GoString Nat) := fun a b => Classical.propDecidable (a = b)


section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- The universal camera. -/
abbrev walAllG : AllG GF := W.hA.absDiskAllG

/-- **The WAL state was `p.1` with incarnations `p.2` at some point of this generation**
(persistent; with its area, the generation's one, `walArea_agree`). -/
def walPastI (p : AbsDiskState × GMap GoString Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop(p ↪[W.γpi]□ () ∗ () ↪[W.hA.γa]□ p.1.area)

instance walPastI_persistent (p : AbsDiskState × GMap GoString Nat) :
    Persistent (walPastI (W := W) p) := by unfold walPastI; infer_instance

instance walPastI_timeless (p : AbsDiskState × GMap GoString Nat) :
    Timeless (walPastI (W := W) p) := by unfold walPastI; infer_instance

/-- **The authority of the past states with incarnations**, all below `p` (`walLeI`), and `p`'s
area. -/
def walPastIAuth (p : AbsDiskState × GMap GoString Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ F : GMap (AbsDiskState × GMap GoString Nat) Unit, ghostMapAuth W.γpi 1 F ∗
    ([∗map] q ↦ _u ∈ F, q ↪[W.γpi]□ ()) ∗ ⌜∀ q, F !! q = some () → walLeI q p⌝ ∗
    () ↪[W.hA.γa]□ p.1.area)

instance walPastIAuth_timeless (p : AbsDiskState × GMap GoString Nat) :
    Timeless (walPastIAuth (W := W) p) := by unfold walPastIAuth; infer_instance

/-- What a past state says of the present one. -/
theorem walPastI_le (p q : AbsDiskState × GMap GoString Nat) :
    ⊢@{IProp GF} walPastIAuth (W := W) p -∗ walPastI (W := W) q -∗ ⌜walLeI q p⌝ := by
  letI := walAllG (W := W)
  unfold walPastIAuth walPastI
  iintro ⟨%F, HA, -, %Hle, -⟩ ⟨Hq, -⟩
  icases ghost_map_lookup $$ HA Hq with %Hl
  ipureintro; exact Hle q Hl

/-- The authority at a bigger present. -/
theorem walPastI_grow (p p' : AbsDiskState × GMap GoString Nat) (hle : walLeI p p') :
    ⊢@{IProp GF} walPastIAuth (W := W) p -∗ walPastIAuth (W := W) p' := by
  letI := walAllG (W := W)
  unfold walPastIAuth
  iintro ⟨%F, HA, HE, %Hle, #Ha⟩
  iexists F
  iframe HA HE
  isplitr
  · ipureintro; exact fun q hq => walLeI_trans (Hle q hq) hle
  · rw [hle.1]; iexact Ha

/-- The present's fact. -/
theorem walPastI_snap (p : AbsDiskState × GMap GoString Nat) :
    ⊢@{IProp GF} walPastIAuth (W := W) p ==∗ walPastIAuth (W := W) p ∗ walPastI (W := W) p := by
  letI := walAllG (W := W)
  unfold walPastIAuth walPastI
  iintro ⟨%F, HA, #HE, %Hle, #Ha⟩
  cases hF : F !! p with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := F)
      (Φ := fun q _ => iprop(q ↪[W.γpi]□ ())) hF).1 $$ HE with ⟨#Hs, -⟩
    imodintro
    isplitl [HA]
    · iexists F; iframe HA HE Ha; ipureintro; exact Hle
    · iframe Hs Ha
  | none =>
    imod ghost_map_insert_persist p () hF $$ HA with ⟨HA, #Hs⟩
    imodintro
    isplitl [HA]
    · iexists (F.insert p ())
      iframe HA Ha
      isplitl
      · iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := F)
          (Φ := fun q _ => iprop(q ↪[W.γpi]□ ())) hF).2
        iframe HE; iexact Hs
      · ipureintro
        intro q hq
        rw [GMap.lookup_insert_eq_iff] at hq
        by_cases hqp : p = q
        · subst hqp; exact walLeI_refl p
        · simp only [hqp, ite_false] at hq; exact Hle q hq
    · iframe Hs Ha

/-- **A quarter of the incarnations** (`WalGS.γI`): the views' (`walDirIs`, `walDirIsI`) and the lock
token's (`walIncAny` in `walUnlockedTok`, `walLockedTokI` in an open handle); `walGhost` holds the half. The
incarnations change only with all three (the discard), so neither under the program's view nor under an
open handle. -/
def walIncQ (I : GMap GoString Nat) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar W.γI (1 : Qp).half.half I

instance walIncQ_timeless (I : GMap GoString Nat) : Timeless (walIncQ (W := W) I) := by
  unfold walIncQ; infer_instance

/-- The lock's quarter of the incarnations, at some value (the free lock token's). -/
def walIncAny : IProp GF := iprop(∃ I : GMap GoString Nat, walIncQ (W := W) I)

instance walIncAny_timeless : Timeless (walIncAny (W := W)) := by
  unfold walIncAny; infer_instance

/-- Two shares of the incarnations agree. -/
theorem walIncQ_agree (I I' : GMap GoString Nat) (q : Qp) :
    ⊢@{IProp GF} walIncQ (W := W) I -∗ (letI := walAllG (W := W); ghostVar W.γI q I') -∗ ⌜I = I'⌝ := by
  unfold walIncQ
  letI := walAllG (W := W)
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

/-- **A fact `P` of incarnation `i` of `dir`, read at incarnations `I`**: `I`'s incarnation of `dir` is
`i` and `P` holds, or `i` is retired (`I`'s is higher): a fact about a discarded WAL says nothing of a
later one, and one about the current incarnation holds of it (`walIncFact_cur`). -/
def walIncFact (I : GMap GoString Nat) (dir : GoString) (i : Nat) (P : Prop) : Prop :=
  (incOf I dir = i ∧ P) ∨ i < incOf I dir

/-- **The program owns the WAL map, which is `M`** (half of the ghost variable, and the token). -/
def walOwn (M : GMap GoString WalDur) : IProp GF := walOwnAt W.hA M

/-- **The WAL state was `s` at some point of this generation** (persistent), at some incarnations. -/
def walPast (s : AbsDiskState) : IProp GF := iprop(∃ I : GMap GoString Nat, walPastI (W := W) (s, I))

instance walPast_persistent (s : AbsDiskState) : Persistent (walPast (W := W) s) := by
  unfold walPast; infer_instance

/-- The handles' authorities, every ghost name from `n` on unused. Sealed: only the WAL's own
proofs allocate a handle or change its mode (`walHandle_alloc`, `walHandleP_set`). -/
@[no_expose] def walHandleAuth : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (n : Nat) (Hh : GMap GName WalMode) (Hd : GMap GName (Loc × GoString × Nat))
      (Hp : GMap GName Unit),
    ghostMapAuth W.γh 1 Hh ∗ ghostMapAuth W.γhd 1 Hd ∗ ghostMapAuth W.γhp 1 Hp ∗
    ⌜∀ k, n ≤ k → Hh !! k = none ∧ Hd !! k = none ∧ Hp !! k = none⌝)

instance walHandleAuth_timeless : Timeless (walHandleAuth (W := W)) := by
  unfold walHandleAuth; infer_instance

/-- **The WAL area is `r`** (persistent). -/
def walArea (r : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, walPast (W := W) s ∗ ⌜s.area = r⌝)

/-- **The WAL directory `dir` holds `o`** (the whole map's ownership, with the program's half of the
incarnations; the mark and `named` lower bounds). -/
def walDirIs (dir : GoString) (o : Option WalDur) : IProp GF :=
  iprop(∃ (M : GMap GoString WalDur) (I : GMap GoString Nat), walOwn (W := W) M ∗ walIncQ (W := W) I ∗
    ⌜walOptLe o (M !! dir)⌝)

/-- **The WAL directory `dir`, at incarnation `i`, holds `o`.** -/
def walDirIsI (dir : GoString) (i : Nat) (o : Option WalDur) : IProp GF :=
  iprop(∃ (M : GMap GoString WalDur) (I : GMap GoString Nat), walOwn (W := W) M ∗ walIncQ (W := W) I ∗
    ⌜walOptLe o (M !! dir)⌝ ∗ ⌜incOf I dir = i⌝)

/-- **The WAL in `dir` is in the durable state `d`.** -/
def walDiskAt (dir : GoString) (d : WalDur) : IProp GF := walDirIs (W := W) dir (some d)

/-- **The WAL in `dir`, at incarnation `i`, is in the durable state `d`.** -/
def walDiskAtI (dir : GoString) (i : Nat) (d : WalDur) : IProp GF := walDirIsI (W := W) dir i (some d)

/-- **`dir` names no WAL.** -/
def walAbsent (dir : GoString) : IProp GF := walDirIs (W := W) dir none

/-- **`dir`, at incarnation `i`, names no WAL.** -/
def walAbsentI (dir : GoString) (i : Nat) : IProp GF := walDirIsI (W := W) dir i none

/-- **The first `n` operations of the history of `dir`'s WAL of incarnation `i` are synced, or `i` is
retired** (persistent; `walIncFact`). -/
def walSyncedLb (dir : GoString) (i n : Nat) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (I : GMap GoString Nat), walPastI (W := W) (s, I) ∗
    ⌜walIncFact I dir i (∃ d, s.wal !! dir = some d ∧ n ≤ d.m)⌝)

/-- **The entry of `dir`'s WAL of incarnation `i`, and its ancestors', are durable, or `i` is retired**
(persistent). -/
def walNamed (dir : GoString) (i : Nat) : IProp GF :=
  iprop(∃ (s : AbsDiskState) (I : GMap GoString Nat), walPastI (W := W) (s, I) ∗
    ⌜walIncFact I dir i (∃ d, s.wal !! dir = some d ∧ d.named = true)⌝)

/-- **`d`'s entry and its ancestors' are durable** (persistent). -/
def dirDurable (d : GoString) : IProp GF :=
  iprop(∃ s : AbsDiskState, walPast (W := W) s ∗ ⌜s.dirs !! d = some ()⌝)

/-- **The handle named `γ` is of the `*wal.WAL` `w`, which writes the WAL in `dir` of incarnation
`i`** (persistent). -/
def walHandleDirI (w : Loc) (dir : GoString) (i : Nat) (γ : GName) : IProp GF :=
  letI := walAllG (W := W)
  γ ↪[W.γhd]□ (w, dir, i)

/-- **The handle named `γ` is of the `*wal.WAL` `w`, which writes the WAL in `dir`** (persistent). -/
def walHandleDir (w : Loc) (dir : GoString) (γ : GName) : IProp GF :=
  iprop(∃ i : Nat, walHandleDirI (W := W) w dir i γ)

/-- **`w` is a handle of the WAL in `dir` of incarnation `i`, in mode `m`** (exclusive). -/
def walHandleStI (w : Loc) (dir : GoString) (i : Nat) (m : WalMode) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ γ : GName, walHandleDirI (W := W) w dir i γ ∗ γ ↪[W.γh] m)

/-- **`w` is a handle of the WAL in `dir`, in mode `m`** (exclusive). -/
def walHandleSt (w : Loc) (dir : GoString) (m : WalMode) : IProp GF :=
  iprop(∃ i : Nat, walHandleStI (W := W) w dir i m)

/-- **The open WAL `w` has written the history of its directory `dir`'s WAL of incarnation `i` up to
length `n`, or `i` is retired** (persistent). -/
def walLenLb (w : Loc) (dir : GoString) (i n : Nat) : IProp GF :=
  iprop(∃ (γ : GName) (s : AbsDiskState) (I : GMap GoString Nat),
    walHandleDir (W := W) w dir γ ∗ walPastI (W := W) (s, I) ∗
    ⌜walIncFact I dir i (∃ d, s.wal !! dir = some d ∧ n ≤ d.H.length)⌝)

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
def walTailsFrag (T : GMap GoString GName) (Lk : GMap GoString Nat := ∅) : IProp GF :=
  letI := walAllG (W := W)
  iprop(ghostMapAuth W.γt (1 : Qp).half T ∗ ghostVar W.γlk (1 : Qp).half Lk)

instance walTailsFrag_timeless (T : GMap GoString GName) (Lk : GMap GoString Nat) :
    Timeless (walTailsFrag (W := W) T Lk) := by
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
    walOutFrag (W := W) WalOut.empty ∗ walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none ∗
    walIncAny (W := W))

/-- **The free lock token but its names fragment** (`walUnlockedTok` less `walNamesFrag none`): what
`Close.spec` (state `unnamed`) returns of the handle before naming, whose names fragment is `Create`'s pending
registration (`some dir`; design P, `notes/wal-units/create.md`). With `walNamesFrag none` it is the
free token (`walUnlockedTokX_join`). -/
def walUnlockedTokX : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) true ∗ walCutFrag (W := W) none ∗
    walOutFrag (W := W) WalOut.empty ∗ walTailsFrag (W := W) ∅ ∗ walIncAny (W := W))

theorem walUnlockedTokX_join :
    walUnlockedTokX (W := W) ∗ walNamesFrag (W := W) none ⊣⊢ walUnlockedTok (W := W) := by
  unfold walUnlockedTokX walUnlockedTok
  constructor
  · iintro ⟨⟨H1, H2, H3, H4, H5, H7⟩, H6⟩
    iframe
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7⟩
    iframe

/-- **The lock token as an open handle holds it**: the parking flag at `false` (the handle may hold
program halves the invariant would otherwise park), no cut's rename pending (a cut sets the flag to
its directory at the rename and back to `none` at the directory's sync: `walCut_begin`/`_end`).
`walHandleP` and `walOpenW` carry it; `Close` returns `walUnlockedTok` after parking what the
handle holds (`walPark_set`). With the lock's quarter of the incarnations at `I` (`walLockedTok`: at
some value). -/
def walLockedTokI (I : GMap GoString Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop(token W.hA.γu ∗ walParkFrag (W := W) false ∗ walCutFrag (W := W) none ∗ walIncQ (W := W) I)

/-- The lock token as an open handle holds it (`walLockedTokI` at some incarnations). -/
def walLockedTok : IProp GF := iprop(∃ I : GMap GoString Nat, walLockedTokI (W := W) I)

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
  iprop(∃ (γ : GName) (i : Nat) (I : GMap GoString Nat), walHandleDirI (W := W) w dir i γ ∗
    γ ↪[W.γh] m ∗ γ ↪[W.γhp] () ∗ walLockedTokI (W := W) I ∗ ⌜incOf I dir = i⌝)

/-- **The key of the cleanup's pin in the creating map** (`walCreatingAuth`'s third case; W4,
`notes/wal-units/create.md`, session 4): no WAL directory (`child r nm` is not empty). `Create`'s
cleanup after its commit pins there the area claim its `cleanupWAL` renames in (`nm` onto
`nm.broken.<time>`), so that the rename's update, opened inside the `os` step, finds the invariant's
half of it, as the commit's update finds the creating entry's. -/
def cleanKey : GoString := []

/-- **The authority of the WALs being created** (the invariant's): each directory `Create` works on,
with the names `N` and history `h` of the area directory's claim it renames in. **At most one**, and
while there is one the invariant holds the free lock token (`walUnlockedTok`: the parking flag stays
`true`, so every program half stays parked), which `Create` deposits where it makes the entry
(`walCreating_mint`) and gets back where the entry goes (`walCreating_delete`: the commit, which then
takes the lock, or the abort, which gives it back free with nothing out). So the map is empty wherever
a program holds the lock token, free or taken: at the minting (no other entry, so none with the same
directory, `CreatingNew`), at the drop, and at `Close`'s unparking (W4 log, eighth and tenth
sessions; the tenth moved the token from the taken one to the free one, for the abort). **The
cleanup's pin** (`cleanKey ↦ (N, h, jr)`, W4 session 4): the same at most one entry, with the free token
less its names fragment (`walUnlockedTokX`: the cleanup's `Create` holds the pending registration's
`walNamesFrag (some dir)`), deposited by `walCreating_mintC` and given back by `walCreating_deleteC`. -/
def walCreatingAuth (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) : IProp GF :=
  letI := walAllG (W := W)
  iprop(ghostMapAuth W.γcr 1 CR ∗
    (⌜CR = ∅⌝ ∨ ⌜∃ d x, CR = <[d := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))⌝ ∗
      walUnlockedTok (W := W) ∨
     ⌜∃ x, CR = <[cleanKey := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))⌝ ∗
      walUnlockedTokX (W := W)))

instance walCreatingAuth_timeless (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) :
    Timeless (walCreatingAuth (W := W) CR) := by
  unfold walCreatingAuth walUnlockedTok walUnlockedTokX walParkFrag walCutFrag walOutFrag walTailsFrag
    walNamesFrag
  infer_instance

/-- **`Create` of `dir` is renaming in the area claim of names `N`, history `h`** (exclusive, the
program's): the invariant holds half of that claim (`walInvBody`'s `CreatingOk`), so a client update
opened at the rename's step, where the file system's shared invariant cannot be opened to compare
claim keys, finds it; `J` is the new WAL's directory, renamed in. -/
def walCreating (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) : IProp GF :=
  letI := walAllG (W := W)
  iprop(dir ↪[W.γcr] (N, h, J) ∗ ⌜dir ≠ cleanKey⌝)

/-- **The cleanup's pin** (exclusive, the cleanup's `Create`'s; W4 session 4): the creating map's entry
at `cleanKey`, the area claim of names `N`, history `h` its rename works in (`J` is `jr`, by
convention). -/
def walCleanPin (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) : IProp GF :=
  letI := walAllG (W := W)
  cleanKey ↪[W.γcr] (N, h, J)

instance walCleanPin_timeless (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    Timeless (walCleanPin (W := W) N h J) := by
  unfold walCleanPin; infer_instance

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
`Create`'s commit and by `ReadAll`; fixed for the generation. The names left out are the pipeline's
(`X = walTmps`, as `DirClaimsOk` has it of every WAL directory's claim): a purge, holding only the key and
the handle's half, knows every other name of the directory is in the claim (unit `locks`, session 10). -/
def walDirKey (dir : GoString) (j : Fs.Ino) (X : List GoString) : IProp GF :=
  letI := walAllG (W := W)
  iprop(dir ↪[W.γdk]□ (j, X) ∗ ⌜X = walTmps⌝)

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
theorem walTails_agree (T T' : GMap GoString GName) {Lk : GMap GoString Nat} :
    ⊢@{IProp GF} walTailsAuth (W := W) T -∗ walTailsFrag (W := W) T' Lk -∗ ⌜T = T'⌝ := by
  unfold walTailsAuth walTailsFrag
  letI := walAllG (W := W)
  iintro Ha ⟨Hf, -⟩
  iapply ghostMapAuth_agree $$ Ha Hf

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

/-- **`w` is the WAL opened in `dir`, of incarnation `i` (the current one), ready to append.** Sealed. -/
@[no_expose] def walOpenWI (w : Loc) (dir : GoString) (i : Nat) : IProp GF :=
  iprop(∃ I : GMap GoString Nat, walHandleStI (W := W) w dir i .append ∗ walLockedTokI (W := W) I ∗
    ⌜incOf I dir = i⌝)

/-- **`w` is the WAL opened in `dir`, ready to append** (at some incarnation, the current one). Sealed. -/
@[no_expose] def walOpenW (w : Loc) (dir : GoString) : IProp GF :=
  iprop(∃ i : Nat, walOpenWI (W := W) w dir i)

/-- **`w` is the WAL opened in `dir` for reading at the snapshot `s`.** Sealed. -/
@[no_expose] def walOpening (w : Loc) (dir : GoString) (s : w64 × w64) : IProp GF :=
  walHandleP (W := W) w dir (.opening s)

/-- **`w`'s `ReadAll` in `dir` failed.** Sealed. -/
@[no_expose] def walReadFailed (w : Loc) (dir : GoString) : IProp GF :=
  walHandleP (W := W) w dir .failed

instance walArea_persistent (r : GoString) : Persistent (walArea (W := W) r) := by
  unfold walArea; infer_instance
instance walSyncedLb_persistent (dir : GoString) (i n : Nat) :
    Persistent (walSyncedLb (W := W) dir i n) := by unfold walSyncedLb; infer_instance
instance walNamed_persistent (dir : GoString) (i : Nat) : Persistent (walNamed (W := W) dir i) := by
  unfold walNamed; infer_instance
instance dirDurable_persistent (d : GoString) : Persistent (dirDurable (W := W) d) := by
  unfold dirDurable; infer_instance
instance walHandleDirI_persistent (w : Loc) (dir : GoString) (i : Nat) (γ : GName) :
    Persistent (walHandleDirI (W := W) w dir i γ) := by unfold walHandleDirI; infer_instance
instance walHandleDir_persistent (w : Loc) (dir : GoString) (γ : GName) :
    Persistent (walHandleDir (W := W) w dir γ) := by unfold walHandleDir; infer_instance
instance walLenLb_persistent (w : Loc) (dir : GoString) (i n : Nat) :
    Persistent (walLenLb (W := W) w dir i n) := by unfold walLenLb; infer_instance

instance walPast_timeless (s : AbsDiskState) : Timeless (walPast (W := W) s) := by
  unfold walPast; infer_instance
instance walArea_timeless (r : GoString) : Timeless (walArea (W := W) r) := by
  unfold walArea; infer_instance
instance walSyncedLb_timeless (dir : GoString) (i n : Nat) :
    Timeless (walSyncedLb (W := W) dir i n) := by unfold walSyncedLb; infer_instance
instance walNamed_timeless (dir : GoString) (i : Nat) : Timeless (walNamed (W := W) dir i) := by
  unfold walNamed; infer_instance
instance walLenLb_timeless (w : Loc) (dir : GoString) (i n : Nat) :
    Timeless (walLenLb (W := W) w dir i n) := by unfold walLenLb walHandleDir walHandleDirI; infer_instance
instance dirDurable_timeless (d : GoString) : Timeless (dirDurable (W := W) d) := by
  unfold dirDurable; infer_instance
instance walOwn_timeless (M : GMap GoString WalDur) : Timeless (walOwn (W := W) M) := by
  unfold walOwn walOwnAt; infer_instance
instance walDirIsI_timeless (dir : GoString) (i : Nat) (o : Option WalDur) :
    Timeless (walDirIsI (W := W) dir i o) := by unfold walDirIsI; infer_instance
instance walDiskAtI_timeless (dir : GoString) (i : Nat) (d : WalDur) :
    Timeless (walDiskAtI (W := W) dir i d) := by unfold walDiskAtI; infer_instance
instance walAbsentI_timeless (dir : GoString) (i : Nat) : Timeless (walAbsentI (W := W) dir i) := by
  unfold walAbsentI; infer_instance
instance walDirIs_timeless (dir : GoString) (o : Option WalDur) :
    Timeless (walDirIs (W := W) dir o) := by unfold walDirIs; infer_instance
instance walDiskAt_timeless (dir : GoString) (d : WalDur) : Timeless (walDiskAt (W := W) dir d) := by
  unfold walDiskAt; infer_instance
instance walAbsent_timeless (dir : GoString) : Timeless (walAbsent (W := W) dir) := by
  unfold walAbsent; infer_instance
instance walUnlockedTok_timeless : Timeless (walUnlockedTok (W := W)) := by
  unfold walUnlockedTok walParkFrag walCutFrag walOutFrag walTailsFrag walNamesFrag; infer_instance
instance walUnlockedTokX_timeless : Timeless (walUnlockedTokX (W := W)) := by
  unfold walUnlockedTokX walParkFrag walCutFrag walOutFrag walTailsFrag; infer_instance
instance walLockedTok_timeless : Timeless (walLockedTok (W := W)) := by
  unfold walLockedTok walLockedTokI walParkFrag walCutFrag walIncQ; infer_instance

/-! ## Laws (as `AbsDisk/Specs.lean`'s, same statements) -/

theorem walDiskAt_weaken (dir : GoString) (d d' : WalDur) (h : walDurLe d d') :
    ⊢@{IProp GF} walDiskAt (W := W) dir d' -∗ walDiskAt (W := W) dir d := by
  unfold walDiskAt walDirIs
  iintro ⟨%M, %I, HM, HI, %HMd⟩
  iexists M, I; iframe HM HI; ipureintro
  exact walOptLe_trans (o2 := some d') h HMd

theorem walDiskAtI_weaken (dir : GoString) (i : Nat) (d d' : WalDur) (h : walDurLe d d') :
    ⊢@{IProp GF} walDiskAtI (W := W) dir i d' -∗ walDiskAtI (W := W) dir i d := by
  unfold walDiskAtI walDirIsI
  iintro ⟨%M, %I, HM, HI, %HMd, %hi⟩
  iexists M, I; iframe HM HI; ipureintro
  exact ⟨walOptLe_trans (o2 := some d') h HMd, hi⟩

/-- The view at its incarnation. -/
theorem walDirIs_inc (dir : GoString) (o : Option WalDur) :
    walDirIs (W := W) dir o ⊣⊢ ∃ i, walDirIsI (W := W) dir i o := by
  unfold walDirIs walDirIsI
  constructor
  · iintro ⟨%M, %I, HM, HI, %h⟩; iexists incOf I dir, M, I; iframe HM HI; ipureintro; exact ⟨h, rfl⟩
  · iintro ⟨%i, %M, %I, HM, HI, %h, -⟩; iexists M, I; iframe HM HI; ipureintro; exact h

theorem walDirIsI_dirIs (dir : GoString) (i : Nat) (o : Option WalDur) :
    walDirIsI (W := W) dir i o ⊢ walDirIs (W := W) dir o :=
  .trans (by iintro H; iexists i; iexact H) (walDirIs_inc dir o).2

theorem walOwn_excl (M M' : GMap GoString WalDur) :
    ⊢@{IProp GF} walOwn (W := W) M -∗ walOwn (W := W) M' -∗ False := by
  unfold walOwn walOwnAt
  letI := walAllG (W := W)
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  iapply token_exclusive $$ H1 H2

theorem walDirIs_excl (dir dir' : GoString) (o o' : Option WalDur) :
    ⊢@{IProp GF} walDirIs (W := W) dir o -∗ walDirIs (W := W) dir' o' -∗ False := by
  unfold walDirIs
  iintro ⟨%M, %I, H1, -⟩ ⟨%M', %I', H2, -⟩
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
  unfold walUnlockedTok walLockedTok walLockedTokI walIncAny
  iintro Ha ⟨Ht, Hf, Hc, Ho, Htf, Hn, %I, Hi⟩
  icases walPark_agree (W := W) b true $$ Ha Hf with %hb
  imod walPark_set (W := W) b true false $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ho Htf Hn
  isplitr
  · ipureintro; exact hb
  iexists I; iframe Ht Hf Hc Hi

/-- **Releasing the lock** (`Close`, an `Open` that failed after taking it): the flag back to `true`,
with the empty record of what is out (everything put back first), no tail registered and no name
claim's program half out. -/
theorem walLockedTok_unlock (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walLockedTok (W := W) -∗
      walOutFrag (W := W) WalOut.empty -∗ walTailsFrag (W := W) ∅ -∗ walNamesFrag (W := W) none ==∗
      ⌜b = false⌝ ∗ walParkAuth (W := W) true ∗ walUnlockedTok (W := W) := by
  unfold walUnlockedTok walLockedTok walLockedTokI walIncAny
  iintro Ha ⟨%I, Ht, Hf, Hc, Hi⟩ Ho Htf Hn
  icases walPark_agree (W := W) b false $$ Ha Hf with %hb
  imod walPark_set (W := W) b false true $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf Hc Ho Htf Hn
  isplitr
  · ipureintro; exact hb
  iexists I; iexact Hi

/-- `walLockedTok_unlock` without the names fragment (`walUnlockedTokX`). -/
theorem walLockedTok_unlockX (b : Bool) :
    ⊢@{IProp GF} walParkAuth (W := W) b -∗ walLockedTok (W := W) -∗
      walOutFrag (W := W) WalOut.empty -∗ walTailsFrag (W := W) ∅ ==∗
      ⌜b = false⌝ ∗ walParkAuth (W := W) true ∗ walUnlockedTokX (W := W) := by
  unfold walUnlockedTokX walLockedTok walLockedTokI walIncAny
  iintro Ha ⟨%I, Ht, Hf, Hc, Hi⟩ Ho Htf
  icases walPark_agree (W := W) b false $$ Ha Hf with %hb
  imod walPark_set (W := W) b false true $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Ht Hf Hc Ho Htf
  isplitr
  · ipureintro; exact hb
  iexists I; iexact Hi

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
  unfold walUnlockedTok walLockedTok walLockedTokI
  letI := walAllG (W := W)
  iintro ⟨%I, H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The lock token held twice: impossible (one token). -/
theorem walLockedTok_excl :
    ⊢@{IProp GF} walLockedTok (W := W) -∗ walLockedTok (W := W) -∗ False := by
  unfold walLockedTok walLockedTokI
  letI := walAllG (W := W)
  iintro ⟨%I, H1, -⟩ ⟨%I', H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The free lock token against the free token less its names fragment (one token). -/
theorem walUnlockedTok_exclX :
    ⊢@{IProp GF} walUnlockedTok (W := W) -∗ walUnlockedTokX (W := W) -∗ False := by
  unfold walUnlockedTok walUnlockedTokX
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The taken lock token against the free token less its names fragment (one token). -/
theorem walLockedTok_exclX :
    ⊢@{IProp GF} walLockedTok (W := W) -∗ walUnlockedTokX (W := W) -∗ False := by
  unfold walLockedTok walLockedTokI walUnlockedTokX
  letI := walAllG (W := W)
  iintro ⟨%I, H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The free token less its names fragment, twice (one token). -/
theorem walUnlockedTokX_exclX :
    ⊢@{IProp GF} walUnlockedTokX (W := W) -∗ walUnlockedTokX (W := W) -∗ False := by
  unfold walUnlockedTokX
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- The free lock token gives the free token less its names fragment. -/
theorem walUnlockedTok_toX :
    walUnlockedTok (W := W) ⊢ walUnlockedTokX (W := W) := by
  iintro Hu
  icases (walUnlockedTokX_join (W := W)).2 $$ Hu with ⟨Hx, -⟩
  iexact Hx

/-- **Minting `Create`'s creating token** (W4 log, eighth and tenth sessions): with the lock token
free (`walUnlockedTok`), the creating map is empty (a non-empty one holds that token); the token is
deposited with the map's one entry `dir ↦ (N, h, J)`. -/
theorem walCreating_mint (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))
    (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) (hdk : dir ≠ cleanKey) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walUnlockedTok (W := W) ==∗
      ⌜CR = ∅⌝ ∗
      walCreatingAuth (W := W) (<[dir := (N, h, J)]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) ∗
      walCreating (W := W) dir N h J := by
  unfold walCreatingAuth
  iintro ⟨Ha, Hor⟩ Hu
  icases Hor with (%hCR | ⟨-, Hl⟩ | ⟨-, Hl⟩)
  · subst hCR
    unfold walCreating
    letI := walAllG (W := W)
    imod ghost_map_insert (γ := W.γcr) dir (N, h, J) (by rfl) $$ Ha with ⟨Ha, Ht⟩
    imodintro
    iframe Ht
    isplitr
    · ipureintro; rfl
    isplitl [Ha Hu]
    · iframe Ha
      iright; ileft
      iframe Hu
      ipureintro; exact ⟨dir, (N, h, J), rfl⟩
    · ipureintro; exact hdk
  · iexfalso
    iapply walUnlockedTok_excl $$ Hl Hu
  · iexfalso
    iapply walUnlockedTok_exclX $$ Hu Hl

/-- The creating token's entry in the authority. -/
theorem walCreating_lookup (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) (dir : GoString)
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h J -∗
      ⌜CR !! dir = some (N, h, J)⌝ ∗ walCreatingAuth (W := W) CR ∗ walCreating (W := W) dir N h J := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ ⟨Ht, %hdk⟩
  icases ghost_map_lookup $$ Ha Ht with %H
  iframe Ha Ht Hor
  isplitr
  · ipureintro; exact H
  ipureintro; exact hdk

/-- A creating token's directory is not the cleanup's key. -/
theorem walCreating_ne (dir : GoString) (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreating (W := W) dir N h J -∗
      ⌜dir ≠ cleanKey⌝ ∗ walCreating (W := W) dir N h J := by
  unfold walCreating
  iintro ⟨Ht, %hdk⟩
  iframe Ht
  isplitr <;> ipureintro <;> exact hdk

/-- **Deleting the creating token's entry** (`Create`'s commit, or its abort before the rename):
the map's one entry, so the map is empty again; the lock token back, with the empty record of what is
out. -/
theorem walCreating_delete (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) (dir : GoString)
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCreating (W := W) dir N h J ==∗
      ⌜GMap.delete dir CR = ∅⌝ ∗ walCreatingAuth (W := W) (GMap.delete dir CR) ∗ walUnlockedTok (W := W) := by
  unfold walCreatingAuth walCreating
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ ⟨Ht, %hdk⟩
  icases ghost_map_lookup $$ Ha Ht with %Hl
  icases Hor with (%hCR | ⟨%hs, Hk⟩ | ⟨%hs, -⟩)
  · subst hCR; simp at Hl
  rotate_left
  · exfalso
    obtain ⟨x, rfl⟩ := hs
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hdk)] at Hl
    simp at Hl
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

/-- **Minting the cleanup's pin** (W4 session 4, `cleanKey`): with the free token less its names
fragment (the cleanup's `Create`'s), the creating map is empty (a non-empty one holds the lock
token); the token is deposited with the map's one entry `cleanKey ↦ (N, h, J)`. -/
theorem walCreating_mintC (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walUnlockedTokX (W := W) ==∗
      ⌜CR = ∅⌝ ∗
      walCreatingAuth (W := W) (<[cleanKey := (N, h, J)]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) ∗
      walCleanPin (W := W) N h J := by
  unfold walCreatingAuth
  iintro ⟨Ha, Hor⟩ Hu
  icases Hor with (%hCR | ⟨-, Hl⟩ | ⟨-, Hl⟩)
  · subst hCR
    unfold walCleanPin
    letI := walAllG (W := W)
    imod ghost_map_insert (γ := W.γcr) cleanKey (N, h, J) (by rfl) $$ Ha with ⟨Ha, Ht⟩
    imodintro
    iframe Ht
    isplitr
    · ipureintro; rfl
    iframe Ha
    iright; iright
    iframe Hu
    ipureintro; exact ⟨(N, h, J), rfl⟩
  · iexfalso
    iapply walUnlockedTok_exclX $$ Hl Hu
  · iexfalso
    iapply walUnlockedTokX_exclX $$ Hl Hu

/-- **Deleting the cleanup's pin**: the map's one entry, so the map is empty again; the deposited
token back. -/
theorem walCreating_deleteC (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))
    (N : Fs.NameSet) (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCleanPin (W := W) N h J ==∗
      ⌜GMap.delete cleanKey CR = ∅⌝ ∗ walCreatingAuth (W := W) (GMap.delete cleanKey CR) ∗
        walUnlockedTokX (W := W) := by
  unfold walCreatingAuth walCleanPin
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ Ht
  icases ghost_map_lookup $$ Ha Ht with %Hl
  have key : ∀ d (x : Fs.NameSet × Fs.NamesH × Fs.Ino),
      (<[d := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) !! cleanKey = some (N, h, J) →
      d = cleanKey ∧ GMap.delete cleanKey (<[d := x]> (∅ : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino))) = ∅ := by
    intro d x hl
    have hd : d = cleanKey := by
      by_cases hne : d = cleanKey
      · exact hne
      · rw [GMap.lookup_insert_ne _ _ hne] at hl
        simp at hl
    subst hd
    exact ⟨rfl, GMap.delete_insert _ _ _ (by rfl)⟩
  icases Hor with (%hCR | ⟨%hs, Hk⟩ | ⟨%hs, Hk⟩)
  · subst hCR; simp at Hl
  · obtain ⟨d, x, rfl⟩ := hs
    obtain ⟨-, he⟩ := key d x Hl
    imod ghost_map_delete $$ Ha Ht with Ha
    imodintro
    rw [he]
    iframe Ha
    isplitr
    · ipureintro; rfl
    isplitr
    · ileft; ipureintro; rfl
    iapply walUnlockedTok_toX $$ Hk
  · obtain ⟨x, rfl⟩ := hs
    obtain ⟨-, he⟩ := key cleanKey x Hl
    imod ghost_map_delete $$ Ha Ht with Ha
    imodintro
    rw [he]
    iframe Ha Hk
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl

/-- The cleanup's pin's entry in the authority. -/
theorem walCleanPin_lookup (CR : GMap GoString (Fs.NameSet × Fs.NamesH × Fs.Ino)) (N : Fs.NameSet)
    (h : Fs.NamesH) (J : Fs.Ino) :
    ⊢@{IProp GF} walCreatingAuth (W := W) CR -∗ walCleanPin (W := W) N h J -∗
      ⌜CR !! cleanKey = some (N, h, J)⌝ ∗ walCreatingAuth (W := W) CR ∗ walCleanPin (W := W) N h J := by
  unfold walCreatingAuth walCleanPin
  letI := walAllG (W := W)
  iintro ⟨Ha, Hor⟩ Ht
  icases ghost_map_lookup $$ Ha Ht with %H
  iframe Ha Ht Hor
  ipureintro; exact H

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
  iintro ⟨Ha, -⟩ ⟨Hk, -⟩
  iapply ghost_map_lookup $$ Ha Hk

/-- **A directory key's names left out are the pipeline's** (unit `locks`, session 10). -/
theorem walDirKey_tmps (dir : GoString) (j : Fs.Ino) (X : List GoString) :
    walDirKey (W := W) dir j X ⊢ ⌜X = walTmps⌝ := by
  unfold walDirKey
  iintro ⟨-, %h⟩
  ipureintro; exact h

/-- **A new directory key** (`Create`'s commit, `ReadAll`), the directory without one. -/
theorem walDirKey_insert (K : GMap GoString (Fs.Ino × List GoString)) (dir : GoString) (j : Fs.Ino)
    (X : List GoString) (hK : K !! dir = none) (hX : X = walTmps) :
    ⊢@{IProp GF} walDirKeysAuth (W := W) K ==∗
      walDirKeysAuth (W := W) (<[dir := (j, X)]> K) ∗ walDirKey (W := W) dir j X := by
  unfold walDirKeysAuth walDirKey
  letI := walAllG (W := W)
  iintro ⟨Ha, Hm⟩
  imod ghost_map_insert_persist dir (j, X) hK $$ Ha with ⟨Ha, #Hk⟩
  imodintro
  isplitl [Ha Hm]
  · iframe Ha
    iapply (BigSepM.bigSepM_insert (Φ := fun (k : GoString) (x : Fs.Ino × List GoString) =>
      iprop(k ↪[W.γdk]□ x)) hK).2
    iframe Hk Hm
  · iframe Hk; ipureintro; exact hX

/-- **A key of the generation, found in the authority** (its copy). -/
theorem walDirKeysAuth_get (K : GMap GoString (Fs.Ino × List GoString)) (dir : GoString) (j : Fs.Ino)
    (X : List GoString) (hK : K !! dir = some (j, X)) (hX : X = walTmps) :
    ⊢@{IProp GF} walDirKeysAuth (W := W) K -∗ walDirKeysAuth (W := W) K ∗ walDirKey (W := W) dir j X := by
  unfold walDirKeysAuth walDirKey
  letI := walAllG (W := W)
  iintro ⟨Ha, #Hm⟩
  iframe Ha Hm
  isplitl []
  · iapply (BigSepM.bigSepM_lookup (Φ := fun (k : GoString) (x : Fs.Ino × List GoString) =>
      iprop(k ↪[W.γdk]□ x)) hK) $$ Hm
  · ipureintro; exact hX

theorem walIncFact.mono {I : GMap GoString Nat} {dir : GoString} {i : Nat} {P Q : Prop}
    (h : walIncFact I dir i P) (hPQ : P → Q) : walIncFact I dir i Q :=
  h.imp (fun h => ⟨h.1, hPQ h.2⟩) id

/-- **A fact of the current incarnation holds**: read at a past state `p` below `(s, I)`, where `dir`'s
incarnation is `i`. -/
theorem walIncFact.cur {p : AbsDiskState × GMap GoString Nat} {s : AbsDiskState}
    {I : GMap GoString Nat} {dir : GoString} {P : Prop}
    (h : walIncFact p.2 dir (incOf I dir) P) (hle : walLeI p (s, I)) :
    incOf p.2 dir = incOf I dir ∧ P := by
  rcases h with h | h
  · exact h
  · exact absurd (hle.2.2.1 dir) (Nat.not_le.2 h)

/-- **A retired incarnation's fact**: any fact of an incarnation below the current one. -/
theorem walIncFact.retired {I : GMap GoString Nat} {dir : GoString} {i : Nat} (P : Prop)
    (h : i < incOf I dir) : walIncFact I dir i P := Or.inr h

theorem walSyncedLb_mono (dir : GoString) (i n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walSyncedLb (W := W) dir i n -∗ walSyncedLb (W := W) dir i n' := by
  unfold walSyncedLb
  iintro ⟨%s, %I, Hs, %Hd⟩
  iexists s, I; iframe Hs; ipureintro
  exact Hd.mono fun ⟨d, hd, hn⟩ => ⟨d, hd, Nat.le_trans h hn⟩

theorem walLenLb_mono (w : Loc) (dir : GoString) (i n n' : Nat) (h : n' ≤ n) :
    ⊢@{IProp GF} walLenLb (W := W) w dir i n -∗ walLenLb (W := W) w dir i n' := by
  unfold walLenLb
  iintro ⟨%γ, %s, %I, Hw, Hs, %Hd⟩
  iexists γ, s, I; iframe Hw Hs; ipureintro
  exact Hd.mono fun ⟨d, hd, hn⟩ => ⟨d, hd, Nat.le_trans h hn⟩

/-- **A synced lower bound from a past state**, of the incarnation there. -/
theorem walSyncedLb_intro (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) (d : WalDur)
    (n : Nat) (hd : s.wal !! dir = some d) (hn : n ≤ d.m) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walSyncedLb (W := W) dir (incOf I dir) n := by
  unfold walSyncedLb
  iintro #Hs
  iexists s, I; iframe Hs; ipureintro; exact Or.inl ⟨rfl, d, hd, hn⟩

/-- **Named, from a past state**, of the incarnation there. -/
theorem walNamed_intro (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) (d : WalDur)
    (hd : s.wal !! dir = some d) (hn : d.named = true) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walNamed (W := W) dir (incOf I dir) := by
  unfold walNamed
  iintro #Hs
  iexists s, I; iframe Hs; ipureintro; exact Or.inl ⟨rfl, d, hd, hn⟩

/-- **Every fact of a retired incarnation** `i` (below the past state's). -/
theorem walSyncedLb_retired (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) (i n : Nat)
    (h : i < incOf I dir) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walSyncedLb (W := W) dir i n := by
  unfold walSyncedLb
  iintro #Hs
  iexists s, I; iframe Hs; ipureintro; exact Or.inr h

theorem walNamed_retired (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) (i : Nat)
    (h : i < incOf I dir) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walNamed (W := W) dir i := by
  unfold walNamed
  iintro #Hs
  iexists s, I; iframe Hs; ipureintro; exact Or.inr h

/-- **A fact at an earlier past's incarnation**, from a later past: the incarnation of `dir` at
`(s0, I0)` is the current one at `(s, I)` (the fact holds) or retired. -/
theorem walNamed_of_le (s s0 : AbsDiskState) (I I0 : GMap GoString Nat) (dir : GoString) (d : WalDur)
    (hle : walLeI (s0, I0) (s, I)) (hd : s.wal !! dir = some d) (hn : d.named = true) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walNamed (W := W) dir (incOf I0 dir) := by
  iintro #Hs
  have h := hle.2.2.1 dir
  simp only at h
  rcases Nat.lt_or_eq_of_le h with h | h
  · iapply walNamed_retired s I dir _ h $$ Hs
  · rw [h]; iapply walNamed_intro s I dir d hd hn $$ Hs

theorem walSyncedLb_of_le (s s0 : AbsDiskState) (I I0 : GMap GoString Nat) (dir : GoString)
    (d : WalDur) (n : Nat) (hle : walLeI (s0, I0) (s, I)) (hd : s.wal !! dir = some d)
    (hn : n ≤ d.m) :
    ⊢@{IProp GF} walPastI (W := W) (s, I) -∗ walSyncedLb (W := W) dir (incOf I0 dir) n := by
  iintro #Hs
  have h := hle.2.2.1 dir
  simp only at h
  rcases Nat.lt_or_eq_of_le h with h | h
  · iapply walSyncedLb_retired s I dir _ n h $$ Hs
  · rw [h]; iapply walSyncedLb_intro s I dir d n hd hn $$ Hs

/-- A past state with its incarnations, as a past state. -/
theorem walPastI_past (p : AbsDiskState × GMap GoString Nat) :
    walPastI (W := W) p ⊢ walPast (W := W) p.1 := by
  unfold walPast
  iintro #H; iexists p.2; iexact H

theorem walHandleDirI_agree (w w' : Loc) (dir dir' : GoString) (i i' : Nat) (γ : GName) :
    ⊢@{IProp GF} walHandleDirI (W := W) w dir i γ -∗ walHandleDirI (W := W) w' dir' i' γ -∗
      ⌜w = w' ∧ dir = dir' ∧ i = i'⌝ := by
  unfold walHandleDirI
  letI := walAllG (W := W)
  iintro #H1 #H2
  icases ghostMapElem_agree $$ H1 H2 with %H
  ipureintro
  simp only [Prod.mk.injEq] at H
  exact H

theorem walHandleDir_agree (w w' : Loc) (dir dir' : GoString) (γ : GName) :
    ⊢@{IProp GF} walHandleDir (W := W) w dir γ -∗ walHandleDir (W := W) w' dir' γ -∗
      ⌜w = w' ∧ dir = dir'⌝ := by
  unfold walHandleDir
  iintro ⟨%i, #H1⟩ ⟨%i', #H2⟩
  icases walHandleDirI_agree $$ H1 H2 with %H
  ipureintro; exact ⟨H.1, H.2.1⟩

/-- The open handle at its incarnation. -/
theorem walOpenW_inc (w : Loc) (dir : GoString) :
    walOpenW (W := W) w dir ⊣⊢ ∃ i, walOpenWI (W := W) w dir i := by
  unfold walOpenW; exact .rfl

theorem walOpenWI_openW (w : Loc) (dir : GoString) (i : Nat) :
    walOpenWI (W := W) w dir i ⊢ walOpenW (W := W) w dir := by
  unfold walOpenW; iintro H; iexists i; iexact H

/-- **An open handle's incarnation is current** against a share `I`. -/
theorem walOpenWI_cur (w : Loc) (dir : GoString) (i : Nat) (q : Qp) (I : GMap GoString Nat) :
    ⊢@{IProp GF} walOpenWI (W := W) w dir i -∗ (letI := walAllG (W := W); ghostVar W.γI q I) -∗
      ⌜incOf I dir = i⌝ ∗ walOpenWI (W := W) w dir i ∗ (letI := walAllG (W := W); ghostVar W.γI q I) := by
  unfold walOpenWI walLockedTokI walIncQ
  letI := walAllG (W := W)
  iintro ⟨%I', Hs, ⟨Ht, Hf, Hc, Hi⟩, %h⟩ HI
  icases ghostVar_agree $$ Hi HI with %e
  subst e
  iframe HI
  isplitr
  · ipureintro; exact h
  iexists I'; iframe Hs Ht Hf Hc Hi; ipureintro; exact h

theorem walOpenW_lenLb (w : Loc) (dir : GoString) (s : AbsDiskState) (I : GMap GoString Nat)
    (d : WalDur) (n : Nat) (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpenW (W := W) w dir -∗ walPastI (W := W) (s, I) -∗
      walOpenW (W := W) w dir ∗ walLenLb (W := W) w dir (incOf I dir) n := by
  unfold walOpenW walOpenWI walHandleStI walLenLb walHandleDir
  iintro ⟨%i, %I', ⟨%γ, #Hw, Hm⟩, Hu⟩ #Hs
  isplitl [Hm Hu]
  · iexists i, I'; iframe Hu; iexists γ; iframe Hw Hm
  · iexists γ, s, I; iframe Hs
    isplitl
    · iexists i; iexact Hw
    ipureintro; exact Or.inl ⟨rfl, d, hd, hn⟩

/-- A handle's length bound of a retired incarnation. -/
theorem walOpenW_lenLb_retired (w : Loc) (dir : GoString) (s : AbsDiskState) (I : GMap GoString Nat)
    (i n : Nat) (h : i < incOf I dir) :
    ⊢@{IProp GF} walOpenW (W := W) w dir -∗ walPastI (W := W) (s, I) -∗
      walOpenW (W := W) w dir ∗ walLenLb (W := W) w dir i n := by
  unfold walOpenW walOpenWI walHandleStI walLenLb walHandleDir
  iintro ⟨%i', %I', ⟨%γ, #Hw, Hm⟩, Hu⟩ #Hs
  isplitl [Hm Hu]
  · iexists i', I'; iframe Hu; iexists γ; iframe Hw Hm
  · iexists γ, s, I; iframe Hs
    isplitl
    · iexists i'; iexact Hw
    ipureintro; exact Or.inr h

/-- **`walOpenW` without its flags** (sealed): what a cut holds of the ghost handle while its rename
is pending (`walOpenW_cut`). -/
@[no_expose] def walOpenWCI (w : Loc) (dir : GoString) (i : Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ I : GMap GoString Nat, walHandleStI (W := W) w dir i .append ∗ token W.hA.γu ∗
    walIncQ (W := W) I ∗ ⌜incOf I dir = i⌝)

/-- `walOpenWCI` at some incarnation. Sealed. -/
@[no_expose] def walOpenWC (w : Loc) (dir : GoString) : IProp GF :=
  iprop(∃ i : Nat, walOpenWCI (W := W) w dir i)

/-- **The parking and pending-cut flags out of the ghost handle** (W2's `cut`: the parking flag
`false` tells the rename's update that the handle has taken its WAL's halves out of `walParked`;
`walCut_set` to `some dir` at the rename's commit, back to `none` at the directory's sync). -/
theorem walOpenW_cut (w : Loc) (dir : GoString) :
    walOpenW (W := W) w dir ⊣⊢
      walOpenWC (W := W) w dir ∗ walParkFrag (W := W) false ∗ walCutFrag (W := W) none := by
  unfold walOpenW walOpenWI walOpenWC walOpenWCI walLockedTokI
  constructor
  · iintro ⟨%i, %I, Hs, ⟨Ht, Hf, Hc, Hi⟩, %h⟩; iframe Hf Hc; iexists i, I; iframe Hs Ht Hi; ipureintro; exact h
  · iintro ⟨⟨%i, %I, Hs, Ht, Hi, %h⟩, Hf, Hc⟩; iexists i, I; iframe Hs Ht Hf Hc Hi; ipureintro; exact h

/-- `walOpenW_cut` at the handle's incarnation. -/
theorem walOpenWI_cut (w : Loc) (dir : GoString) (i : Nat) :
    walOpenWI (W := W) w dir i ⊣⊢
      walOpenWCI (W := W) w dir i ∗ walParkFrag (W := W) false ∗ walCutFrag (W := W) none := by
  unfold walOpenWI walOpenWCI walLockedTokI
  constructor
  · iintro ⟨%I, Hs, ⟨Ht, Hf, Hc, Hi⟩, %h⟩; iframe Hf Hc; iexists I; iframe Hs Ht Hi; ipureintro; exact h
  · iintro ⟨⟨%I, Hs, Ht, Hi, %h⟩, Hf, Hc⟩; iexists I; iframe Hs Ht Hf Hc Hi; ipureintro; exact h

/-- **A handle's written length** at its incarnation `i`, from a past state there. -/
theorem walOpenWI_lenLb (w : Loc) (dir : GoString) (i : Nat) (s : AbsDiskState) (I : GMap GoString Nat)
    (d : WalDur) (n : Nat) (hi : incOf I dir = i) (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpenWI (W := W) w dir i -∗ walPastI (W := W) (s, I) -∗
      walOpenWI (W := W) w dir i ∗ walLenLb (W := W) w dir i n := by
  unfold walOpenWI walHandleStI walLenLb walHandleDir
  iintro ⟨%I', ⟨%γ, #Hw, Hm⟩, Hu, %h⟩ #Hs
  isplitl [Hm Hu]
  · iexists I'; iframe Hu
    isplitl
    · iexists γ; iframe Hw Hm
    ipureintro; exact h
  · iexists γ, s, I; iframe Hs
    isplitl
    · iexists i; iexact Hw
    ipureintro; exact Or.inl ⟨hi, d, hd, hn⟩

theorem walOpening_lenLb (w : Loc) (dir : GoString) (sn : w64 × w64) (s : AbsDiskState)
    (I : GMap GoString Nat) (d : WalDur)
    (n : Nat) (hd : s.wal !! dir = some d) (hn : n ≤ d.H.length) :
    ⊢@{IProp GF} walOpening (W := W) w dir sn -∗ walPastI (W := W) (s, I) -∗
      walOpening (W := W) w dir sn ∗ walLenLb (W := W) w dir (incOf I dir) n := by
  unfold walOpening walHandleP walLenLb walHandleDir
  iintro ⟨%γ, %i, %I', #Hw, Hm, Hp, Hu, %hi⟩ #Hs
  isplitl [Hm Hp Hu]
  · iexists γ, i, I'; iframe Hw Hm Hp Hu; ipureintro; exact hi
  · iexists γ, s, I; iframe Hs
    isplitl
    · iexists i; iexact Hw
    ipureintro; exact Or.inl ⟨rfl, d, hd, hn⟩

theorem walArea_agree (r r' : GoString) :
    ⊢@{IProp GF} walArea (W := W) r -∗ walArea (W := W) r' -∗ ⌜r = r'⌝ := by
  unfold walArea walPast walPastI
  letI := walAllG (W := W)
  iintro ⟨%p, ⟨%I, -, #Hp⟩, %hp⟩ ⟨%q, ⟨%I', -, #Hq⟩, %hq⟩
  icases ghostMapElem_agree $$ Hp Hq with %H
  ipureintro; rw [← hp, ← hq]; exact H

theorem walPast_walArea (s : AbsDiskState) :
    ⊢@{IProp GF} walPast (W := W) s -∗ walArea (W := W) s.area := by
  unfold walArea
  iintro #Hs
  iexists s; iframe Hs; ipureintro; rfl

/-! ## The handles' locked ranges (unit `locks`, session 4) -/

/-- **Each handle's locked range starts at or before its WAL's `unl`**: the position `b` registered for
`dir` is at most the `unl` of `dir`'s WAL. -/
def LksOk (s : AbsDiskState) (Lk : GMap GoString Nat) : Prop :=
  ∀ dir b, Lk !! dir = some b → ∃ d, s.wal !! dir = some d ∧ b ≤ d.unl

/-- No WAL goes and no `unl` goes down: what `walGhost`'s updates take (`walLksAuth_mono`). -/
def UnlMono (s s' : AbsDiskState) : Prop :=
  ∀ dir d, s.wal !! dir = some d → ∃ d', s'.wal !! dir = some d' ∧ d.unl ≤ d'.unl

/-- `LksOk` at a state where no WAL went and no `unl` went down. -/
theorem LksOk.mono {s s' : AbsDiskState} {Lk : GMap GoString Nat} (h : LksOk s Lk)
    (hu : UnlMono s s') :
    LksOk s' Lk := by
  intro dir b hb
  obtain ⟨d, hd, hbd⟩ := h dir b hb
  obtain ⟨d', hd', hu'⟩ := hu dir d hd
  exact ⟨d', hd', Nat.le_trans hbd hu'⟩

theorem LksOk.empty (s : AbsDiskState) : LksOk s ∅ := by
  intro dir b hb; rw [GMap.lookup_empty] at hb; cases hb


theorem unlMono_upd (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur)
    (hf : ∀ d, d.unl ≤ (f d).unl) : UnlMono s (absDiskUpd s dir f) := by
  intro k d hd
  unfold absDiskUpd
  cases h : s.wal !! dir with
  | none => exact ⟨d, hd, Nat.le_refl _⟩
  | some d0 =>
    simp only
    by_cases e : k = dir
    · subst e; rw [hd] at h; cases h
      exact ⟨f d, by rw [GMap.lookup_insert], hf d⟩
    · exact ⟨d, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hd, Nat.le_refl _⟩

theorem unlMono_insert (s : AbsDiskState) (dir : GoString) (d' : WalDur)
    (h : ∀ d, s.wal !! dir = some d → d.unl ≤ d'.unl) :
    UnlMono s { s with wal := <[dir := d']> s.wal } := by
  intro k d hd
  by_cases e : k = dir
  · subst e; exact ⟨d', by simp only; rw [GMap.lookup_insert], h d hd⟩
  · exact ⟨d, by simp only; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hd, Nat.le_refl _⟩

/-- **The handles' locked ranges, the invariant's half** (in `walGhost`): the map `Lk` (`WalGS.γlk`),
with `LksOk`; the other half is the lock holder's (`walTailsFrag`'s second map). -/
def walLksAuth (s : AbsDiskState) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ Lk : GMap GoString Nat, ghostVar W.γlk (1 : Qp).half Lk ∗ ⌜LksOk s Lk⌝)

instance walLksAuth_timeless (s : AbsDiskState) : Timeless (walLksAuth (W := W) s) := by
  unfold walLksAuth; infer_instance

/-- `walLksAuth` at a state where no WAL went and no `unl` went down. -/
theorem walLksAuth_mono (s s' : AbsDiskState)
    (hu : UnlMono s s') :
    walLksAuth (W := W) s ⊢ walLksAuth (W := W) s' := by
  unfold walLksAuth
  iintro ⟨%Lk, Ha, %h⟩
  iexists Lk; iframe Ha; ipureintro; exact h.mono hu

/-- **The two halves of the locked ranges agree**, and the holder's ranges are within the `unl`s. -/
theorem walLks_agree (s : AbsDiskState) (T : GMap GoString GName) (Lk : GMap GoString Nat) :
    ⊢ walLksAuth (W := W) s -∗ walTailsFrag (W := W) T Lk -∗
      ⌜LksOk s Lk⌝ ∗ walLksAuth (W := W) s ∗ walTailsFrag (W := W) T Lk := by
  unfold walLksAuth walTailsFrag
  letI := walAllG (W := W)
  iintro ⟨%Lk', Ha, %h⟩ ⟨Ht, Hf⟩
  icases ghostVar_agree $$ Ha Hf with %e
  subst e
  isplitr
  · ipureintro; exact h
  isplitl [Ha]
  · iexists Lk'; iframe Ha; ipureintro; exact h
  · iframe Ht Hf

/-- **Setting the locked ranges** (both halves): to any `Lk'` within the `unl`s (a handle registering
its range, raising it, or dropping it). -/
theorem walLks_set (s : AbsDiskState) (T : GMap GoString GName) (Lk Lk' : GMap GoString Nat)
    (h : LksOk s Lk') :
    ⊢ walLksAuth (W := W) s -∗ walTailsFrag (W := W) T Lk ==∗
      walLksAuth (W := W) s ∗ walTailsFrag (W := W) T Lk' := by
  unfold walLksAuth walTailsFrag
  letI := walAllG (W := W)
  iintro ⟨%Lk0, Ha, -⟩ ⟨Ht, Hf⟩
  imod ghostVar_update_halves Lk' _ _ _ $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isplitl [Ha]
  · iexists Lk'; iframe Ha; ipureintro; exact h
  · iframe Ht Hf

end ghost


section ghostInv
variable {GF : BundledGFunctors} [W : WalGS GF] {hlc : HasLC} [GooseExts] [GooseInterp]
  [G : GooseGlobalGS hlc GF]

/-- **What the WAL invariant holds of the ghost state, the real WAL state being `s` and the
incarnations `I`**: the map's other half, below `s`'s (`walMapLe`), the past states' authority (with
their incarnations, below `(s, I)`) and half of the incarnations (the views hold the other,
`walIncQ`), the handles' authorities, every WAL key in the area, and the WALs' step bound
(`walStepsLb`). -/
def walGhostI (s : AbsDiskState) (I : GMap GoString Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop((∃ G : GMap GoString WalDur, ghostVar W.hA.γs (1 : Qp).half G ∗ ⌜walMapLe G s.wal⌝) ∗
    (walPastIAuth (W := W) (s, I) ∗ ghostVar W.γI (1 : Qp).half I) ∗
    (walHandleAuth (W := W) ∗ walLksAuth (W := W) s) ∗ ⌜walKeysInArea s⌝ ∗ walStepsLb s)

/-- **What the WAL invariant holds of the ghost state, the real WAL state being `s`** (at some
incarnations). -/
def walGhost (s : AbsDiskState) : IProp GF :=
  iprop(∃ I : GMap GoString Nat, walGhostI (W := W) s I)

instance walGhostI_timeless (s : AbsDiskState) (I : GMap GoString Nat) :
    Timeless (walGhostI (W := W) s I) := by
  letI := walAllG (W := W)
  unfold walGhostI walPastIAuth walLksAuth; infer_instance

instance walGhost_timeless (s : AbsDiskState) : Timeless (walGhost (W := W) s) := by
  unfold walGhost; infer_instance

theorem walGhostI_ghost (s : AbsDiskState) (I : GMap GoString Nat) :
    walGhostI (W := W) s I ⊢ walGhost (W := W) s := by
  unfold walGhost; iintro H; iexists I; iexact H

/-- **`walGhost` at the view's incarnations** (the halves agree). -/
theorem walGhost_inc (s : AbsDiskState) (I' : GMap GoString Nat) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walIncQ (W := W) I' -∗
      walGhostI (W := W) s I' ∗ walIncQ (W := W) I' := by
  unfold walGhost walGhostI walIncQ
  letI := walAllG (W := W)
  iintro ⟨%I, Hm, ⟨Hp, Hi⟩, Hr⟩ Hq
  icases ghostVar_agree $$ Hi Hq with %e
  subst e
  iframe Hm Hp Hi Hr Hq

/-- **The lock's incarnations are the ghost's.** -/
theorem walGhostI_lockedI_agree (s : AbsDiskState) (I I' : GMap GoString Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walLockedTokI (W := W) I' -∗
      walGhostI (W := W) s I ∗ walLockedTokI (W := W) I' ∗ ⌜I' = I⌝ := by
  unfold walGhostI walLockedTokI walIncQ
  letI := walAllG (W := W)
  iintro ⟨Hm, ⟨Hp, Hi⟩, Hr⟩ ⟨Ht, Hf, Hc, Hq⟩
  icases ghostVar_agree $$ Hi Hq with %e
  subst e
  iframe Hm Hp Hi Hr Ht Hf Hc Hq
  ipureintro; rfl

/-- **`walGhost` at a view's incarnation**: the view's `i` is the ghost's. -/
theorem walGhost_dirIsI (s : AbsDiskState) (dir : GoString) (i : Nat) (o : Option WalDur) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walDirIsI (W := W) dir i o -∗
      ∃ I, ⌜incOf I dir = i⌝ ∗ walGhostI (W := W) s I ∗ walDirIsI (W := W) dir i o := by
  unfold walDirIsI
  iintro Hg ⟨%M, %I, HM, HI, %h, %hi⟩
  icases walGhost_inc s I $$ Hg HI with ⟨Hg, HI⟩
  iexists I; iframe Hg
  isplitr
  · ipureintro; exact hi
  iexists M, I; iframe HM HI; ipureintro; exact ⟨h, hi⟩

/-- **An open handle's incarnation is the ghost's.** -/
theorem walGhostI_openWI (s : AbsDiskState) (I : GMap GoString Nat) (w : Loc) (dir : GoString) (i : Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walOpenWI (W := W) w dir i -∗
      ⌜incOf I dir = i⌝ ∗ walGhostI (W := W) s I ∗ walOpenWI (W := W) w dir i := by
  unfold walGhostI
  iintro ⟨Hm, ⟨Hp, Hi⟩, Hr⟩ Hw
  icases walOpenWI_cur w dir i _ I $$ Hw Hi with ⟨%h, Hw, Hi⟩
  iframe Hm Hp Hi Hr Hw
  ipureintro; exact h

/-- What the program's WAL map says of the invariant's: it is below the real one. -/
theorem walOwn_agree (s : AbsDiskState) (M : GMap GoString WalDur) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walOwn (W := W) M -∗ ⌜walMapLe M s.wal⌝ := by
  unfold walGhost walGhostI walOwn walOwnAt
  letI := walAllG (W := W)
  iintro ⟨%I, ⟨%G, Hs, %HG⟩, -⟩ ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  ipureintro; subst HMG; exact HG

/-- `walOwn_agree` at `walGhostI`. -/
theorem walGhostI_own_agree (s : AbsDiskState) (I : GMap GoString Nat) (M : GMap GoString WalDur) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walOwn (W := W) M -∗ ⌜walMapLe M s.wal⌝ := by
  unfold walGhostI walOwn walOwnAt
  letI := walAllG (W := W)
  iintro ⟨⟨%G, Hs, %HG⟩, -⟩ ⟨HM, -⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  ipureintro; subst HMG; exact HG

/-- What a past state (with its incarnations) says of the present one. -/
theorem walPastI_ghost_le (s : AbsDiskState) (I : GMap GoString Nat) (p : AbsDiskState × GMap GoString Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walPastI (W := W) p -∗ ⌜walLeI p (s, I)⌝ := by
  unfold walGhostI
  iintro ⟨-, ⟨HP, -⟩, -⟩ Hp
  iapply walPastI_le $$ HP Hp

/-- What a past state says of the present one: the area and the durable directories. -/
theorem walPast_ghost_le (s p : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walPast (W := W) p -∗
      ⌜s.area = p.area ∧ ∀ d, p.dirs !! d = some () → s.dirs !! d = some ()⌝ := by
  unfold walGhost walPast
  iintro ⟨%I, Hg⟩ ⟨%I', Hp⟩
  icases walPastI_ghost_le s I (p, I') $$ Hg Hp with %h
  ipureintro; exact ⟨h.1, h.2.1⟩

/-- **A synced lower bound of the current incarnation holds of the present WAL.** -/
theorem walSyncedLb_ghost (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) (n : Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walSyncedLb (W := W) dir (incOf I dir) n -∗
      ⌜∃ d, s.wal !! dir = some d ∧ n ≤ d.m⌝ := by
  unfold walSyncedLb
  iintro Hg ⟨%p, %I0, Hp, %hp⟩
  icases walPastI_ghost_le s I (p, I0) $$ Hg Hp with %h
  ipureintro
  obtain ⟨he, d0, hd0, hn⟩ := hp.cur h
  obtain ⟨d, hd, hm, -, -⟩ := h.2.2.2 dir d0 hd0 he.symm
  exact ⟨d, hd, Nat.le_trans hn hm⟩

/-- **Named, of the current incarnation, holds of the present WAL.** -/
theorem walNamed_ghost (s : AbsDiskState) (I : GMap GoString Nat) (dir : GoString) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walNamed (W := W) dir (incOf I dir) -∗
      ⌜∃ d, s.wal !! dir = some d ∧ d.named = true⌝ := by
  unfold walNamed
  iintro Hg ⟨%p, %I0, Hp, %hp⟩
  icases walPastI_ghost_le s I (p, I0) $$ Hg Hp with %h
  ipureintro
  obtain ⟨he, d0, hd0, hn⟩ := hp.cur h
  obtain ⟨d, hd, -, -, hn'⟩ := h.2.2.2 dir d0 hd0 he.symm
  exact ⟨d, hd, hn' hn⟩

/-- **A written length of the current incarnation holds of the present WAL.** -/
theorem walLenLb_ghost (s : AbsDiskState) (I : GMap GoString Nat) (w : Loc) (dir : GoString) (n : Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walLenLb (W := W) w dir (incOf I dir) n -∗
      ⌜∃ d, s.wal !! dir = some d ∧ n ≤ d.H.length⌝ := by
  unfold walLenLb
  iintro Hg ⟨%γ, %p, %I0, -, Hp, %hp⟩
  icases walPastI_ghost_le s I (p, I0) $$ Hg Hp with %h
  ipureintro
  obtain ⟨he, d0, hd0, hn⟩ := hp.cur h
  obtain ⟨d, hd, -, hl, -⟩ := h.2.2.2 dir d0 hd0 he.symm
  exact ⟨d, hd, Nat.le_trans hn hl⟩

/-- **A written length's incarnation is not above the current one**: it is the current one or
retired. -/
theorem walLenLb_ghost_le (s : AbsDiskState) (I : GMap GoString Nat) (w : Loc) (dir : GoString)
    (i n : Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walLenLb (W := W) w dir i n -∗ ⌜i ≤ incOf I dir⌝ := by
  unfold walLenLb
  iintro Hg ⟨%γ, %p, %I0, -, Hp, %hp⟩
  icases walPastI_ghost_le s I (p, I0) $$ Hg Hp with %h
  ipureintro
  have := h.2.2.1 dir
  simp only at this
  rcases hp with ⟨he, -⟩ | hlt
  · omega
  · omega

theorem walArea_ghost (s : AbsDiskState) (r : GoString) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walArea (W := W) r -∗ ⌜s.area = r⌝ := by
  unfold walArea
  iintro Hc ⟨%p, Hp, %hp⟩
  icases walPast_ghost_le $$ Hc Hp with %Hle
  ipureintro; rw [Hle.1, hp]

/-- **Setting the locked ranges, from `walGhost`** (`walLks_set` with the invariant's half out of
`walGhost`). -/
theorem walGhost_lksSet (s : AbsDiskState) (T : GMap GoString GName) (Lk Lk' : GMap GoString Nat)
    (h : LksOk s Lk') :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walTailsFrag (W := W) T Lk ==∗
      walGhost (W := W) s ∗ walTailsFrag (W := W) T Lk' := by
  unfold walGhost walGhostI
  iintro ⟨%I, Hm, Hp, ⟨Hh, Hl⟩, Hk, Hs⟩ Hf
  imod walLks_set s T Lk Lk' h $$ Hl Hf with ⟨Hl, Hf⟩
  imodintro
  iframe Hf
  iexists I
  iframe Hm Hp Hh Hl Hk Hs

/-- **The locked ranges agree, from `walGhost`.** -/
theorem walGhost_lksAgree (s : AbsDiskState) (T : GMap GoString GName) (Lk : GMap GoString Nat) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walTailsFrag (W := W) T Lk -∗
      ⌜LksOk s Lk⌝ ∗ walGhost (W := W) s ∗ walTailsFrag (W := W) T Lk := by
  unfold walGhost walGhostI
  iintro ⟨%I, Hm, Hp, ⟨Hh, Hl⟩, Hk, Hs⟩ Hf
  icases walLks_agree s T Lk $$ Hl Hf with ⟨%h, Hl, Hf⟩
  iframe Hf
  isplitr
  · ipureintro; exact h
  iexists I
  iframe Hm Hp Hh Hl Hk Hs

/-- One registered range, at most its WAL's `unl`. -/
theorem LksOk.single {s : AbsDiskState} {dir : GoString} {d : WalDur} {b : Nat}
    (hd : s.wal !! dir = some d) (hb : b ≤ d.unl) : LksOk s (<[dir := b]> (∅ : GMap GoString Nat)) := by
  intro dir' b' h
  by_cases e : dir' = dir
  · subst e; rw [GMap.lookup_insert_eq] at h; cases h; exact ⟨d, hd, hb⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), GMap.lookup_empty] at h; cases h

theorem walGhost_keys (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ ⌜walKeysInArea s⌝ := by
  unfold walGhost walGhostI
  iintro ⟨%I, -, -, -, %hk, -⟩
  ipureintro; exact hk

/-- **One purge right per handle.** -/
theorem walGhost_keys_keep (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walGhost (W := W) s ∗ ⌜walKeysInArea s⌝ := by
  unfold walGhost walGhostI
  iintro ⟨%I, Hs, HP, Hh, %hk, #Hst⟩
  isplitl
  · iexists I; iframe Hs HP Hh Hst; ipureintro; exact hk
  · ipureintro; exact hk

/-- **The WALs' step bound, read off the ghost state** (persistent). -/
theorem walGhost_steps (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walGhost (W := W) s ∗ walStepsLb s := by
  unfold walGhost walGhostI
  iintro ⟨%I, Hs, HP, Hh, %hk, #Hst⟩
  isplitl
  · iexists I; iframe Hs HP Hh Hst
    ipureintro; exact hk
  · iexact Hst

theorem walPurgeW_excl (γ : GName) :
    ⊢@{IProp GF} (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗
      (letI := walAllG (W := W); γ ↪[W.γhp] ()) -∗ False := by
  letI := walAllG (W := W)
  iintro H1 H2
  icases ghostMapElem_valid_2 γ _ (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2 with %Hv
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- **The ghost state at a bigger real state, the incarnations `I` kept, a counted step's receipt
`⧖ n'` deposited** (an append's commit: the WAL's history one longer, within `n'`): the map set to the
new state's, the past states kept, and the new state's fact with its incarnations. -/
theorem walGhostI_updR (s s' : AbsDiskState) (I : GMap GoString Nat) (M : GMap GoString WalDur)
    (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (n' : Nat)
    (hst : ∀ n, WalsStepped s n → WalsStepped s' (max n n'))
    (hu : UnlMono s s') :
    ⊢@{IProp GF} ⧖ n' -∗ walGhostI (W := W) s I -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhostI (W := W) s' I ∗ walOwn (W := W) s'.wal ∗
        walPastI (W := W) (s', I) := by
  iintro #Hn' Hc HM
  unfold walGhostI walOwn walOwnAt
  letI := walAllG (W := W)
  icases Hc with ⟨⟨%G, Hs, %HG⟩, ⟨HP, HI⟩, ⟨Hh, Hlk⟩, %Hk, #Hst⟩
  icases HM with ⟨HM, Ht⟩
  icases ghostVar_agree $$ HM Hs with %HMG
  subst HMG
  imod ghostVar_update_halves s'.wal _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  ihave HP := walPastI_grow _ (s', I) (walLeI_of_absLe I hle) $$ HP
  imod walPastI_snap (s', I) $$ HP with ⟨HP, Hp⟩
  ihave Hlk := walLksAuth_mono s s' hu $$ Hlk
  imodintro
  iframe HM Ht HP HI Hh Hlk Hp Hs
  isplitr
  · ipureintro; exact HG
  isplitr
  · ipureintro; exact walMapLe_refl _
  isplitr
  · ipureintro; exact hk Hk
  iapply walStepsLb_upd s s' n' hst $$ Hn' Hst

/-- **The ghost state at a bigger real state, a counted step's receipt `⧖ n'` deposited**
(`walGhostI_updR` at the ghost's incarnations). -/
theorem walGhost_updR (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (n' : Nat)
    (hst : ∀ n, WalsStepped s n → WalsStepped s' (max n n'))
    (hu : UnlMono s s') :
    ⊢@{IProp GF} ⧖ n' -∗ walGhost (W := W) s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhost (W := W) s' ∗ walOwn (W := W) s'.wal ∗ walPast (W := W) s' := by
  iintro #Hn' Hc HM
  unfold walGhost walPast
  icases Hc with ⟨%I, Hc⟩
  imod walGhostI_updR s s' I M hle hk n' hst hu $$ Hn' Hc HM with ⟨%h, Hc, HM, #Hp⟩
  imodintro
  iframe HM
  isplitr
  · ipureintro; exact h
  isplitl [Hc]
  · iexists I; iexact Hc
  · iexists I; iexact Hp

/-- **The ghost state at a bigger real state, the incarnations kept** (a step's update, no WAL's
history longer than the bound). -/
theorem walGhostI_upd (s s' : AbsDiskState) (I : GMap GoString Nat) (M : GMap GoString WalDur)
    (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (hst : ∀ n, WalsStepped s n → WalsStepped s' n)
    (hu : UnlMono s s') :
    ⊢@{IProp GF} walGhostI (W := W) s I -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhostI (W := W) s' I ∗ walOwn (W := W) s'.wal ∗
        walPastI (W := W) (s', I) := by
  iintro Hc HM
  imod preceipt_zero (GF := GF) with #H0
  iapply walGhostI_updR s s' I M hle hk 0 (fun n hn => by rw [Nat.max_zero]; exact hst n hn) hu
    $$ H0 Hc HM

/-- **The ghost state at a bigger real state** (a step's update, no WAL's history longer than the
bound): the map set to the new state's, the past states kept, and the new state's fact. -/
theorem walGhost_upd (s s' : AbsDiskState) (M : GMap GoString WalDur) (hle : absLe s s')
    (hk : walKeysInArea s → walKeysInArea s') (hst : ∀ n, WalsStepped s n → WalsStepped s' n)
    (hu : UnlMono s s') :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walGhost (W := W) s' ∗ walOwn (W := W) s'.wal ∗ walPast (W := W) s' := by
  iintro Hc HM
  imod preceipt_zero (GF := GF) with #H0
  iapply walGhost_updR s s' M hle hk 0 (fun n hn => by rw [Nat.max_zero]; exact hst n hn) hu $$ H0 Hc HM

/-- **The ghost state at a bigger real state, the program's map and the incarnations unchanged.** -/
theorem walGhostI_upd_lag (s s' : AbsDiskState) (I : GMap GoString Nat)
    (hlag : ∀ G, walMapLe G s.wal → walMapLe G s'.wal)
    (hle : absLe s s') (hk : walKeysInArea s → walKeysInArea s')
    (hst : ∀ n, WalsStepped s n → WalsStepped s' n)
    (hu : UnlMono s s') :
    ⊢@{IProp GF} walGhostI (W := W) s I ==∗ walGhostI (W := W) s' I ∗ walPastI (W := W) (s', I) := by
  iintro Hc
  unfold walGhostI
  icases Hc with ⟨⟨%G, Hs, %HG⟩, ⟨HP, HI⟩, ⟨Hh, Hlk⟩, %Hk, #Hst⟩
  ihave HP := walPastI_grow _ (s', I) (walLeI_of_absLe I hle) $$ HP
  imod walPastI_snap (s', I) $$ HP with ⟨HP, Hp⟩
  ihave Hlk := walLksAuth_mono s s' hu $$ Hlk
  imodintro
  iframe HP HI Hh Hlk Hp
  isplitl [Hs]
  · iexists G; iframe Hs; ipureintro; exact hlag G HG
  isplitr
  · ipureintro; exact hk Hk
  iapply walStepsLb_mono s s' hst $$ Hst

/-- **The ghost state at a bigger real state, the program's map unchanged.** -/
theorem walGhost_upd_lag (s s' : AbsDiskState) (hlag : ∀ G, walMapLe G s.wal → walMapLe G s'.wal)
    (hle : absLe s s') (hk : walKeysInArea s → walKeysInArea s')
    (hst : ∀ n, WalsStepped s n → WalsStepped s' n)
    (hu : UnlMono s s') :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s' ∗ walPast (W := W) s' := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨%I, Hc⟩
  imod walGhostI_upd_lag s s' I hlag hle hk hst hu $$ Hc with ⟨Hc, #Hp⟩
  imodintro
  isplitl [Hc]
  · iexists I; iexact Hc
  · iexists I; iexact Hp

/-- A past state's fact (with the incarnations), from the authority. -/
theorem walGhostI_past (s : AbsDiskState) (I : GMap GoString Nat) :
    ⊢@{IProp GF} walGhostI (W := W) s I ==∗ walGhostI (W := W) s I ∗ walPastI (W := W) (s, I) := by
  iintro Hc
  unfold walGhostI
  icases Hc with ⟨Hs, ⟨HP, HI⟩, Hh, Hk⟩
  imod walPastI_snap (s, I) $$ HP with ⟨HP, Hp⟩
  imodintro
  iframe Hs HP HI Hh Hk Hp

/-- A past state's fact, from the authority. -/
theorem walGhost_past (s : AbsDiskState) :
    ⊢@{IProp GF} walGhost (W := W) s ==∗ walGhost (W := W) s ∗ walPast (W := W) s := by
  iintro Hc
  unfold walGhost walPast
  icases Hc with ⟨%I, Hc⟩
  imod walGhostI_past s I $$ Hc with ⟨Hc, #Hp⟩
  imodintro
  isplitl [Hc]
  · iexists I; iexact Hc
  · iexists I; iexact Hp

end ghostInv

/-! ## A generation's start -/

section init
variable {GF : BundledGFunctors} {hlc : HasLC} [GooseExts] [GooseInterp] [G : GooseGlobalGS hlc GF]

/-- **A new generation's ghost state** at the real state `s` (every WAL key in the area): the
invariant's part, the program's map at `s.wal`, `s`'s fact, the lock token and the crash token; the
WALs' step bound carried over (`walStepsLb`: a crash keeps a prefix of each history). -/
theorem walGhost_init (hPre : AbsDiskGpreS GF) (R : List (GoString × Fs.Ino)) (s : AbsDiskState) (hk : walKeysInArea s) :
    ⊢@{IProp GF} walStepsLb s -∗ |==> ∃ W : WalGS GF, ⌜W.roots = R⌝ ∗ walGhost (W := W) s ∗ walOwn (W := W) s.wal ∗
      walIncQ (W := W) ∅ ∗ walPastI (W := W) (s, ∅) ∗ walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗
      walCreatingAuth (W := W) ∅ ∗ walTailsAuth (W := W) ∅ ∗ walParkAuth (W := W) true ∗
      walDirKeysAuth (W := W) ∅ ∗ walCutAuth (W := W) none ∗ walOutAuth (W := W) WalOut.empty ∗
      walNamesAuth (W := W) none ∗ walSplitAuth (W := W) [] ∗ walSplitFrag (W := W) [] ∗
      walLentAuth (W := W) ∅ := by
  iintro #Hstp
  imod absDisk_local_init hPre s hk with ⟨%hA, Hctx, Hst⟩
  letI := hA.absDiskAllG
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := WalMode)) with ⟨%γh, Hh⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GName) (V := Loc × GoString × Nat)) with ⟨%γhd, Hhd⟩
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
  imod (ghostVar_alloc (GF := GF) (∅ : GMap GoString Nat)) with ⟨%γlk, Hlk⟩
  imod (ghostVar_alloc (GF := GF) (∅ : GMap GoString Nat)) with ⟨%γI, HI⟩
  icases (ghostVar_split_half (GF := GF) γI 1 (∅ : GMap GoString Nat)).1 $$ HI with ⟨HI1, HI2⟩
  icases (ghostVar_split_half (GF := GF) γI (1 : Qp).half (∅ : GMap GoString Nat)).1 $$ HI2 with ⟨HI2, HI3⟩
  have hsing : (GMap.singleton ((s, ∅) : AbsDiskState × GMap GoString Nat) () :
      GMap (AbsDiskState × GMap GoString Nat) Unit) = (∅ : GMap _ _).insert (s, ∅) () := rfl
  imod (ghost_map_alloc (GF := GF) (GMap.singleton ((s, ∅) : AbsDiskState × GMap GoString Nat) ()))
    with ⟨%γpi, HF, HFe⟩
  rw [hsing]
  icases (BigSepM.bigSepM_insert (PROP := IProp GF) (m := (∅ : GMap (AbsDiskState × GMap GoString Nat) Unit))
    (Φ := fun p v => iprop(p ↪[γpi] v)) rfl).1 $$ HFe with ⟨Hse, -⟩
  imod ghostMapElem_persist $$ Hse with #Hse
  iexists ⟨hA, γh, γhd, γhp, γc, γcr, γt, γpk, γdk, γcp, γpo, γnm, γnw, γl, γlk, γI, γpi, R⟩
  icases (ghostVar_split_half (GF := GF) γlk 1 (∅ : GMap GoString Nat)).1 $$ Hlk with ⟨Hlk1, Hlk2⟩
  icases (ghostVar_split_half (GF := GF) γnm 1 (none : Option GoString)).1 $$ Hnm with ⟨Hnm1, Hnm2⟩
  icases (ghostVar_split_half (GF := GF) γnw 1 ([] : List GoString)).1 $$ Hnw with ⟨Hnw1, Hnw2⟩
  icases (ghostVar_split_half (GF := GF) γpo 1 WalOut.empty).1 $$ Hpo with ⟨Hpo1, Hpo2⟩
  icases (ghostMapAuth_halves (GF := GF) γt (∅ : GMap GoString GName)).1 $$ Ht with ⟨Ht1, Ht2⟩
  icases (ghostVar_split_half (GF := GF) γpk 1 true).1 $$ Hpk with ⟨Hpk1, Hpk2⟩
  icases (ghostVar_split_half (GF := GF) γcp 1 (none : Option GoString)).1 $$ Hcp with ⟨Hcp1, Hcp2⟩
  imodintro
  iunfold absDiskCtx at Hctx
  icases Hctx with ⟨Hs, HP, -, -⟩
  iunfold absPastAuth at HP
  icases HP with ⟨%F0, -, -, -, #Ha⟩
  iunfold absDiskStart at Hst
  icases Hst with ⟨HM, -, Hu⟩
  unfold walGhost walGhostI walPastIAuth walPastI walOwn walUnlockedTok walCrashTok walHandleAuth walCreatingAuth walTailsAuth
    walParkFrag walParkAuth walDirKeysAuth walCutFrag walCutAuth walOutFrag walOutAuth walTailsFrag
    walNamesFrag walNamesAuth walSplitFrag walSplitAuth walLentAuth walLksAuth walIncAny walIncQ walAllG
  iframe Hs HM Hu Hc Hcr HI2 Hse Ha Ht1 Ht2 Hpk1 Hpk2 Hdk Hcp1 Hcp2 Hpo1 Hpo2 Hnm1 Hnm2 Hnw1 Hnw2 Hl Hlk1 Hlk2
  icases (ghostVar_split_half (GF := GF) γI (1 : Qp).half (∅ : GMap GoString Nat)).1 $$ HI1 with ⟨HI1, HI4⟩
  isplitr
  · ipureintro; rfl
  isplitl [Hh Hhd Hhp HF HI1]
  · isplitl [HF HI1]
    · iframe HI1
      iexists ((∅ : GMap (AbsDiskState × GMap GoString Nat) Unit).insert (s, ∅) ())
      iframe HF
      isplitl
      · iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
          (m := (∅ : GMap (AbsDiskState × GMap GoString Nat) Unit))
          (Φ := fun p _ => iprop(p ↪[γpi]□ ())) rfl).2
        iframe Hse
        iapply BigSepM.bigSepM_empty.2; itrivial
      · ipureintro
        intro p hp
        rw [GMap.lookup_insert_eq_iff] at hp
        by_cases hq : ((s, ∅) : AbsDiskState × GMap GoString Nat) = p
        · subst hq; exact walLeI_refl _
        · simp only [hq, ite_false, GMap.lookup_empty] at hp; cases hp
    isplitl [Hh Hhd Hhp]
    · isplitl [Hh Hhd Hhp]
      · iexists 0, ∅, ∅, ∅
        iframe Hh Hhd Hhp
        ipureintro; intro k _; exact ⟨rfl, rfl, rfl⟩
      · ipureintro; exact LksOk.empty s
    isplitr
    · ipureintro; exact hk
    · iexact Hstp
  isplitl [HI4]
  · iexact HI4
  isplitl [HI3]
  · iexists ∅; iexact HI3
  isplitr
  · ileft; ipureintro; rfl
  · iapply BigSepM.bigSepM_empty.2; iempintro

end init

end WalFs
end EtcdGrove
end Perennial

end
