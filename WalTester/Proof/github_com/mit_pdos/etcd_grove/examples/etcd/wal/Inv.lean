/-
Lean-first (no Rocq counterpart).

# The WAL tester's crash invariant over `fsExt` (W4c U5, `notes/wal-fsext-w4c-plan.md`)

The main tree's `TInvBody`/`TInv`/`TBoot` (over `absDiskExt`'s `walDirIs`/`walArea`/`dirDurable` and
`durableExt`'s `durableOwnM`) restated over the part's WAL layer (`WalFs`: `walDirIs`, `walSyncedLb`,
`walNamed`, `walAreaOk`, `walAreaRes`, the lock and crash tokens) and `lib/durable` over `fsExt`
(`DurFs`: `durSt`, `durInv`, `durHandle`).

* **The environment** (`TEnv`): the tester's `root`, the file system's roots `R`, the area's directory
  `jr` and the oracle directory's `jo`. The area `tArea root` (`root/data/member`) and the oracle's
  directory `tOrDir root` (`root/oracle`) are both roots of `R` (U3's boot premise 3: a durable
  directory is a root; `durable` creates no directory): the closed theorem's world premises (U7).
* **The oracle file** (`tOracleFile`): over durable's client state `DurSt` (`cur`, and `alt` while a
  `Write`'s rename may be lost to a crash), the tester's oracle `o` held by `cur` and, while a `Write`
  is between its rename and its directory's sync, the oracle before it `oa = some o'` held by `alt`.
  Both must account for the WAL (`tRelI`, `tRelA`): a crash then may keep either file. The WAL does not
  move during a `Write` (the program's calls are serialized), so the old oracle's relation still holds.
  An encoding the file holds is at most 1 GiB (`tOrSmall`): `durable.Write`'s premise, and the decoder's
  bound when the next incarnation reads it.
* **The invariant** (`TInvBody`, `TInv`): durable's client half of the state, the oracle file holding the
  ghost oracles, the WAL directory holding the ghost WAL state (`walDirIs`), the program's ghost halves'
  other halves, the relations. A plain invariant, as the main tree's: the crash obligation opens it at
  `⊤` and closes it again with its contents, through the `_keep` lemmas (`WalFs.walDiskAt_crash_keep`,
  ...; durable's crash lemma likewise, U2), which keep the old generation's resources.
* **The boot precondition of an incarnation** (`TBoot`), after the shared mode's switch (`wp_osShare`;
  how the program reaches it, U7): the invariant and the program's halves (no `Write` pending), the
  WAL's area (`walAreaOk`, `dirDurable` of the area, `walAreaRes`, the lock token), durable's (its
  invariant and handle), the whole call permission, and the two crash tokens the crash obligation takes
  (`walInv_crash`'s `walCrashTok`, durable's `durCrashTok`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Marshal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3 Fs WalFs

/-! ## The environment and the oracle file (pure) -/

section pure
variable [GooseExts]

/-- The oracle's directory (`Boot`: `root + "/oracle"`). -/
def tOrDir (root : GoString) : GoString := root ++ go!"/oracle"

/-- The oracle file's base name (`Boot`: `.../state`). -/
def tOrBase : GoString := go!"state"

/-- The oracle file's path is its directory's child. -/
theorem tOrPath_child (root : GoString) : child (tOrDir root) tOrBase = tOrPath root := by
  simp [child, tOrDir, tOrBase, tOrPath]
  rfl

/-- **The tester's environment**: its `root`, the file system's roots `R`, the WAL area's directory
`jr` (`tArea root`, a root of `R`) and the oracle directory's `jo` (`tOrDir root`, a root of `R`). -/
structure TEnv where
  root : GoString
  R : Roots
  jr : Ino
  jo : Ino

/-- The oracle file as `durable` manages it. -/
def TEnv.orFile (e : TEnv) : DurFs.DFile := ⟨tOrDir e.root, e.jo, tOrBase⟩

/-- **An oracle the file may hold**: its encoding at most 1 GiB (`durable.Write`'s premise). -/
def tOrSmall (o : TOracle) : Prop := (tEncodeOracle o).length ≤ 0x40000000

/-- **The file contents `v` hold the oracle `o`**: its encoding, or no file and the fresh oracle. -/
def tOrHolds (v : Option GoString) (o : TOracle) : Prop :=
  (v = some (tEncodeOracle o) ∧ tOrSmall o) ∨ (v = none ∧ o = tFreshOracle)

/-- **The oracle file holds `o`** (durable's `cur`) **and, while a `Write` may still be lost to a crash,
the oracle before it `oa = some o'`** (durable's `alt`). -/
def tOracleFile (s : DurFs.DurSt) (o : TOracle) (oa : Option TOracle) : Prop :=
  tOrHolds s.cur o ∧ match s.alt, oa with
    | none, none => True
    | some v, some o' => tOrHolds v o'
    | _, _ => False

/-- With no `Write` pending, durable's state has no `alt`. -/
theorem tOracleFile_alt {s : DurFs.DurSt} {o : TOracle} (h : tOracleFile s o none) : s.alt = none := by
  obtain ⟨-, h⟩ := h
  cases hs : s.alt with
  | none => rfl
  | some v => rw [hs] at h; exact h.elim

/-- **A `Write`'s rename** (its first update): the file holds the new oracle `o'`, the old one `o`
pending. -/
theorem tOracleFile_write {s : DurFs.DurSt} {o o' : TOracle} (h : tOracleFile s o none)
    (hs : tOrSmall o') :
    tOracleFile ⟨some (tEncodeOracle o'), some s.cur⟩ o' (some o) :=
  ⟨Or.inl ⟨rfl, hs⟩, h.1⟩

/-- **A `Write`'s directory sync** (its second update): nothing pending. -/
theorem tOracleFile_sync {s : DurFs.DurSt} {o' : TOracle} {oa : Option TOracle}
    (h : tOracleFile s o' oa) : tOracleFile ⟨s.cur, none⟩ o' none :=
  ⟨h.1, trivial⟩

/-- No file, no `Write` pending: the fresh oracle. -/
theorem tOracleFile_fresh : tOracleFile ⟨none, none⟩ tFreshOracle none :=
  ⟨Or.inr ⟨rfl, rfl⟩, trivial⟩

/-- **A crash keeps the file at `cur` or at `alt`'s contents**: either holds one of the oracles,
which the next generation starts from with nothing pending. -/
theorem tOracleFile_crash {s : DurFs.DurSt} {o : TOracle} {oa : Option TOracle}
    (h : tOracleFile s o oa) (v : Option GoString) (hv : v = s.cur ∨ s.alt = some v) :
    ∃ o'', (o'' = o ∨ oa = some o'') ∧ tOracleFile ⟨v, none⟩ o'' none := by
  obtain ⟨hc, ha⟩ := h
  rcases hv with rfl | hv
  · exact ⟨o, Or.inl rfl, hc, trivial⟩
  · rw [hv] at ha
    cases oa with
    | none => exact ha.elim
    | some o' => exact ⟨o', Or.inr rfl, ha, trivial⟩

end pure

/-! ## The invariant (per generation) -/

/-- The invariant's namespace. -/
def tN : Namespace := nroot .@ "etcd_wal_tester"

/-- The tester's ghost names of a generation: durable's file, the oracles, the WAL state. -/
structure TGS where
  γd : DurFs.DurGS
  γo : GName
  γw : GName

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

instance walPast_timeless' (s : AbsDiskState) : Timeless (WalFs.walPast (W := W) s) := by
  unfold WalFs.walPast absPastAt; infer_instance

instance walSyncedLb_timeless' (dir : GoString) (n : Nat) : Timeless (WalFs.walSyncedLb (W := W) dir n) := by
  unfold WalFs.walSyncedLb; infer_instance

instance walNamed_timeless' (dir : GoString) : Timeless (WalFs.walNamed (W := W) dir) := by
  unfold WalFs.walNamed; infer_instance

instance walOwn_timeless' (M : GMap GoString WalDur) : Timeless (WalFs.walOwn (W := W) M) := by
  unfold WalFs.walOwn walOwnAt; infer_instance

instance walDirIs_timeless' (dir : GoString) (o : Option WalDur) :
    Timeless (WalFs.walDirIs (W := W) dir o) := by
  unfold WalFs.walDirIs; infer_instance

/-- **What the WAL side knows of the oracle `o`**, by its phase: after `Create` returned, some
candidate accounts for the WAL (`tCandOk`), whose mark is synced and whose entry is durable; before,
`tPreOk`. -/
def tRelI (root : GoString) (o : TOracle) (od : Option WalDur) : IProp GF :=
  if o.created then
    iprop(∃ (d : WalDur) (c : TCand), ⌜od = some d ∧ c ∈ o.cands ∧ tCandOk o c d⌝ ∗
      WalFs.walSyncedLb (W := W) (tWalDir root) (tCandMark o c) ∗ WalFs.walNamed (W := W) (tWalDir root))
  else iprop(⌜tPreOk o od⌝)

instance tRelI_persistent (root : GoString) (o : TOracle) (od : Option WalDur) :
    Persistent (tRelI (W := W) (GF := GF) root o od) := by
  unfold tRelI; split <;> infer_instance

instance tRelI_timeless (root : GoString) (o : TOracle) (od : Option WalDur) :
    Timeless (tRelI (W := W) (GF := GF) root o od) := by
  unfold tRelI; split <;> infer_instance

/-- **The pending oracle's relation**: while a `Write` is pending, the oracle before it accounts for
the WAL too. -/
def tRelA (root : GoString) (oa : Option TOracle) (od : Option WalDur) : IProp GF :=
  match oa with
  | none => iprop(emp)
  | some o' => tRelI (W := W) root o' od

instance tRelA_persistent (root : GoString) (oa : Option TOracle) (od : Option WalDur) :
    Persistent (tRelA (W := W) (GF := GF) root oa od) := by
  unfold tRelA; split <;> infer_instance

instance tRelA_timeless (root : GoString) (oa : Option TOracle) (od : Option WalDur) :
    Timeless (tRelA (W := W) (GF := GF) root oa od) := by
  unfold tRelA; split <;> infer_instance

/-- **The program's half of the oracles**: the oracle `o` and the pending one `oa`. -/
def tOrOwn (γ : TGS) (o : TOracle) (oa : Option TOracle) : IProp GF :=
  ghostVar γ.γo (1 : Qp).half (o, oa)

/-- **The program's half of the WAL state** `od`. -/
def tWalOwn (γ : TGS) (od : Option WalDur) : IProp GF := ghostVar γ.γw (1 : Qp).half od

instance tOrOwn_timeless (γ : TGS) (o : TOracle) (oa : Option TOracle) :
    Timeless (tOrOwn (GF := GF) γ o oa) := by
  unfold tOrOwn; infer_instance

instance tWalOwn_timeless (γ : TGS) (od : Option WalDur) : Timeless (tWalOwn (GF := GF) γ od) := by
  unfold tWalOwn; infer_instance

/-- **The tester's crash invariant's contents** (generation `L`, WAL names `W`): durable's client half
of the oracle file's state `s`, which holds the oracle `o` (and the pending `oa`, `tOracleFile`), the
WAL directory holding `od`, the other halves of the program's ghost variables, and the relations of
both oracles to the WAL. -/
def TInvBody (e : TEnv) (γ : TGS) : IProp GF :=
  iprop(∃ (s : DurFs.DurSt) (o : TOracle) (oa : Option TOracle) (od : Option WalDur),
    DurFs.durSt γ.γd s ∗ ⌜tOracleFile s o oa⌝ ∗ ghostVar γ.γo (1 : Qp).half (o, oa) ∗
    WalFs.walDirIs (W := W) (tWalDir e.root) od ∗ ghostVar γ.γw (1 : Qp).half od ∗
    tRelI (W := W) e.root o od ∗ tRelA (W := W) e.root oa od)

instance TInvBody_timeless (e : TEnv) (γ : TGS) : Timeless (TInvBody (W := W) (GF := GF) e γ) := by
  unfold TInvBody; infer_instance

/-- **The tester's crash invariant** of the generation. -/
def TInv (e : TEnv) (γ : TGS) : IProp GF := inv tN (TInvBody (W := W) e γ)

instance TInv_persistent (e : TEnv) (γ : TGS) : Persistent (TInv (W := W) (GF := GF) e γ) := by
  unfold TInv; infer_instance

/-- The oracles' halves agree. -/
theorem tOrOwn_agree (γ : TGS) (o o' : TOracle) (oa oa' : Option TOracle) :
    ⊢@{IProp GF} tOrOwn γ o oa -∗ ghostVar γ.γo (1 : Qp).half (o', oa') -∗ ⌜o' = o ∧ oa' = oa⌝ := by
  unfold tOrOwn
  iintro H1 H2
  icases ghostVar_agree (GF := GF) γ.γo (o, oa) (1 : Qp).half (o', oa') (1 : Qp).half $$ H1 H2
    with %h
  ipureintro
  cases h; exact ⟨rfl, rfl⟩

end inv

/-! ## The boot precondition -/

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The boot precondition of an incarnation** (generation `L`), after the shared mode's switch:
fresh WAL names `W`; the invariant and the program's halves (the oracle `o`, no `Write` pending; the
WAL state `od`); the WAL's area (`walAreaOk` over the WAL's codec and raftpb's marshaller, U4), the
area's durability (`Create`'s `dirDurable r`), the program's part of the area and the lock token;
durable's invariant and handle on the oracle file; the whole call permission; the crash tokens the
crash obligation takes (`walInv_crash`'s, durable's). -/
def TBoot (e : TEnv) : IProp GF :=
  iprop(∃ (W : WalGS GF) (γ : TGS) (o : TOracle) (od : Option WalDur),
    TInv (W := W) e γ ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗
    WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (tArea e.root) ∗
    WalFs.dirDurable (W := W) (tArea e.root) ∗ WalFs.walAreaRes (W := W) e.jr ∗ WalFs.walUnlockedTok (W := W) ∗
    DurFs.durInv γ.γd e.orFile ∗ DurFs.durHandle γ.γd e.orFile e.R ∗ osCallPerm 1 ∗
    WalFs.walCrashTok (W := W) ∗ DurFs.durCrashTok γ.γd)

end boot

end etcd_wal
end EtcdGrove
end Perennial
