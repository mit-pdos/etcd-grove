/-
Lean-first (no Rocq counterpart).

# The WAL tester's crash invariant over `fsExt` (W4c U5, `notes/wal-fsext-w4c-plan.md`)

The main tree's `TInvBody`/`TInv`/`TBoot` (over `absDiskExt`'s `walDirIs`/`walArea`/`dirDurable` and
`durableExt`'s `durableOwnM`) restated over the part's WAL layer (`WalFs`: `walDirIs`, `walSyncedLb`,
`walNamed`, `walAreaOk`, `walAreaRes`, the lock and crash tokens) and `lib/durable` over `fsExt`
(`DurFs`: `durSt`, `durInv`, `durHandle`).

* **The environment** (`TEnv`): `Boot`'s two directories, the WAL area `area` (the WAL is `area/wal`)
  and the oracle's directory `orDir` (the oracle `orDir/state`), the file system's roots `R`, the
  area's directory `jr` and the oracle directory's `jo`. Both directories are roots of `R` (U3's boot
  premise 3: a durable directory is a root; `durable` and `Boot` create no directory, 2026-11-15): the
  closed theorem's world premises (U7).
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
* **The boot precondition of an incarnation** (`TBoot`), from the tree's shared view (`osShared`;
  how the program reaches it, U7): the invariant and the program's halves (no `Write` pending), the
  WAL's area (`walAreaOk`, `dirDurable` of the area, `walAreaRes`, the lock token), durable's (its
  invariant and handle), the whole call permission, and the two crash tokens the crash obligation takes
  (`walInv_crash`'s `walCrashTok`, durable's `durCrashTok`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Check
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

/-- The oracle file's base name (`Boot`: `orDir + "/state"`). -/
def tOrBase : GoString := go!"state"

/-- The oracle file's path is its directory's child. -/
theorem tOrPath_child (orDir : GoString) : child orDir tOrBase = tOrPath orDir := by
  simp [child, tOrBase, tOrPath]
  rfl

/-- **The tester's environment**: `Boot`'s WAL area `area` and oracle directory `orDir`, the file
system's roots `R`, the area's directory `jr` and the oracle directory's `jo` (both directories roots
of `R`). -/
structure TEnv where
  area : GoString
  orDir : GoString
  R : Roots
  jr : Ino
  jo : Ino

/-- The oracle file as `durable` manages it. -/
def TEnv.orFile (e : TEnv) : DurFs.DFile := ⟨e.orDir, e.jo, tOrBase⟩

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
  unfold WalFs.walPast WalFs.walPastI; letI := WalFs.walAllG (W := W); infer_instance

instance walSyncedLb_timeless' (dir : GoString) (i n : Nat) : Timeless (WalFs.walSyncedLb (W := W) dir i n) := by
  unfold WalFs.walSyncedLb; infer_instance

instance walNamed_timeless' (dir : GoString) (i : Nat) : Timeless (WalFs.walNamed (W := W) dir i) := by
  unfold WalFs.walNamed; infer_instance

instance walOwn_timeless' (M : GMap GoString WalDur) : Timeless (WalFs.walOwn (W := W) M) := by
  unfold WalFs.walOwn walOwnAt; infer_instance

instance walDirIs_timeless' (dir : GoString) (i : Nat) (o : Option WalDur) :
    Timeless (WalFs.walDirIsI (W := W) dir i o) := by
  unfold WalFs.walDirIsI; infer_instance

/-- **What the WAL side knows of the oracle `o`**, by its phase: after `Create` returned, some
candidate accounts for the WAL (`tCandOk`), whose mark is synced and whose entry is durable, and the
oracle is well formed for `checkRestart` (`tCheckWf`: every stored oracle is a running member's, which
`memLive` keeps so; the next incarnation's `restart` of the loaded oracle needs it); before, `tPreOk`. -/
def tRelI (area : GoString) (o : TOracle) (od : Option WalDur) : IProp GF :=
  if o.created then
    iprop(∃ (d : WalDur) (c : TCand), ⌜od = some d ∧ c ∈ o.cands ∧ tCandOk o c d ∧ tCheckWf o⌝ ∗
      WalFs.walSyncedLb (W := W) (tWalDir area) 0 (tCandMark o c) ∗ WalFs.walNamed (W := W) (tWalDir area) 0)
  else iprop(⌜tPreOk o od⌝)

instance tRelI_persistent (area : GoString) (o : TOracle) (od : Option WalDur) :
    Persistent (tRelI (W := W) (GF := GF) area o od) := by
  unfold tRelI; split <;> infer_instance

instance tRelI_timeless (area : GoString) (o : TOracle) (od : Option WalDur) :
    Timeless (tRelI (W := W) (GF := GF) area o od) := by
  unfold tRelI; split <;> infer_instance

open Iris.ProofMode in
/-- A created oracle the invariant relates is well formed. -/
theorem tRelI_checkWf (area : GoString) (o : TOracle) (od : Option WalDur) (hcr : o.created = true) :
    tRelI (W := W) (GF := GF) area o od ⊢ ⌜tCheckWf o⌝ := by
  unfold tRelI
  simp only [hcr, ite_true]
  iintro ⟨%d, %c, %h, -, -⟩
  ipureintro; exact h.2.2.2

/-- **What the restart takes of the WAL side, for the member's candidate `cd`** (`restartRead`'s and
`restart`'s premise, B1 of the tenth session): after `Create` returned, `cd`'s mark synced and the WAL
named (`tRelI`'s facts); before, the oracle fresh up to its opens (`Boot`'s restart from an oracle stored
before `created`). With `cd ∈ o.cands` and `tCandOk o cd d` it gives `tRelI` (`tRelI_of_relW`). -/
def tRelW (area : GoString) (o : TOracle) (cd : TCand) : IProp GF :=
  if o.created then
    iprop(⌜tCheckWf o⌝ ∗ WalFs.walSyncedLb (W := W) (tWalDir area) 0 (tCandMark o cd) ∗
      WalFs.walNamed (W := W) (tWalDir area) 0)
  else iprop(⌜tPre o⌝)

instance tRelW_persistent (area : GoString) (o : TOracle) (cd : TCand) :
    Persistent (tRelW (W := W) (GF := GF) area o cd) := by
  unfold tRelW; split <;> infer_instance

open Iris.ProofMode in
theorem tRelI_of_relW (area : GoString) (o : TOracle) (cd : TCand) (d : WalDur)
    (hcd : cd ∈ o.cands) (hok : tCandOk o cd d) :
    tRelW (W := W) (GF := GF) area o cd ⊢ tRelI (W := W) area o (some d) := by
  unfold tRelW tRelI
  cases hcr : o.created with
  | true =>
    simp only [ite_true]
    iintro ⟨%hw, #Hsl, #Hnm⟩
    iexists d, cd
    iframe Hsl Hnm
    ipureintro; exact ⟨rfl, hcd, hok, hw⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    iintro %hpre
    ipureintro
    have : cd = tCand0 := by simpa [tPre_cands hpre] using hcd
    subst this
    exact ⟨hpre, Or.inr ⟨d, rfl, hok⟩⟩

/-- **The pending oracle's relation**: while a `Write` is pending, the oracle before it accounts for
the WAL too. -/
def tRelA (area : GoString) (oa : Option TOracle) (od : Option WalDur) : IProp GF :=
  match oa with
  | none => iprop(emp)
  | some o' => tRelI (W := W) area o' od

instance tRelA_persistent (area : GoString) (oa : Option TOracle) (od : Option WalDur) :
    Persistent (tRelA (W := W) (GF := GF) area oa od) := by
  unfold tRelA; split <;> infer_instance

instance tRelA_timeless (area : GoString) (oa : Option TOracle) (od : Option WalDur) :
    Timeless (tRelA (W := W) (GF := GF) area oa od) := by
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
    WalFs.walDirIsI (W := W) (tWalDir e.area) 0 od ∗ ghostVar γ.γw (1 : Qp).half od ∗
    tRelI (W := W) e.area o od ∗ tRelA (W := W) e.area oa od)

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

/-- **The tester's call permission, the WAL's fraction `q`**: the call permission of the WAL directory's
key (`tWalDir e.area`'s, the area root's: an open WAL's handle holds the rest, `WAL.Close` gives it back
under that key) and the whole one of the oracle directory's root (two distinct roots; only the oracle
file's `durable` calls use it). -/
def tPerm (e : TEnv) (q : Qp) : IProp GF :=
  iprop(osCallPerm (L := L) (callKey e.R (tWalDir e.area)) q ∗ osCallPerm (L := L) (callKey e.R e.orDir) 1)

/-- The WAL directory is the area's `wal`. -/
theorem tWalDir_child (a : GoString) : tWalDir a = child a go!"wal" := rfl

/-- The WAL directory's key is the area root's. -/
theorem tWalDir_key {R : Roots} {a : GoString} {jr : Ino} (hR : RootsOk R) (hr : (a, jr) ∈ R) :
    callKey R (tWalDir a) = callKey R a := by
  rw [callKey_eq hR hr (.inr ⟨go!"wal", by rw [tWalDir_child]; simp⟩), callKey_eq hR hr (.inl rfl)]

open Iris.ProofMode in
/-- **The tester's whole permission, from the shared view's** (`osShared`'s `osCallPerms`): the wholes of
the area's root and of the oracle directory's (distinct roots). -/
theorem tPerm_of_osCallPerms (e : TEnv) {jr jo : Ino} (hR : RootsOk e.R) (hr : (e.area, jr) ∈ e.R)
    (ho : (e.orDir, jo) ∈ e.R) (hne : jo ≠ jr) :
    osCallPerms (L := L) e.R ⊢ tPerm (L := L) e 1 := by
  have hao : e.orDir ≠ e.area := by
    intro h
    apply hne
    have := eq_of_nodup_map hR.1 ho hr (by simpa using h)
    simpa using congrArg Prod.snd this
  have hon : ([] : GoString) ≠ e.orDir := by
    obtain ⟨cs, hcs, -, hrc⟩ := (hR.2.2 _ ho).1
    intro h0
    rw [← h0] at hrc
    cases cs with
    | nil => exact hcs rfl
    | cons c cs => simp [joinPath] at hrc
  unfold tPerm
  iintro H
  icases osCallPerms_root e.R e.area jr hR hr $$ H with ⟨Ha, Hrest⟩
  have hl : GMap.delete e.area (GMap.delete [] (permMap e.R)) !! e.orDir = some () := by
    rw [GMap.lookup_delete_ne _ (Ne.symm hao), GMap.lookup_delete_ne _ hon]
    exact permMap_lookup e.R e.orDir (.inr ⟨jo, ho⟩)
  icases (BigSepM.bigSepM_delete (M := GMap GoString)
    (Φ := fun (r' : GoString) (_u : Unit) => osCallPerm (L := L) r' 1) (x := ()) hl).1 $$ Hrest
    with ⟨Ho, -⟩
  rw [tWalDir_key hR hr]
  iframe Ha
  rw [callKey_eq hR ho (.inl rfl)]
  iexact Ho

open Iris.ProofMode in
/-- **The WAL's half back** (`member.close`, then `restart`): the tester's half and the half the handle
held make the whole. -/
theorem tPerm_join (e : TEnv) :
    tPerm (L := L) e (1 : Qp).half ∗ osCallPerm (L := L) (callKey e.R (tWalDir e.area)) (1 : Qp).half ⊢
      tPerm (L := L) e 1 := by
  unfold tPerm
  iintro ⟨⟨Ha, Ho⟩, Hb⟩
  iframe Ho
  have h := osCallPerm_split (L := L) (callKey e.R (tWalDir e.area)) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iapply h.2
  iframe

/-- **The boot precondition of an incarnation** (generation `L`), after the shared mode's switch:
fresh WAL names `W`; the invariant and the program's halves (the oracle `o`, no `Write` pending; the
WAL state `od`); the WAL's area (`walAreaOk` over the WAL's codec and raftpb's marshaller, U4), the
area's durability (`Create`'s `dirDurable r`), the program's part of the area and the lock token;
durable's invariant and handle on the oracle file; the whole call permission (`tPerm`); the crash tokens the
crash obligation takes (`walInv_crash`'s, durable's). -/
def TBoot (e : TEnv) : IProp GF :=
  iprop(∃ (W : WalGS GF) (γ : TGS) (o : TOracle) (od : Option WalDur),
    TInv (W := W) e γ ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗
    WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
    WalFs.dirDurable (W := W) (e.area) ∗ WalFs.walAreaRes (W := W) e.jr ∗ WalFs.walUnlockedTok (W := W) ∗
    DurFs.durInv γ.γd e.orFile ∗ DurFs.durHandle γ.γd e.orFile e.R ∗ tPerm e 1 ∗
    WalFs.walCrashTok (W := W) ∗ DurFs.durCrashTok γ.γd)

/-- **The program's part of `TBoot`** at its witnesses (the WAL names `W`, the ghost names `γ`, the oracle
`o`, the WAL state `od`): `TBoot` without the crash tokens. -/
def TRun (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur) : IProp GF :=
  iprop(TInv (W := W) e γ ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗
    WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
    WalFs.dirDurable (W := W) (e.area) ∗ WalFs.walAreaRes (W := W) e.jr ∗ WalFs.walUnlockedTok (W := W) ∗
    DurFs.durInv γ.γd e.orFile ∗ DurFs.durHandle γ.γd e.orFile e.R ∗
    tPerm e 1)

open Iris.ProofMode in
/-- **`TBoot` is the program's part and the crash tokens.** -/
theorem TBoot_run (e : TEnv) :
    TBoot (L := L) e ⊣⊢ ∃ (W : WalGS GF) (γ : TGS) (o : TOracle) (od : Option WalDur),
      TRun W e γ o od ∗ WalFs.walCrashTok (W := W) ∗ DurFs.durCrashTok γ.γd := by
  unfold TBoot TRun
  constructor
  · iintro ⟨%W, %γ, %o, %od, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12⟩
    iexists W, γ, o, od; iframe
  · iintro ⟨%W, %γ, %o, %od, ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩, H11, H12⟩
    iexists W, γ, o, od; iframe

end boot

end etcd_wal
end EtcdGrove
end Perennial
