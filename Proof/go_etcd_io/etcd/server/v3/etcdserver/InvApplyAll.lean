/-
The apply loop's step `applyAll` (`server.go`: a batch from raft applied, the applied index's
waiters triggered, the snapshot trigger): the shared vocabulary of the specs of `applyAll`,
`applySnapshot`, `Backend`, `snapshotIfNeededAndCompactRaftLog`, `shouldSnapshotToDisk`,
`shouldSnapshotToMemory` and the trust-boundary contracts `snapshot`, `compactRaftLog` (until
D19p, 2026-10-18, also `createMergedSnapshotMessage`, `sendMergedSnap`). Lean-first (no Rocq counterpart); the request
path's unit 4b (2026-10-13).

**The server, as `applyAll` sees it** (`isServerApplyAll s γr`, persistent, beside the apply
thread's `isServer`): the applied index's waiters (`applyWait`, a `WaitTime` for
`appliedAtLeast γr`, `isWaitTime`), the raft wrapper's `msgSnapC` (a bag channel of messages,
which never delivers since D19p, 2026-10-18: raft sends no `MsgSnap` (since D21 M3 in its
no-snapshot mode, until then of a one-member cluster); until
then `applyAll` passed a received one to the merged-snapshot contract), the configuration's
`SnapshotCount`.

**The apply thread's own snapshot state** (`srvSnapState s ep`): `ep.diskSnapshotIndex`,
`ep.memorySnapshotIndex`, `s.forceDiskSnapshot` (the apply thread's: `ForceSnapshot` is called by
the apply package, `snapshot` resets it), and a reader slot of `s.bemu` (`Backend` read-locks it;
`applySnapshot`, the writer, does not run: raft's contract hands over no snapshot).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.raft.v3.MemstorageAU
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvForceSnapAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"forceDiskSnapshot" s
abbrev epDiskSnapAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"diskSnapshotIndex" ep
abbrev epMemSnapAddr (ep : Loc) : Loc := structFieldRef etcdProgress go!"memorySnapshotIndex" ep
abbrev taSnapshotAddr (ta : Loc) : Loc := structFieldRef toApply go!"snapshot" ta
abbrev taNotifycAddr (ta : Loc) : Loc := structFieldRef toApply go!"notifyc" ta
abbrev srvInflightAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"inflightSnapshots" s

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `s.bemu`'s lock invariant at fraction `q`: `s.be` at half the fraction, holding the real
backend `d`, the current backend's ghost variable `γbe` at `d` at half the fraction, and
`d`'s persistent facts (`srvBeRO`). (D22 receiver epochs, S7b, 2026-10-23: the other half of `s.be`
and a quarter of `γbe` are the apply thread's, `srvBeOwn`, a quarter of `γbe` the write budget's,
`srvWTPool`; `applySnapshot` holds all of them to swap the backend. Until then (D19i part 2) the
other half of `s.be` was `↦□`, `NewServer`'s, so the backend was known for good, which
`applySnapshot`'s store refutes.) -/
def bemuP (s : Loc) (γbe : GName) (q : Qp) : IProp GF :=
  iprop(∃ d : mvcc.KBReal, srvBeAddr s ↦{DFrac.own q.half} srvBeIface d.be ∗
    dghostVar γbe (DFrac.own q.half) d ∗ srvBeRO d)

/-- The namespace of `s.inflightSnapshots`'s invariant. -/
def srvInflightN : Namespace := nroot .@ "etcdserver_inflight_snapshots"

/-- **`s.inflightSnapshots`** (persistent; D22 S-h, 2026-10-20): the atomic count of merged
snapshots in flight, in an invariant with no content (`sendMergedSnap` adds `1`, its release
goroutine `-1`, `compactRaftLog` skips the compaction while it is not `0`: liveness only, the
proofs read nothing of its value). -/
def srvInflight (s : Loc) : IProp GF :=
  inv srvInflightN iprop(∃ n : w64, sync.atomic.ownInt64 (srvInflightAddr s) (DFrac.own 1) n)

instance srvInflight_persistent (s : Loc) : Persistent (srvInflight (GF := GF) s) := by
  unfold srvInflight; infer_instance

/-- **A reader slot of `s.bemu`** at its lock invariant over the current backend's ghost variable
`γbe` (D22 receiver epochs, S7b: the apply thread's, for `Backend` and, for `applySnapshot`, the
lock's write side; the storage-version monitor's, `srvSVRes`). -/
def srvBemuReaderAt (s : Loc) (γbe : GName) : IProp GF :=
  sync.ownRWMutex (srvBemuAddr s) (bemuP s γbe)

/-- **A reader slot of `s.bemu`** (for `Backend`: the quota checks' and `v3rpc.Server`'s), at
some current backend's ghost variable. -/
def srvBemuReader (s : Loc) : IProp GF :=
  iprop(∃ γbe : GName, srvBemuReaderAt s γbe)

/-- **The server, as `applyAll` sees it** (persistent; see the file header). -/
def isServerApplyAll (s : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (wt : GoInterface) (msc : Loc) (sc : w64),
    srvApplyWaitAddr s ↦□ wt ∗ isWaitTime wt (appliedAtLeast γr) ∗
    rnMsgSnapCAddr (srvRAddr s) ↦□ msc ∗
    (∃ (γc : ChanNames) (P : Loc → IProp GF), isChanBag γc msc (V := Loc) P ∗
      -- (D19p, 2026-10-18) it never delivers: raft sends no `MsgSnap` (D21 M3: in its
      -- no-snapshot mode; until then of a one-member cluster)
      □ (∀ m : Loc, P m -∗ False)) ∗
    srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
    -- (D19i part 1) `s.stopping`, which `applyAll` selects on beside `raftAdvancedC`
    (∃ stg : Loc, srvStoppingAddr s ↦□ stg ∗ stopChan stg) ∗
    -- (2026-10-19, D21 M3) `SnapshotCatchUpEntries`, which `compactRaftLog` reads, past the
    -- receipts' bound (`NewServer.spec`'s run bound): every compaction is at index `1`
    (∃ scu : w64, srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu ∗
      ⌜receiptBound GF ≤ uint.Z scu + 1⌝) ∗
    -- (D22 S-h, 2026-10-20) `s.inflightSnapshots`, which `compactRaftLog` reads and
    -- `sendMergedSnap` writes
    srvInflight s ∗
    -- (2026-10-26) the logger, which `compactRaftLog` logs with
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝))

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
instance isServerApplyAll_persistent (s : Loc) (γr : ReadNames) :
    Persistent (isServerApplyAll (GF := GF) s γr) := by
  unfold isServerApplyAll; infer_instance

/-- (D22 J4) The namespace of the storage's shared snapshot token (`srvSnapState`), disjoint from
the storage's own (`memSnapN`). -/
def srvStorTokN : Namespace := nroot .@ "etcdserver_stor_tok"

theorem srvStorTokN_disj : (↑srvStorTokN : CoPset) ## ↑memSnapN := by
  intro p ⟨hp, h⟩
  exact ndot_ne_disjoint nroot (by decide : "etcdserver_stor_tok" ≠ "raft_memsnap") p ⟨hp, h⟩

/-- **The apply thread's snapshot state** (see the file header) at the applied index `ai`: the
snapshot indices at most `ai`; and (D19i part 1, 2026-10-18) the raft wrapper's `MemoryStorage`
`ms` and the application's snapshot token, its snapshot index at least `sl` (`snapshot` raises it
to `ai`, which `compactRaftLog` then compacts below).

(D22 J4, 2026-10-26; decided by the orchestrator while the user was away (J5/J4), J0's item 2) **The
token shared**: the token's ghost part (`memSnapTokG`, the storage's snapshot and boundary) is in
an invariant (`srvStorTokN`, `memTokShared`: with the storage's snapshot index counted by `γss`,
the boundary at or below the snapshot), which raft's goroutine shares for its `ApplySnapshot`
(J6b) while the apply job runs `CreateSnapshot`/`Compact` (the FIFO scheduler does not wait,
`notes/j3-overlap-test/`); the apply thread keeps the storage's persistent part (`memSnapRO`),
the application's key (`memKey γs.ak`, `CreateSnapshot`'s for its critical section) and a lower
bound `sl` of the snapshot counter. Until J4 the whole token (`memSnapTok`) was the apply
thread's, with its boundary at most `ai` (false once raft's goroutine installs a snapshot past
`ai`; `CreateSnapshot`'s `prev ≤ i` now comes from `prev ≤ ss < i`). J0's ceiling `γsc` (the
storage's snapshot index at most raft's delivered log, which refutes `ApplySnapshot`'s out-of-date
branch) is J6b's, which calls `ApplySnapshot`: it adds the ceiling's lower bound to the invariant. -/
def srvSnapState (s ep ms : Loc) (γs : MemStorNames) (ai sl : w64) : IProp GF :=
  iprop(∃ (d m : w64) (f : Bool), epDiskSnapAddr ep ↦ d ∗ epMemSnapAddr ep ↦ m ∗
    srvForceSnapAddr s ↦ f ∗ ⌜uint.Z d ≤ uint.Z ai ∧ uint.Z m ≤ uint.Z ai⌝ ∗
    rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
    memSnapRO ms γs ∗ memKey γs.ak ∗
    ∃ γss : GName, inv srvStorTokN (memTokShared γs γss) ∗ monoNatLbOwn γss (uint.nat sl))

/-- (D22 J4) **The shared token, allocated** (`run`, right after its `Snapshot()`, the token's last
user in hand): from the whole token with its boundary at or below its snapshot, the invariant and
a lower bound of the counter at the snapshot's index. -/
theorem srvStorTok_alloc (ms : Loc) (γs : MemStorNames) (σ : StorState) (Ec : CoPset)
    (h : uint.Z σ.prev.index' ≤ uint.Z σ.ss.index') :
    ⊢ memSnapTok (GF := GF) ms γs σ ={Ec}=∗ memSnapRO ms γs ∗ memKey γs.ak ∗
      ∃ γss : GName, inv srvStorTokN (memTokShared γs γss) ∗
        monoNatLbOwn γss (uint.nat σ.ss.index') := by
  iintro Htok
  icases (memSnapTok_split ms γs σ).1 $$ Htok with ⟨#Hro, Hak, Htg⟩
  imod mono_nat_own_alloc (GF := GF) (uint.nat σ.ss.index') with ⟨%γss, Ha, #Hlb⟩
  imod inv_alloc srvStorTokN Ec (memTokShared γs γss) $$ [Htg Ha] with #Hinv
  · inext
    iunfold memTokShared
    iexists σ
    iframe Htg Ha
    ipureintro; exact h
  imodintro
  iframe Hro Hak
  iexists γss
  iframe Hinv Hlb

/-- A lower bound of the counter is one of every smaller index. -/
theorem srvSnapState_sl_le (s ep ms : Loc) (γs : MemStorNames) (ai sl sl' : w64)
    (h : uint.Z sl' ≤ uint.Z sl) :
    srvSnapState (GF := GF) s ep ms γs ai sl ⊢ srvSnapState s ep ms γs ai sl' := by
  iintro H
  iunfold srvSnapState at H
  icases H with ⟨%d, %m, %f, Hd, Hm, Hf, %Hdm, #Hms, #Hro, Hak, %γss, #Hinv, #Hlb⟩
  iunfold srvSnapState
  iexists d, m, f
  iframe Hd Hm Hf Hms Hro Hak
  isplitr
  · ipureintro; exact Hdm
  iexists γss
  iframe Hinv
  iapply monoNatLbOwn_le (uint.nat sl') (by word) $$ Hlb

/-! ## The apply thread's backend, per batch (D22 receiver epochs, S7f) -/

/-- **The apply environment `E` on another backend** (D22 receiver epochs, S7f, 2026-10-23): the
store's names at the physical names `p` (`mvcc.StoreNames.withPhys`), the batch lock's invariant
`P` and hook `f`, the consistent index's resources `ciC`, the rest buckets' resource `RO` and the
write right `RW` of that backend; every other field (the store's logical names, `RD`, `γrev`,
`authOn`, `FS`, `γbe`, `s`) kept. What `applySnapshot`'s `NewUberApplier` takes after the swap. -/
def apply.AEnv.onBe (E : apply.AEnv GF) (p : mvcc.PhysNames) (P : IProp GF) (f : val)
    (ciC : IProp GF → Prop) (RO : apply.RestM → IProp GF) (RW : IProp GF) : apply.AEnv GF :=
  { E with γ := E.γ.withPhys p, P := P, f := f, ciC := ciC, RO := RO, RW := RW }

/-- **The apply thread's backend after a batch** (D22 receiver epochs, S7f): the protocol's names
`γ'` are `γ`'s at some physical names, the environment `E'` is `E` on some backend
(`AEnv.onBe`). `applyAll` keeps its backend but `applySnapshot` moves it (S8). -/
def beSucc (γ : ApplyNames) (E : apply.AEnv GF) (γ' : ApplyNames) (E' : apply.AEnv GF) : Prop :=
  γ' = γ.withPh γ'.ph ∧ ∃ (p : mvcc.PhysNames) (P : IProp GF) (f : val) (ciC : IProp GF → Prop)
    (RO : apply.RestM → IProp GF) (RW : IProp GF), E' = E.onBe p P f ciC RO RW

theorem beSucc_refl (γ : ApplyNames) (E : apply.AEnv GF) : beSucc γ E γ E :=
  ⟨rfl, E.γ.phys, E.P, E.f, E.ciC, E.RO, E.RW, rfl⟩

theorem beSucc_trans {γ γ' γ'' : ApplyNames} {E E' E'' : apply.AEnv GF}
    (h1 : beSucc γ E γ' E') (h2 : beSucc γ' E' γ'' E'') : beSucc γ E γ'' E'' := by
  obtain ⟨hg1, p1, P1, f1, c1, RO1, RW1, rfl⟩ := h1
  obtain ⟨hg2, p2, P2, f2, c2, RO2, RW2, rfl⟩ := h2
  refine ⟨?_, p2, P2, f2, c2, RO2, RW2, rfl⟩
  obtain ⟨⟩ := γ; obtain ⟨⟩ := γ'; obtain ⟨⟩ := γ''
  simp only [ApplyNames.withPh, ApplyNames.mk.injEq] at hg1 hg2 ⊢
  grind

/-- The environment's logical fields, kept by `beSucc`. -/
theorem beSucc_γbe {γ γ' : ApplyNames} {E E' : apply.AEnv GF} (h : beSucc γ E γ' E') :
    E'.γbe = E.γbe := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h; rfl

/-- The batch's claims do not depend on the environment's backend. -/
theorem batchWaitOk_beSucc {γ γ' : ApplyNames} {E E' : apply.AEnv GF} (h : beSucc γ E γ' E')
    (ρ : ReqNames) (ms : List EntryModel) : batchWaitOk ρ E' ms = batchWaitOk ρ E ms := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h; rfl

/-- The write budget does not depend on the environment's backend (only on `γbe`). -/
theorem srvWTPool_beSucc {γ γ' : ApplyNames} {E E' : apply.AEnv GF} (h : beSucc γ E γ' E')
    (γp : GName) : srvWTPool E' γp = srvWTPool E γp := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h; rfl

end defs

end EtcdGrove
end Perennial
