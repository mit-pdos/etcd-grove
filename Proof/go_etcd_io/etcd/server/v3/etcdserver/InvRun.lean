/-
**The server's apply loop, `run`** (`server.go`): the shared vocabulary of `run`'s and `start`'s
specs. Lean-first (the request path's unit 4c, 2026-10-13); see `notes/decisions.md`, "The
server's goroutines: the FIFO scheduler as a chain of saved postconditions, the construction
premise".

**The raft contract's apply side** (`srvC`, what `E.C` is for the server: `RNEnv.C`, which every
`Ready`'s committed entries carry, `rnApP`): the log `L` the raft wrapper hands the apply side,
from the node's start, is the committed entries after the applied index `ai₀` the server started
at, consecutive (`srvIdxOk`: entry `n` has index `ai₀ + 1 + n`, a normal entry or a v1 conf
change, no index past `2 ^ 64 - 1`); each normal entry's id is claimed for its data and a conf
change's is no KV request's (`batchWaitOk`: the claims of `batchCommitted`); and, a premise on
the workload rather than on raft, the log's entries have good shapes (`logShape L`: every
normal entry decodes to a request with an id that meets its premise wherever the size clauses
hold; D19c's move, 2026-10-18: until then `entriesOk c₀ L x₀`, the premises themselves at every
state a run of the log from `x₀` reaches, whose size clauses the server's construction took as a
premise, `clusterLogBound`; the apply thread now checks them at the log it meets).

**The apply thread's resources at the log `A`** (`applyRes`: one definition, chained from job to
job through the FIFO scheduler: a job's `Prev` is the previous job's `Post`): `ep`'s applied
index, term and conf state, the snapshot state, the protocol's state, the backend, the applying
index, the reader slots (logger, `bemu`, `wgMu`), the KV at `x`, the applied index's half and the
applied log; the applied index is `ai₀ + |A|`, the KV state is reached from `x₀` by a run of `A`,
and the consistent index is still `c₀` or both it and `c₀` are at most the applied index
(`ciJ`), so that a batch above the applied index meets the same `batchStep`s from either.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftLoop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Perennial.Proof.context
public import Perennial.Ghost.Token
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## The log raft hands the apply side (pure) -/

-- `srvIdxOk`: `KVModelDefs.lean` (2026-10-14, unit T1: the raft contract states it).

/-- The consistent index `c` (the protocol's, `ciEff`) relative to the one the apply thread
started at, `c₀`, at the applied index `ai`: unchanged, or both at most `ai`. -/
def ciJ (c c₀ ai : w64) : Prop :=
  c = c₀ ∨ (uint.Z c₀ ≤ uint.Z ai ∧ uint.Z c ≤ uint.Z ai)

/-- A batch after the log `A`: its indices are above `ai₀ + |A|`. -/
theorem srvIdxOk_batch_above [GooseExts] (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
    (hai : uint.Z ai = uint.Z ai₀ + A.length) :
    ∀ m ∈ B, uint.Z ai < uint.Z m.index := by
  intro m hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  have := (h.2 (A.length + n) m (by rw [List.getElem?_append_right (by omega)]; simpa using hn)).1
  push_cast at this
  omega

/-- A non-empty batch after the log `A` counts up from `ai + 1` (`entriesFrom`). -/
theorem srvIdxOk_batch_from [GooseExts] (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
    (hai : uint.Z ai = uint.Z ai₀ + A.length) (hne : B ≠ []) :
    entriesFrom (ai + 1) B ∧ uint.Z (ai + 1) = uint.Z ai + 1 := by
  have h1 : uint.Z ai₀ + 1 + (A.length : Int) + (B.length : Int) < 2 ^ 64 := by
    have := h.1; rw [List.length_append] at this; push_cast at this; omega
  have hB : (0 : Int) < B.length := by
    have := List.length_pos_iff.mpr hne; omega
  have hai0 : 0 ≤ uint.Z ai₀ := by word
  have hai1 : uint.Z (ai + 1) = uint.Z ai + 1 := by
    have : uint.Z ai + 1 < 2 ^ 64 := by omega
    word
  have e1 : 0 < uint.Z (ai + 1) := by omega
  have e2 : uint.Z (ai + 1) + B.length < 2 ^ 64 := by omega
  refine ⟨⟨e1, e2, fun n m hm => ?_⟩, hai1⟩
  have hidx : (A ++ B)[A.length + n]? = some m := by
    rw [List.getElem?_append_right (by omega)]; simpa using hm
  have := h.2 (A.length + n) m hidx
  push_cast at this
  have e3 : uint.Z m.index = uint.Z (ai + 1) + n := by omega
  exact ⟨e3, this.2⟩

/-- The applied index after a non-empty batch: its last index. -/
theorem srvIdxOk_batch_last [GooseExts] (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
    (hai : uint.Z ai = uint.Z ai₀ + A.length) :
    max (uint.Z ai) (((B.getLast?).map (fun m => uint.Z m.index)).getD 0) =
      uint.Z ai₀ + (A ++ B).length := by
  rcases List.eq_nil_or_concat B with hB | ⟨L, b, rfl⟩
  · subst hB
    have : (0 : Int) ≤ uint.Z ai := by word
    simp only [List.append_nil] at hai ⊢
    rw [show ([] : List EntryModel).getLast? = none from rfl]
    simp only [Option.map_none, Option.getD_none]
    omega
  · have hidx : (A ++ L ++ [b])[A.length + L.length]? = some b := by simp
    have := (h.2 (A.length + L.length) b (by simp only [List.append_assoc, List.concat_eq_append] at hidx ⊢; exact hidx)).1
    have hai0 : (0 : Int) ≤ uint.Z ai := by word
    simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.map_some, Option.getD_some, List.length_append,
      List.length_singleton] at this ⊢
    push_cast at this ⊢
    omega

/-- `batchStep` depends on the consistent index only through the comparison with the entry's
index. -/
theorem batchStep_congr (c c' : w64) (m : EntryModel)
    (h : uint.Z c < uint.Z m.index ↔ uint.Z c' < uint.Z m.index) :
    batchStep c m = batchStep c' m := by
  funext x x'
  unfold batchStep
  have : decide (uint.Z c < uint.Z m.index) = decide (uint.Z c' < uint.Z m.index) :=
    decide_eq_decide.mpr h
  rw [this]

theorem ciJ_iff (c c₀ ai : w64) (hJ : ciJ c c₀ ai) (m : EntryModel)
    (hm : uint.Z ai < uint.Z m.index) :
    uint.Z c < uint.Z m.index ↔ uint.Z c₀ < uint.Z m.index := by
  rcases hJ with rfl | ⟨h1, h2⟩
  · exact Iff.rfl
  · constructor <;> intro <;> omega

theorem entriesStep_congr (c c' : w64) (L : List EntryModel)
    (h : ∀ m ∈ L, (uint.Z c < uint.Z m.index ↔ uint.Z c' < uint.Z m.index))
    (x x' : apply.ApplyKV) :
    entriesStep c L x x' → entriesStep c' L x x' := by
  induction L generalizing x with
  | nil => simp [entriesStep]
  | cons m L ih =>
    have hm := batchStep_congr c c' m (h m (List.mem_cons_self ..))
    rintro ⟨x1, h1, h2⟩
    exact ⟨x1, hm ▸ h1, ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) x1 h2⟩

theorem entriesStep_append' (c : w64) (A B : List EntryModel) (x₀ x x' : apply.ApplyKV)
    (h1 : entriesStep c A x₀ x) (h2 : entriesStep c B x x') : entriesStep c (A ++ B) x₀ x' := by
  induction A generalizing x₀ with
  | nil => simp only [entriesStep] at h1; subst h1; simpa using h2
  | cons m A ih =>
    obtain ⟨x1, hm, hr⟩ := h1
    exact ⟨x1, hm, ih x1 hr⟩

theorem unapplied_all (ai : w64) (L : List EntryModel) (h : ∀ m ∈ L, uint.Z ai < uint.Z m.index) :
    unapplied ai L = L := by
  unfold unapplied
  rw [List.filter_eq_self]
  intro m hm; simpa using h m hm

/-- `ciJ` after a batch (the applied index grows; the consistent index unchanged or the larger of
itself and the new applied index). -/
theorem ciJ_step (c c' c₀ ai ai' : w64) (hJ : ciJ c c₀ ai) (hle : uint.Z ai ≤ uint.Z ai')
    (hc : c' = c ∨ uint.Z c' = max (uint.Z c) (uint.Z ai')) : ciJ c' c₀ ai' := by
  unfold ciJ at *
  rcases hc with rfl | hc
  · rcases hJ with h | ⟨h1, h2⟩
    · left; exact h
    · right; omega
  · rcases hJ with rfl | ⟨h1, h2⟩
    · by_cases hlt : uint.Z c ≤ uint.Z ai'
      · right; omega
      · left; apply BitVec.eq_of_toNat_eq; unfold uint.Z at hc hlt; omega
    · right; omega

/-! ## The server's `E.C` and the apply thread's resources -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The raft contract's apply side, for the server** (`E.C`; see the file header): the log
after `ai₀`, consecutive, each entry's id claimed, meeting the KV's premises from `x₀` at the
consistent index `c₀`. -/
-- 2026-10-14 (unit T1): the log `L` is committed (`srvRLogLb ρ.raft L`), raft's committed log's.
def srvC (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : IProp GF :=
  iprop(⌜srvIdxOk ai₀ L ∧ logShape L⌝ ∗ batchWaitOk ρ E L ∗ srvRLogLb ρ.raft L)

instance srvC_persistent (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : Persistent (srvC (GF := GF) ρ E ai₀ c₀ x₀ L) := by
  unfold srvC; infer_instance

/-- **A batch after `A` is committed entry by entry** (2026-10-14, unit C2a): its indices are
consecutive (`srvIdxOk`), so the committed index past its last index (`committedLast`, what raft's
batch carries) is past each. -/
theorem batchCommittedIdx_of_last (γr : ReadNames) (ai₀ : w64) (A ce : List EntryModel)
    (h : srvIdxOk ai₀ (A ++ ce)) :
    committedLast (GF := GF) γr ce ⊢ batchCommittedIdx γr ce := by
  rcases List.eq_nil_or_concat ce with hce | ⟨L, b, rfl⟩
  · subst hce
    iintro -
    iunfold batchCommittedIdx
    iintro !> %m %hm
    exact absurd hm List.not_mem_nil
  · have hl : (L.concat b).getLast? = some b := by simp
    unfold committedLast
    rw [hl]
    iintro #Hl
    iunfold batchCommittedIdx
    iintro !> %m %hm
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    have hlen : n < L.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hn).1; simpa using this
    have h1 := (h.2 (A.length + n) m (by
      rw [List.getElem?_append_right (by omega)]; simpa using hn)).1
    have h2 := (h.2 (A.length + L.length) b (by simp)).1
    iapply committedAtLeast_le γr b.index m.index (by push_cast at h1 h2; omega) $$ Hl

/-- The names and values the apply thread's resources are stated over (fixed for `run`; D22
receiver epochs, S7f, 2026-10-23: `γ`, `E` and `b` are the start's, the current backend's are
`applyRes`'s `ApplyBe`). -/
structure ApplyCtx (GF : BundledGFunctors) where
  s : Loc
  ep : Loc
  γ : ApplyNames
  ci : Loc
  b : GoInterface
  E : apply.AEnv GF
  γr : ReadNames
  ai₀ : w64
  c₀ : w64
  x₀ : apply.ApplyKV
  /-- the server's wait's registered ids (`ρ.wait`: the apply thread's `IsRegistered`) -/
  γw : GName
  /-- (D19i part 1) the raft wrapper's `MemoryStorage` and its names (`srvSnapState`) -/
  ms : Loc
  γs : MemStorNames
  /-- (2026-10-19, D21 M3) the write budget's counter (`srvWTPool`) -/
  wt : GName
  /-- (D22 receiver epochs, S7f) the request path's names (`isServer`'s) -/
  ρ : ReqNames

/-- **The apply thread's current backend** (D22 receiver epochs, S7f, 2026-10-23): the protocol's
names at its physical names, its batch lock's meta-keys resource, the apply environment on it and
the backend's interface value (`ci.be`). `run`'s loop invariant holds them per batch (`applyRes`):
`applySnapshot` moves them. -/
structure ApplyBe (GF : BundledGFunctors) where
  γ : ApplyNames
  TM : MetaCI → IProp GF
  E : apply.AEnv GF
  b : GoInterface

/-- **The apply thread's KV ghost state at the committed raft log `A`** (2026-10-14, unit T1):
`kvApplied`, with the model's start index and consistent index the apply thread's. -/
def kvRun (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV) : IProp GF :=
  iprop(kvApplied γr.raft γr.kv A x ∗ ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝)

/-- **The apply thread's resources at the log `A`** (see the file header; the one place the
chain's resource is defined: `run`'s loop invariant and its jobs' `Prev`/`Post`). -/
def applyRes (C : ApplyCtx GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV),
    -- (D22 receiver epochs, S7f, 2026-10-23) the current backend `B`, at the start's logical names,
    -- with the server's view at it
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServer C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKV C.s B.E C.γw x ∗
    srvAppliedOwn C.γr ai ∗ appliedLogAt C.γr ai x.log ∗ kvRun C.γr C.ai₀ C.c₀ A x ∗
    srvRest B.E C.γr A ∗ srvApRes C.s C.γr A ∗
    -- (2026-10-19, D21 M3) the write tokens taken through `ai`, the storage's cap; (D22 J5,
    -- 2026-10-26) a count `w` of the tokens taken, at least the applied index (no snapshot
    -- installed: `applyAll`'s premise; J8a's snapshot case makes it conditional)
    (∃ w : Nat, srvWTTaken C.wt w ∗ ⌜uint.Z ai ≤ w⌝) ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ ai ∧
      entriesStep C.c₀ A C.x₀ x ∧ 1 ≤ C.γs.cap ∧
      -- (D22 S-h, 2026-10-20; S-0's amendment) `ep.appliedt` the last applied entry's term
      lastTermIs A at'⌝)

/-- **The compactor** (`s.compactor`, persistent: what `run` uses): nil (the compactor off,
`AutoCompactionRetention = 0`), or a compactor with the frozen contract of the spec-first pilot
(`v3compactor.compactorOk`: its `Stop`, `Pause`, `Resume`, and its `Run` from a run token and a
run precondition; M2, `notes/m2-plan.md`, S4). `run` pauses and resumes it (persistent triples);
`start` runs it once (`compactorRun`). -/
def compactorOk (c : GoInterface) : IProp GF :=
  iprop(⌜c = GoInterface.nil⌝ ∨ ∃ (T P : IProp GF), v3compactor.compactorOk c T P)

instance compactorOk_persistent (c : GoInterface) : Persistent (compactorOk (GF := GF) c) := by
  unfold compactorOk; infer_instance

/-- **The compactor's run, once** (M2, S4; not persistent): what `start`'s `s.compactor.Run()`
spends: nil, or the compactor's contract with its run token `T` and its run precondition `P`
(`NewServer` makes them: the run token from `v3compactor.New`, `P` the environment's contracts,
`v3compactor.runPre`). -/
def compactorRun (c : GoInterface) : IProp GF :=
  iprop(⌜c = GoInterface.nil⌝ ∨ ∃ (T P : IProp GF), v3compactor.compactorOk c T P ∗ T ∗ P)

/-- The run's contract is the compactor's. -/
theorem compactorRun_ok (c : GoInterface) :
    compactorRun (GF := GF) c ⊢ compactorOk c := by
  iintro H
  iunfold compactorRun at H
  iunfold compactorOk
  icases H with (%H | ⟨%T, %P, #Hc, -, -⟩)
  · ileft; ipureintro; exact H
  · iright; iexists T, P; iexact Hc

/-- **The raft storage's snapshot when `run` starts** (`*raft.MemoryStorage`; not persistent: the
snapshot changes once the server takes one; since D17d, 2026-10-18, proved by `NewServer` from the
storage's application token, `rnSnapOnce_of_tok`, until then a trust-boundary contract):
`Snapshot()` returns the snapshot the server started from, read-only (raft's `ownSnapM` at `□`:
raft's `MemoryStorage.Snapshot` spec hands out a fresh clone, owned, which nothing writes), of
index `ai₀` and term `at₀`, with its metadata and conf-state pointers allocated (`pm`, `cs`:
`run` reads `sn.Metadata.ConfState` directly, and its "empty confstate" `panic` is not reached;
nor its `lg.Panic`, the error being nil: a construction premise, see `notes/STATUS.md`). Since
stage R6 of the raft v3.7 retarget (2026-10-16) over raft's record; until then field by field
(`optU64`), with the conf-state pointer's non-nilness stated; until stage R8b (2026-10-16) the
pointers were non-nil by the conf state having a voter (`Voters' ≠ []`), which a new cluster's
fresh `MemoryStorage` (an empty conf state, allocated by raft's `EnsureSnapshot`) does not meet:
`run` uses only the pointers. -/
def rnSnapOnce (ms : Loc) (γs : MemStorNames) (ai₀ at₀ : w64) : IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sn pm cs : Loc) (sv : SnapshotM),
      ⌜sv.Metadata'.Index' = ai₀ ∧ sv.Metadata'.Term' = at₀ ∧ pm ≠ null ∧ cs ≠ null⌝ -∗
      ownSnapM sn DFrac.discard sv -∗
      sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦□ pm -∗
      pm.[go_etcd_io.raft.v3.raftpb.SnapshotMetadata, go!"ConfState"] ↦□ cs -∗
      -- (D19i part 1) the conf state read-only for good (`ep.confState`'s first value), and
      -- (2026-10-30, the repair: raft's two-writer `MemoryStorage` specs, R1) the storage's
      -- "no snapshot taken yet" token back (`memSnapNone`, under which `Snapshot()` answers the
      -- empty snapshot; until then the application's snapshot token `memSnapTok`)
      epCsOk cs -∗ memSnapNone γs -∗
      Φ (PairV #sn #(GoInterface.nil))) -∗
    WP (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
      (Val #())) {{ Φ }})

/-- The values of the server's fields `run` reads (besides the apply thread's and the raft
wrapper's). -/
structure RunFields where
  errorc : Loc
  stop : Loc
  done : Loc
  cancel : GoFunc
  compactor : GoInterface
  stats : Loc
  leaderChanged : Loc

section addrsR
variable [GoSemanticsFunctions]
abbrev srvErrorcAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"errorc" s
abbrev srvStopAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"stop" s
abbrev srvCancelAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"cancel" s
abbrev srvCompactorAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"compactor" s
abbrev srvStatsAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"stats" s
abbrev srvLeadTimeMuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"leadTimeMu" s
end addrsR

/-- **`run`'s view of the server** at the fields' values `v` (persistent): `errorc` (a channel of
errors on which nothing is sent: a bag with predicate `False`, D19m, 2026-10-18: its senders are
`stopWithDelay`, which `apply` never asks for, and the transport's peers, which report nothing
there: `rafthttp.Transport.Start`'s axiom, D21 M2),
`stop` (the unit channel `HardStop` sends on, a bag with predicate `False`: the runs covered call
neither `Stop` nor `HardStop`, D19m), `done`, `cancel` (the server
context's cancel function, `WithCancel`'s), the compactor, the stats, the leader-change notifier,
`leadTimeMu`'s write side, the committed index's invariant, `GoAttach`'s protocol. -/
def srvRunFieldsAt (s : Loc) (γr : ReadNames) (γg : GoNames) (γcx : context.ContextNames)
    (v : RunFields) : IProp GF :=
  iprop(srvErrorcAddr s ↦□ v.errorc ∗
      (∃ γe : ChanNames, isChanBag γe v.errorc (V := GoInterface) (fun _ => iprop(False))) ∗
    srvStopAddr s ↦□ v.stop ∗
      (∃ γst : ChanNames, isChanBag γst v.stop (V := Unit) (fun _ => iprop(False))) ∗
    srvDoneAddr s ↦□ v.done ∗
    srvCancelAddr s ↦□ v.cancel ∗ context.cancelSpec v.cancel γcx iprop(True) ∗
    srvCompactorAddr s ↦□ v.compactor ∗ compactorOk v.compactor ∗
    srvStatsAddr s ↦□ v.stats ∗
    srvLeaderChangedAddr s ↦□ v.leaderChanged ∗ isNotifier v.leaderChanged ∗
    sync.isRWMutexGuard (srvLeadTimeMuAddr s) (leadTimeP s) ∗
    srvCommittedInv s γr ∗ srvGoAttachOk s γg)

instance srvRunFieldsAt_persistent (s : Loc) (γr : ReadNames) (γg : GoNames)
    (γcx : context.ContextNames) (v : RunFields) :
    Persistent (srvRunFieldsAt (GF := GF) s γr γg γcx v) := by
  unfold srvRunFieldsAt; infer_instance

/-- **The apply thread's resources when `run` starts** (at the snapshot's index `ai₀`, the KV at
`x₀`, the protocol at `st₀` with the consistent index `c₀`), but `ep`, which `run` makes: what
`applyRes []` is once `ep` is built. -/
def applyStart (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvWgReader s ∗ srvApplyKV s E γw x₀ ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRun γr ai₀ c₀ [] x₀ ∗ srvRest E γr [] ∗
    srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f)

/-- **What `run` needs** (see `Spec/.../EtcdServer__run.lean`; named conjuncts): the apply
thread's view, `applyAll`'s, the raft wrapper (its node contract over the server's `E.C`), `run`'s
fields, the ticks; the snapshot's contract once; the raft wrapper's loop, apply and done tokens
at the empty log; the committed index's writer half; the right to close `done` and `stopping`;
the apply thread's resources at the start; `run`'s own logger slot; the write budget (D19b: the
receipt-backed `srvWTPool`, until then `N` write tokens). -/
def isServerRun (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    IProp GF :=
  iprop("#Hsrv" ∷ isServer s γ ci TM E ρ γr ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (D43 M3, 2026-10-25) in raft's dynamic mode a fresh start: no entry replayed
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
    "Hrunh" ∷ rnRunHalf γn ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd iprop(True) .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hstart" ∷ applyStart s γ ci b E γr ai₀ c₀ x₀ ρ.wait ∗
    "Hlr" ∷ srvLgReader s ∗
    -- (2026-10-19, D21 M3) with its counter, the apply thread's tokens taken through `ai₀`
    "#HWB" ∷ (∃ γp : GName, srvWTPool E γp ∗ srvWTAt γp ai₀) ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`):
    -- its persistent bundle, the snapshot-taken counter's authority, the reader-slot stocks
    "Hsnapb" ∷ srvSnapBoot s ci E γr)

end defs

end EtcdGrove
end Perennial
