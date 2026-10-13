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
the workload rather than on raft, the log meets the KV's premises from the state `x₀` the server
started at (`entriesOk c₀ L x₀`: every normal entry decodes to a request with an id, within the
revision budget, ..., at every state a run of the log before it reaches; `c₀` the consistent
index the apply thread started at).

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
public import Perennial.Proof.context
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## The log raft hands the apply side (pure) -/

/-- The log `L` after the applied index `ai₀`: consecutive indices from `ai₀ + 1`, no overflow,
normal entries and v1 conf changes. -/
def srvIdxOk (ai₀ : w64) (L : List EntryModel) : Prop :=
  uint.Z ai₀ + 1 + L.length < 2 ^ 64 ∧
  ∀ (n : Nat) (m : EntryModel), L[n]? = some m →
    uint.Z m.index = uint.Z ai₀ + 1 + n ∧
      (m.typ = W32 0 ∨ (m.typ = W32 1 ∧ isConfChangeEncoding m.data))

/-- The consistent index `c` (the protocol's, `ciEff`) relative to the one the apply thread
started at, `c₀`, at the applied index `ai`: unchanged, or both at most `ai`. -/
def ciJ (c c₀ ai : w64) : Prop :=
  c = c₀ ∨ (uint.Z c₀ ≤ uint.Z ai ∧ uint.Z c ≤ uint.Z ai)

theorem srvIdxOk_prefix (ai₀ : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B)) :
    srvIdxOk ai₀ A := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp only [List.length_append] at h1; push_cast at h1; omega, fun n m hm => h2 n m ?_⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]; exact hm

/-- A batch after the log `A`: its indices are above `ai₀ + |A|`. -/
theorem srvIdxOk_batch_above (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
    (hai : uint.Z ai = uint.Z ai₀ + A.length) :
    ∀ m ∈ B, uint.Z ai < uint.Z m.index := by
  intro m hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  have := (h.2 (A.length + n) m (by rw [List.getElem?_append_right (by omega)]; simpa using hn)).1
  push_cast at this
  omega

/-- A non-empty batch after the log `A` counts up from `ai + 1` (`entriesFrom`). -/
theorem srvIdxOk_batch_from (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
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
theorem srvIdxOk_batch_last (ai₀ ai : w64) (A B : List EntryModel) (h : srvIdxOk ai₀ (A ++ B))
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

theorem entriesOk_congr (c c' : w64) (L : List EntryModel)
    (h : ∀ m ∈ L, (uint.Z c < uint.Z m.index ↔ uint.Z c' < uint.Z m.index)) (x : apply.ApplyKV) :
    entriesOk c L x ↔ entriesOk c' L x := by
  induction L generalizing x with
  | nil => simp [entriesOk]
  | cons m L ih =>
    have hm := batchStep_congr c c' m (h m (List.mem_cons_self ..))
    simp only [entriesOk, hm]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x1 hx => (ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) x1).1 (h2 x1 hx)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x1 hx => (ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) x1).2 (h2 x1 hx)⟩

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

/-- The premise of a log, after a run of its prefix: the premise of the rest. -/
theorem entriesOk_append_run (c : w64) (A B : List EntryModel) (x₀ x : apply.ApplyKV)
    (h : entriesOk c (A ++ B) x₀) (hr : entriesStep c A x₀ x) : entriesOk c B x := by
  induction A generalizing x₀ with
  | nil => simp only [entriesStep] at hr; subst hr; simpa using h
  | cons m A ih =>
    obtain ⟨x1, h1, h2⟩ := hr
    exact ih x1 (h.2 x1 h1) h2

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The raft contract's apply side, for the server** (`E.C`; see the file header): the log
after `ai₀`, consecutive, each entry's id claimed, meeting the KV's premises from `x₀` at the
consistent index `c₀`. -/
def srvC (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : IProp GF :=
  iprop(⌜srvIdxOk ai₀ L ∧ entriesOk c₀ L x₀⌝ ∗ batchWaitOk ρ E L)

instance srvC_persistent (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (L : List EntryModel) : Persistent (srvC (GF := GF) ρ E ai₀ c₀ x₀ L) := by
  unfold srvC; infer_instance

/-- The names and values the apply thread's resources are stated over (fixed for `run`). -/
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

/-- **The apply thread's resources at the log `A`** (see the file header; the one place the
chain's resource is defined: `run`'s loop invariant and its jobs' `Prev`/`Post`). -/
def applyRes (C : ApplyCtx GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV),
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfStateAddr C.ep ↦ cs ∗
    srvSnapState C.s C.ep ∗ applyThread C.γ st ∗ applyBackend C.γ C.ci C.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReader C.s ∗ srvWgReader C.s ∗ srvApplyKV C.s C.E C.γw x ∗
    srvAppliedOwn C.γr ai ∗ appliedLogAt C.γr ai x.log ∗
    ⌜loopOk C.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff C.γ st.k) C.c₀ ai ∧
      entriesStep C.c₀ A C.x₀ x⌝)

/-- The raft node contract's environment of the server: `E.C` is `srvC` (the rest is the raft
wrapper's: messages, ticks, read names, read registrations). -/
def srvRNEnv (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (M : Loc → IProp GF) (T : IProp GF) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) : RNEnv GF :=
  ⟨srvC ρ E ai₀ c₀ x₀, M, T, γr, RQ⟩

/-- **The compactor** (`s.compactor`, a `v3compactor.Compactor`, names-only: a trust-boundary
contract): nil (no auto-compaction), or one whose `Pause` and `Resume` return. -/
def compactorOk (c : GoInterface) : IProp GF :=
  iprop(⌜c = GoInterface.nil⌝ ∨ ∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Pause" ci.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Resume" ci.v)) (Val #())) {{ RET #(); True }}))

instance compactorOk_persistent (c : GoInterface) : Persistent (compactorOk (GF := GF) c) := by
  unfold compactorOk; infer_instance

/-- **The raft storage's snapshot when `run` starts** (`*raft.MemoryStorage`, names-only: a
trust-boundary contract, as `isRNMemStor`; not persistent: the snapshot changes once the server
takes one): `Snapshot()` returns the snapshot the server started from, with its metadata, a conf
state, the index `ai₀` and term `at₀`, and no error (so `run`'s `lg.Panic` and its "empty
confstate" `panic` are not reached: a construction premise, see `notes/STATUS.md`). -/
def rnSnapOnce (ms : Loc) (ai₀ at₀ : w64) : IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sn md cs pi pt : Loc), ⌜sn ≠ null ∧ md ≠ null ∧ cs ≠ null⌝ -∗
      structFieldRef go_etcd_io.raft.v3.raftpb.Snapshot go!"Metadata" sn ↦□ md -∗
      structFieldRef go_etcd_io.raft.v3.raftpb.SnapshotMetadata go!"ConfState" md ↦□ cs -∗
      structFieldRef go_etcd_io.raft.v3.raftpb.SnapshotMetadata go!"Index" md ↦□ pi -∗ optU64 pi ai₀ -∗
      structFieldRef go_etcd_io.raft.v3.raftpb.SnapshotMetadata go!"Term" md ↦□ pt -∗ optU64 pt at₀ -∗
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
errors, no content), `stop` (a unit channel `HardStop` sends on), `done`, `cancel` (the server
context's cancel function, `WithCancel`'s), the compactor, the stats, the leader-change notifier,
`leadTimeMu`'s write side, the committed index's invariant, `GoAttach`'s protocol. -/
def srvRunFieldsAt (s : Loc) (γr : ReadNames) (γg : GoNames) (γcx : context.ContextNames)
    (v : RunFields) : IProp GF :=
  iprop(srvErrorcAddr s ↦□ v.errorc ∗
      (∃ γe : ChanNames, isChanBag γe v.errorc (V := GoInterface) (fun _ => iprop(True))) ∗
    srvStopAddr s ↦□ v.stop ∗ isUnitBag v.stop ∗
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
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReader s ∗ srvWgReader s ∗ srvApplyKV s E γw x₀ ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ srvForceSnapAddr s ↦ f)

/-- **What `run` needs** (see `Spec/.../EtcdServer__run.lean`; named conjuncts): the apply
thread's view, `applyAll`'s, the raft wrapper (its node contract over the server's `E.C`), `run`'s
fields, the ticks; the snapshot's contract once; the raft wrapper's loop, apply and done tokens
at the empty log; the committed index's writer half; the right to close `done` and `stopping`;
the apply thread's resources at the start; `run`'s own logger slot; the write budget. -/
def isServerRun (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    IProp GF :=
  iprop("#Hsrv" ∷ isServer s γ ci TM E ρ γr ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvC ρ E ai₀ c₀ x₀ ∧ Er.γr = γr⌝ ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v ∗
    "#HT" ∷ □ (|==> Er.T) ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd iprop(True) .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hstart" ∷ applyStart s γ ci b E γr ai₀ c₀ x₀ ρ.wait ∗
    "Hlr" ∷ srvLgReader s ∗
    "HWB" ∷ txn.storeWTs E.γ N)

end defs

end EtcdGrove
end Perennial
