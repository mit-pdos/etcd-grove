/-
**The replay window of a restarted member** (R2d, Q9 (d) and Q13 (a), 2026-11-06; DRAFT, the
window-form round: `notes/restart-plan.md`, "R2d Scope", its amendment). Lean-first (no Rocq
counterpart).

A restarted member's ghost applied log starts at its backend's consistent index `i` (the restart is
a jump, as a snapshot's install: `applied_jump`), while Go's `ep.appliedi` starts at the WAL
snapshot's index `σ.b ≤ i`. Raft hands the entries from `σ.b + 1` again; those in `(σ.b, i]` are
already in the ghost log and Go applies them v2-only (`shouldApplyV3`'s `e.Index <=
ConsistentIndex`, `server.go:1933-1937`): no KV write, no rest-bucket write, but their in-memory
effects happen again (R2d review F8):
* the members' attributes (`UpdateAttributes` v2-only, `membership/cluster.go:467-477`): modeled,
  `RestM.mem` (`restUpdateAttrs`, `restReplay` below);
* the cluster version (`SetVersion`, `membership/cluster.go:589-623`) and the downgrade info: not
  modeled (`RestM` has neither; `restSetVersion` at `v3 = false` is the identity, and the
  downgrade's writers take `AEnv.RW`);
* a replayed conf change's transport calls (`AddPeer`/`RemovePeer`): modeled by `ccPeersAfter`'s
  `v3 = false` case. In R2d the window has no conf change (the restart's named conjunct
  `winNoConf`, `notes/restart-plan.md`'s R2d' list), so none happens there.
The apply chain's specs (`apply.spec`, `applyEntries.specBatch`, `applyAll.specBatch`) are stated
over the window's state:
* `W`, the window's entries still to be replayed (a suffix of the ghost log `A`), and `D`, those
  replayed already (`D ++ W` a suffix of `A`, `winOk`); no window: `W = D = []`;
* the ghost applied index `winGhost ai W`: Go's index `ai` plus the pending replays;
* a batch `ms` (Go's unapplied entries) starts with the next pending replays (`winAgree`); its new
  entries are `winNew W ms`, which the ghost log grows by, and the window left after it
  `winRest W ms`;
* the kv side's batch (`kvBatchW`, `kvBatch` over the new entries, at the ghost index) and the rest
  buckets' resources (`srvRestW`: the buckets at `A`'s model, the in-memory members after `A`'s model
  and then the replays `D`, v2-only, `restReplay`), which at the window's end are `srvRest`'s again
  (last writer wins over the same entries: R2d-3's lemma, a proof obligation of `apply`'s proof).

Every definition reduces to the no-window one *definitionally* at `W = D = []` (`winGhost ai [] =
ai`, `winNew [] ms = ms`, `winRest [] ms = []`, `winDone D [] ms = []`, `kvBatchW_nil`,
`srvRestW_nil`), so that the specs' no-window instances are today's texts
(`ApplyWindowLaws.lean`) and a first start's callers use them unchanged.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The window's lists (pure) -/

/-- **The ghost applied index** at Go's applied index `ai` with the replays `W` pending: `ai`
itself with no window. -/
def winGhost {α : Type} (ai : w64) : List α → w64
  | [] => ai
  | W => W64 (uint.Z ai + W.length)

/-- **A batch `ms` starts with the next pending replays `W`** (as far as both go). -/
def winAgree [GooseExts] : List EntryModel → List EntryModel → Prop
  | [], _ => True
  | _ :: _, [] => True
  | w :: W, m :: ms => w = m ∧ winAgree W ms

/-- **The new entries of a batch `ms`** past the pending replays `W`: `ms` with no window. -/
def winNew {α : Type} : List α → List α → List α
  | [], ms => ms
  | _ :: _, [] => []
  | _ :: W, _ :: ms => winNew W ms

/-- **The replays left pending after a batch `ms`**: none with no window. -/
def winRest {α : Type} : List α → List α → List α
  | [], _ => []
  | W, [] => W
  | _ :: W, _ :: ms => winRest W ms

/-- **The replays done after a batch `ms`**, from the done ones `D`: none once the window is
over (the in-memory members are then `srvRest`'s again), else `D` and the batch. -/
def winDone {α : Type} (D W ms : List α) : List α :=
  match winRest W ms with
  | [] => []
  | _ => D ++ ms

/-- **The window's premise of a call on the batch `ms`**: the done and pending replays a suffix of
the ghost log `A`, the batch starting with the pending ones. -/
def winOk [GooseExts] (A D W ms : List EntryModel) : Prop :=
  (D ++ W) <:+ A ∧ winAgree W ms

/-- No window. -/
theorem winOk_nil [GooseExts] (A ms : List EntryModel) : winOk A [] [] ms :=
  ⟨List.nil_suffix, trivial⟩

/-- **No conf change in the window** (R2d review F1, decided by etcd-grove-82 under the user's
delegation, 2026-11-06, pending the user's review; DRAFT): no entry the restart replays is a conf
change. A named conjunct of the restart's `%HEr` (R2d-2), an assumption R2d carries for R2d'
(`notes/restart-plan.md`, "R2d Draft, round 2", the R2d' list): Go replays a conf change in the
window v2-only (`server.go:1949`, `applyConfChange` at `shouldApplyV3` false, `:2031-2101`;
`ValidateConfigurationChange` accepts it, `membership/cluster.go:307-309`), which R2d does not
state. -/
def winNoConf [GooseExts] (W : List EntryModel) : Prop := ∀ m ∈ W, m.typ ≠ W32 1

/-- A first start's window is empty: trivially no conf change. -/
theorem winNoConf_nil [GooseExts] : winNoConf [] := fun _ hm => nomatch hm

/-! ## The window's resources -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`kvBatch` in the window** (Q13 (a)): the batch `ms` at Go's index `ai` with the replays `W`
pending: `kvBatch`'s facts over its new entries (`winNew W ms`) at the ghost index
(`winGhost ai W`, the ghost log's end). `kvBatch` at `W = []` (`kvBatchW_nil`, by definition). -/
def kvBatchW (γr : ReadNames) (c ai : w64) (W A ms : List EntryModel) : IProp GF :=
  iprop(srvRLogLb γr.raft (A ++ winNew W ms) ∗
    ⌜uint.Z (winGhost ai W) = uint.Z γr.raft.ai0 + A.length ∧
      ∀ m ∈ winNew W ms, (uint.Z c < uint.Z m.index ↔ uint.Z γr.kv.c0 < uint.Z m.index)⌝)

instance kvBatchW_persistent (γr : ReadNames) (c ai : w64) (W A ms : List EntryModel) :
    Persistent (kvBatchW (GF := GF) γr c ai W A ms) := by
  unfold kvBatchW; infer_instance

/-- No window: `kvBatch`. -/
theorem kvBatchW_nil (γr : ReadNames) (c ai : w64) (A ms : List EntryModel) :
    kvBatchW (GF := GF) γr c ai [] A ms = kvBatch γr c ai A ms := rfl

/-- **The rest model after the replays `D`** of the ghost log `A`'s window: `A`'s model, then each
replay's v2-only effect (`restEntry` at the ghost index, above every replay: `v3 = false`, only the
in-memory members' attributes change, `restUpdateAttrs`). -/
def restReplay (γr : ReadNames) (A D : List EntryModel) : apply.RestM :=
  D.foldl (fun r m => restEntry (W64 (uint.Z γr.raft.ai0 + A.length)) m r)
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))

/-- **`srvRest` in the window**: `srvRest`'s resources at `restReplay γr A D`. `srvRest` at
`D = []` (`srvRestW_nil`, by definition). -/
def srvRestW (E : apply.AEnv GF) (γr : ReadNames) (A D : List EntryModel) : IProp GF :=
  if E.lg then
    iprop(srvRestAt E (appliedTable γr A) (restReplay γr A D) ∗ srvEver E A)
  else E.RO (restReplay γr A D)

/-- No window: `srvRest`. -/
theorem srvRestW_nil (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRestW (GF := GF) E γr A [] = srvRest E γr A := rfl

/-- **No merged-snapshot send while a window is pending** (the Q16-3 review's finding 1, decided by
etcd-grove-82 under the user's delegation, 2026-11-06, pending the user's review; DRAFT): with the
replays `W` pending, no member of the cluster `γ` sends a `MsgSnap` (`sentMsg` of that type), so
none reaches `msgSnapC` and `applyAll`'s merge (`createMergedSnapshotMessage`, `server.go:1045`)
does not run in a window. A named conjunct of the restart's starting point beside `winNoConf`
(R2d-2), and `applyAll.specBatch`'s premise; an assumption R2d carries for R2s
(`notes/restart-plan.md`, "Assumptions R2d carries for R2d'/R2s"). Its cost: it does not hold of
every Go execution: a leader in its window does send (raft sends a snapshot to a follower behind its
log's first index, `raft.go:1877`, whatever the application's applied index), and its merge then
writes an image at Go's index below the ghost one (the review's scenario, `InvRequest.lean:2312`,
`SnapRO.lean:345,358`). R2s discharges it (the snapshots across windows). At no window it holds
trivially (`winNoMergedSend_nil`). -/
def winNoMergedSend (γ : SrvRaft) (W : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ
  iprop(⌜W = []⌝ ∨ □ (∀ (id : w64) (st : MsgSt), sentMsg γ.cl srvClusterN id st -∗ ⌜st.msg.Type' ≠ MsgSnap⌝))

instance winNoMergedSend_persistent (γ : SrvRaft) (W : List EntryModel) :
    Persistent (winNoMergedSend (GF := GF) γ W) := by
  unfold winNoMergedSend; infer_instance

/-- A first start's window is empty: no pending window, nothing assumed. -/
theorem winNoMergedSend_nil (γ : SrvRaft) : ⊢ winNoMergedSend (GF := GF) γ [] := by
  unfold winNoMergedSend
  ileft; ipureintro; rfl

end defs

end EtcdGrove
end Perennial
