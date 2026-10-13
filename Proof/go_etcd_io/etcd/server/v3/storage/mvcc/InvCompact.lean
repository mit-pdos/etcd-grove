/-
Compaction (`kvstore.go`'s `Compact` and its helpers, `kvstore_compaction.go`, `store.go`'s meta
keys, `index.go`'s and `key_index.go`'s compaction): what the specs of the compaction functions
are stated in. Lean-first (2026-10-13, the mvcc store's unit 5a; `notes/decisions.md`, "mvcc:
compaction"). The pure model is `Compact.lean`; the store's compaction state is in
`InvStore.lean` (`compactMainRev` under `s.mu` and `s.revMu`, `muInv`/`revMuInv`; the
compaction right `compactRight`; the frozen store `crevFrozen`; the keys compaction may delete,
`delKey`; the meta keys' record `metaCompact` and the finished compactions' `compactedAt`, in the
batch lock's resource).

* **The `available` map** (`map[Revision]struct{}`): `availAdd` (`doCompact` adds the revision it
  keeps, `kiAvail`), `keepApply` (`keep`: the same, but not a tombstone that ends a generation
  that is not the last, `kiKeep`); `keepSetIs A log c` (the map `treeIndex.Compact` returns: the
  revisions compaction at `c` keeps of a certified log), `keepOfIs A log rev` (`treeIndex.Keep`'s).
* **The channel `Compact` returns** (`compactChan ch Q`, the caller's receive right; the job holds
  the close right, `compactCloser`): Perennial's broadcast idiom, closed once, a receive returns
  once it is closed with `□ Q`. For a scheduled compaction at `rev`, `Q = compactDone s γ rev`:
  the compaction finished (`compactedAt γ rev`), or it was interrupted — the store's stop
  channel closed (`storeStopped`: `Close`), or the job's context cancelled (the scheduler
  stopped: `Close`/`Restore`, out of scope; the barrier then closes the channel). For
  `ErrCompacted`'s barrier, `Q = True`.
* **The job's context** (`barrierCtx`): `context.TODO()`'s value, or an `isContext` (the
  scheduler's, maybe cancelled).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ### The `available` map -/

section maps
variable [ext : FfiSyntax]

/-- `Revision`s are compared by their fields (the `available` map's keys). -/
instance revision_decEq : DecidableEq Revision := fun a b =>
  if h : a.Main' = b.Main' ∧ a.Sub' = b.Sub' then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- `doCompact`'s addition to `available` (the revision it keeps, if any). -/
def availAdd (A : GMap Revision Unit) : Option Rev → GMap Revision Unit
  | some r => GMap.insert (revVal r) () A
  | none => A

/-- `keep`'s effect on `available`: nothing for an empty key index; else `doCompact`'s addition,
taken back for a tombstone that ends a generation that is not the last (`kiKeep`). -/
def keepApply (A : GMap Revision Unit) (atRev : w64) (ki : KeyIndex) : GMap Revision Unit :=
  if kiIsEmpty ki then A
  else
    match kiAvail atRev ki with
    | none => A
    | some r =>
      if kiKeep atRev ki = some r then GMap.insert (revVal r) () A
      else GMap.delete (revVal r) (GMap.insert (revVal r) () A)

/-- The generations `doCompact` walks: some, every one but the last with a revision (its
tombstone, `g.revs[len(g.revs)-1]`; the code indexes it). -/
def gensOk (ki : KeyIndex) : Prop :=
  ki.gens ≠ [] ∧ ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ []

/-- The map `treeIndex.Compact(c)` returns: the revisions compaction at `c` keeps of the log
(`keepAt`), as `Revision` values. -/
def keepSetIs (A : GMap Revision Unit) (log : Log) (c : Int) : Prop :=
  ∀ r : Rev, (A.lookup (revVal r)).isSome ↔ keepAt log c r

/-- The map `treeIndex.Keep(rev)` returns: every key's `kiKeep` at `rev` of the log. -/
def keepOfIs (A : GMap Revision Unit) (log : Log) (rev : w64) : Prop :=
  ∀ r : Rev, (A.lookup (revVal r)).isSome ↔ ∃ k, kiKeep rev (kiOfKey (evsOf log) k) = some r

end maps

section chans
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store was stopped** (persistent): its stop channel is closed (`store.Close`; the job's
loop receives from it). -/
def storeStopped (s : Loc) : IProp GF :=
  iprop(∃ (c : GoChan) (γc : ChanNames), s.[store, go!"stopc"] ↦□ c ∗
    ownBroadcastChan c γc iprop(True) Broadcast.Done)

instance storeStopped_persistent (s : Loc) : Persistent (storeStopped (GF := GF) s) := by
  unfold storeStopped; infer_instance

/-- **A scheduled compaction at `rev` is done** (persistent; what a receive on `Compact`'s
channel gives): it finished (`compactedAt`), or it was interrupted: the store was stopped, or the
job's context (the scheduler's) was cancelled (both only when the store is closed or restored). -/
def compactDone (s : Loc) (γ : StoreNames) (rev : Int) : IProp GF :=
  iprop(compactedAt γ rev ∨ storeStopped s ∨
    ∃ cd : context.ContextDesc (IProp GF), context.ContextClosed cd.Done_gn)

instance compactDone_persistent (s : Loc) (γ : StoreNames) (rev : Int) :
    Persistent (compactDone (GF := GF) s γ rev) := by
  unfold compactDone; infer_instance

/-- **The receive right** on a channel closed once with `Q` (persistent: Perennial's broadcast
idiom). -/
def compactChan (ch : GoChan) (Q : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan ch γc Q Broadcast.Unknown)

instance compactChan_persistent (ch : GoChan) (Q : IProp GF) :
    Persistent (compactChan (GF := GF) ch Q) := by
  unfold compactChan; infer_instance

/-- **The close right** on that channel (the job's, or the barrier's): closing needs `□ Q`. -/
def compactCloser (ch : GoChan) (Q : IProp GF) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan ch γc Q Broadcast.Pending)

/-- The context a compaction job or barrier runs with: `context.TODO()`'s value (after a failed
pass, the job's barrier), or an `isContext` (the scheduler's: maybe cancelled). -/
def barrierCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(⌜ctx = todoCtxV⌝ ∨ context.isContext ctx cd)

instance barrierCtx_persistent (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (barrierCtx (GF := GF) ctx cd) := by
  unfold barrierCtx; infer_instance

/-- **What the compaction job at `rev` needs** (persistent): the store and its stop channel, its
backend supporting the compaction (`storeCmp`), a lower bound `rev` of the compaction revision
(`Compact` set it), a certified log with revision `rev`, which does not delete a key and put it
again (`NoDelPutAt`: `store.Compact`'s caller asserted it; the keys the job deletes carry it,
`delKey`; 2026-10-13, unit 6a). -/
def compactJobPre (s : Loc) (γ : StoreNames) (rev : w64) : IProp GF :=
  iprop(isStore s γ ∗ storeStop s ∗ ⌜storeCmp γ⌝ ∗ crevLb γ.idx (sint.Z rev) ∗
    ∃ log : Log, idxCert γ.idx log ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧ NoDelPutAt log (sint.Z rev)⌝)

instance compactJobPre_persistent (s : Loc) (γ : StoreNames) (rev : w64) :
    Persistent (compactJobPre (GF := GF) s γ rev) := by
  unfold compactJobPre; infer_instance

end chans

end mvcc
end EtcdGrove
end Perennial
