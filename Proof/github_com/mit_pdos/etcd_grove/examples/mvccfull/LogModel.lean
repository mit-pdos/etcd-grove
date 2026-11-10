/-
mvccfull's writer: **the operation log's model** (pure; `notes/mvccfull-proof-plan.md`, W). Lean-first
(no Rocq counterpart). Split out of `Writer.lean` (review round 2's S6, 2026-11-10), so that the
model's facts (`LogLemmas.lean`) import the model only.

The log (`x.log`) holds each operation at a pure value `OpM` (its choices, its slices' contents as
strings). The tester's model is a pure function of the log's prefixes (`runM ks ops n`, `MSt`): the
history of revisions (`hs`), the compaction revision, the live leases (increasing), the ids ever
granted. A member that has applied `n` operations is at the store state `σOf ks ops n`, its Go
model fields `revAfter`, `cmpAfter`, `leasesAfter` of `n`. **`logOk`**: every operation is valid
for the state it applies to (`opValid`). The model's facts along a valid log are `LogLemmas.lean`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Members
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/-! ## The operation log's model (pure) -/

section model
variable [GooseExts]

/-- The operations' kinds (`opPut`, ..., `opLeases`). -/
abbrev kPut : w64 := W64 0
abbrev kDelete : w64 := W64 1
abbrev kTxn : w64 := W64 2
abbrev kGrant : w64 := W64 3
abbrev kRevoke : w64 := W64 4
abbrev kCompact : w64 := W64 5
abbrev kCommit : w64 := W64 6
abbrev kRead : w64 := W64 7
abbrev kLeases : w64 := W64 8

/-- **A range read's request** (`rangeReq`), its slices as strings (`endNil`: a `nil` end). -/
structure RangeM where
  key : GoString
  e : GoString
  endNil : Bool
  ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions

/-- **A transaction's sub-operation** (`subOp`): a put (`0`), a range delete (`1`) or a range read
(`2`). -/
structure SubM where
  kind : w64
  key : GoString
  e : GoString
  endNil : Bool
  val : GoString
  lease : w64
  q : RangeM

/-- **An operation of the log** (`op`), every choice made. -/
structure OpM where
  kind : w64
  key : GoString
  e : GoString
  endNil : Bool
  val : GoString
  lease : w64
  q : RangeM
  write : Bool
  shared : Bool
  subs : List SubM
  id : w64
  rev : w64
  wait : Bool

/-- **The model after a prefix of the log**: the history of revisions (`hs[r]`: revision `r`'s
state and changes; revisions `0` and `1` empty), the compaction revision (`-1`: none), the live
leases (in grant order, so increasing), every id ever granted. -/
structure MSt where
  hs : List HRev
  crev : Int
  leases : List w64
  granted : List w64
  /-- the revisions of the successful compactions, in order (the history's `comps`) -/
  comps : List w64

/-- The model before any operation. -/
def mStart : MSt := ⟨hist0, -1, [], [], []⟩

/-- The model's revision (the history's last). -/
def MSt.rev (s : MSt) : Nat := s.hs.length - 1

/-- The last revision's state of a history. -/
def lastSt (Hs : List HRev) : GMap GoString kvRec := (Hs[Hs.length - 1]?.map Prod.fst).getD ∅

/-- The history after a revision's model: the pending revision appended if it has a change. -/
def histAfter (Hs : List HRev) (P : PendM) : List HRev :=
  if P.chs = [] then Hs else Hs ++ [(P.st, P.chs)]

/-- **The tester's test of a key on the lease `id`** in `M` (`ok && e.lease == id`). -/
def onLease (M : GMap GoString kvRec) (id : w64) (k : GoString) : Bool :=
  match M !! k with
  | some e => decide (e.lease' = id)
  | none => false

/-- A write transaction's sub-operation on its pending model (`writeSub`). -/
def subStep (ks : List GoString) (P : PendM) (s : SubM) : PendM :=
  if s.kind = W64 0 then P.put s.key s.val s.lease
  else if s.kind = W64 1 then P.del ks s.endNil s.key s.e
  else P

/-- **The pending model of the revision an operation makes** at the model `s` (`apply`'s `p`):
from the last state at the next revision number, a put, a range delete, a write transaction's
sub-operations, a revoke's deletes (the keys on the lease, in order); nothing for the others. -/
def opPend (ks : List GoString) (s : MSt) (o : OpM) : PendM :=
  let P0 : PendM := ⟨W64 (s.hs.length : Int), lastSt s.hs, []⟩
  if o.kind = kPut then P0.put o.key o.val o.lease
  else if o.kind = kDelete then P0.del ks o.endNil o.key o.e
  else if o.kind = kTxn then (if o.write then o.subs.foldl (subStep ks) P0 else P0)
  else if o.kind = kRevoke then (ks.filter (onLease P0.st o.id)).foldl PendM.delOne P0
  else P0

/-- **One operation's model step**: the revision appended if it changed something, the
compaction revision raised by a compaction above it and not past the revision, the live leases
after a grant or a revoke, the granted ids after a grant. -/
def opStep (ks : List GoString) (s : MSt) (o : OpM) : MSt :=
  let cok := decide (o.kind = kCompact ∧ s.crev < sint.Z o.rev ∧ sint.Z o.rev ≤ (s.rev : Int))
  { hs := histAfter s.hs (opPend ks s o),
    crev := if cok then sint.Z o.rev else s.crev,
    comps := if cok then s.comps ++ [o.rev] else s.comps,
    leases := if o.kind = kGrant then s.leases ++ [o.id]
      else if o.kind = kRevoke then s.leases.filter (· != o.id) else s.leases,
    granted := if o.kind = kGrant then s.granted ++ [o.id] else s.granted }

/-- **The model after the first `n` operations of the log.** -/
def runM (ks : List GoString) (ops : List OpM) (n : Nat) : MSt := (ops.take n).foldl (opStep ks) mStart

/-- The member's `rev`, `cmp`, `leases` after `n` operations, and the history then. -/
abbrev revAfter (ks : List GoString) (ops : List OpM) (n : Nat) : Nat := (runM ks ops n).rev
abbrev cmpAfter (ks : List GoString) (ops : List OpM) (n : Nat) : Int := (runM ks ops n).crev
abbrev leasesAfter (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 := (runM ks ops n).leases
abbrev grantedAfter (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 :=
  (runM ks ops n).granted
abbrev histAt (ks : List GoString) (ops : List OpM) (n : Nat) : List HRev := (runM ks ops n).hs
abbrev compsAt (ks : List GoString) (ops : List OpM) (n : Nat) : List w64 := (runM ks ops n).comps

/-- mvcc's change of a tester's change. -/
def toChange (c : change) : Change :=
  if c.del' then .del c.key' else .put c.key' c.kv'.val' c.kv'.lease'

/-- **mvcc's log of a history**: each revision's changes. -/
def logOfHist (Hs : List HRev) : Log := Hs.map fun e => e.2.map toChange

/-- **The store's state of a member that applied `n` operations** (nothing pending). -/
def σOf (ks : List GoString) (ops : List OpM) (n : Nat) : MvccState :=
  ⟨logOfHist (histAt ks ops n), cmpAfter ks ops n, none⟩

/-- The store's state after a write transaction begun at `σ` (nothing pending) ends with `pend`. -/
def commitSt (σ : MvccState) (pend : List Change) : MvccState := (σ.notify pend).commitPending

/-- **A pending transaction's model is the tester's** (mvccrand's, over the keys `ks`): inside a
write transaction begun at `σ`, the member's history at `Hs` (its revisions, `σ`'s), mvcc's pending
changes `pend`: `pendOf` of the last revision's state, holding the store's state after them. -/
def pendOk (ks : List GoString) (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM) :
    Prop :=
  P = pendOf (lastSt Hs) (W64 (Hs.length : Int)) pend ∧
  stMatch ks P.st (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) pend)

/-- What `view` returns: the states (the pending one appended once it has a change), their
fractions, the revision a read in the transaction is at. -/
def viewSt (Hs : List HRev) (P : PendM) : List (GMap GoString kvRec) :=
  Hs.map Prod.fst ++ (if P.chs = [] then [] else [P.st])

def viewDq (Hs : List HRev) (P : PendM) : List DFrac :=
  List.replicate Hs.length DFrac.discard ++ (if P.chs = [] then [] else [DFrac.own 1])

def viewRev (P : PendM) : w64 := if P.chs = [] then P.rev - W64 1 else P.rev

/-- The batch limit `openBackend` configures (`cfg.BatchLimit` if positive, else
`DefaultBackendConfig`'s `10000`). -/
def limOf (cfg : Config) : w64 := if 0 < sint.Z cfg.BatchLimit' then cfg.BatchLimit' else W64 10000

/-- The compaction batch limit `open` configures (`cfg.CompactionBatchLimit` if positive, else `0`:
mvcc's default). -/
def cblOf (cfg : Config) : w64 :=
  if 0 < sint.Z cfg.CompactionBatchLimit' then cfg.CompactionBatchLimit' else W64 0

/-- **A write transaction's sub-operations, as `genSubs` makes them** (the keys
`ks`, the live leases `L`): each put's key one of the keys, its lease `0` or live; a put's key is no earlier put's and in
no earlier delete's range, and no earlier put's key is in a delete's range (etcd's
`checkIntervals`). -/
def subsOk (ks : List GoString) (L : List w64) (subs : List SubM) : Prop :=
  (∀ x ∈ subs, x.kind = W64 0 → x.key ∈ ks ∧ (x.lease = W64 0 ∨ x.lease ∈ L)) ∧
  ∀ (i j : Nat) (a b : SubM), i < j → subs[i]? = some a → subs[j]? = some b →
    (a.kind = W64 0 → b.kind = W64 0 → a.key ≠ b.key) ∧
    (a.kind = W64 1 → b.kind = W64 0 → inRangeM a.endNil a.key a.e b.key = false) ∧
    (a.kind = W64 0 → b.kind = W64 1 → inRangeM b.endNil b.key b.e a.key = false)

/-- **An operation valid at the model `s`** (see the file header). -/
def opValid (ks : List GoString) (s : MSt) (o : OpM) : Prop :=
  sint.Z o.kind < 9 ∧ 0 ≤ sint.Z o.kind ∧
  (o.kind = kPut → o.key ∈ ks ∧ (o.lease = W64 0 ∨ o.lease ∈ s.leases)) ∧
  (o.kind = kTxn → o.write = true → subsOk ks s.leases o.subs) ∧
  (o.kind = kGrant → 0 < sint.Z o.id ∧ ∀ id ∈ s.granted, sint.Z id < sint.Z o.id) ∧
  (o.kind = kRevoke → o.id ∈ s.leases) ∧
  (o.kind = kCompact → 1 ≤ sint.Z o.rev)

/-- **The log is valid**: each operation at the model before it. -/
def logOk (ks : List GoString) (ops : List OpM) : Prop :=
  ∀ i (o : OpM), ops[i]? = some o → opValid ks (runM ks ops i) o

/-- **The lease bucket holds exactly the live leases' records**, in key order (`backend.bktEnts`):
each `Grant`'s record (`leaseRecEnc`: the id, a TTL of at least the requested `3600` (the
lessor's minimum may raise it), the remaining TTL). The tracked buckets `r`. -/
def leaseRecsOk (r : GMap GoString backend.BktData) (L : List w64) : Prop :=
  ∃ recs : List (w64 × w64 × w64),
    backend.bktEnts ((r.lookup leaseName).getD ∅) = recs.map lease.leaseRecEnc ∧
    recs.map (·.1) = L ∧ ∀ x ∈ recs, 3600 ≤ sint.Z x.2.1

/-! ### The model's first facts -/

theorem runM_zero (ks : List GoString) (ops : List OpM) : runM ks ops 0 = mStart := by
  simp [runM]

/-- The step to `n + 1`. (Pure; proved.) -/
theorem runM_succ (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM) (h : ops[n]? = some o) :
    runM ks ops (n + 1) = opStep ks (runM ks ops n) o := by
  unfold runM
  rw [List.take_add_one, h, List.foldl_append]
  rfl

/-- The model of a prefix of the log is the log's (the follower's and the builder's model is the
leader's at their counts). (Pure; proved.) -/
theorem runM_prefix (ks : List GoString) (ops ops' : List OpM) (n : Nat) (hp : ops <+: ops')
    (hn : n ≤ ops.length) : runM ks ops' n = runM ks ops n := by
  obtain ⟨t, rfl⟩ := hp
  unfold runM
  rw [List.take_append_of_le_length hn]


/-! ### The model along the log (the writer's restart and restore) -/

/-- One step keeps or grows the history by one revision. -/
theorem opStep_len (ks : List GoString) (s : MSt) (o : OpM) :
    s.hs.length ≤ (opStep ks s o).hs.length ∧ (opStep ks s o).hs.length ≤ s.hs.length + 1 := by
  simp only [opStep, histAfter]
  split <;> simp

theorem foldl_opStep_len (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.hs.length ≤ (l.foldl (opStep ks) s).hs.length ∧
      (l.foldl (opStep ks) s).hs.length ≤ s.hs.length + l.length := by
  induction l with
  | nil => intro s; simp
  | cons o l ih =>
    intro s
    have h1 := opStep_len ks s o
    have h2 := ih (opStep ks s o)
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- **The model's history has at least the two empty revisions, and one more per operation at
most.** (Pure; proved.) -/
theorem runM_hs_len (ks : List GoString) (ops : List OpM) (n : Nat) :
    2 ≤ (runM ks ops n).hs.length ∧ (runM ks ops n).hs.length ≤ n + 2 := by
  have h := foldl_opStep_len ks (ops.take n) mStart
  have h0 : mStart.hs.length = 2 := rfl
  have ht : (ops.take n).length ≤ n := by simp only [List.length_take]; exact Nat.min_le_left _ _
  unfold runM
  omega

theorem foldl_opStep_prefix (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.hs <+: (l.foldl (opStep ks) s).hs := by
  induction l with
  | nil => intro s; exact List.prefix_refl _
  | cons o l ih =>
    intro s
    refine List.IsPrefix.trans ?_ (ih (opStep ks s o))
    simp only [opStep, histAfter]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

/-- **The model's history only grows along the log** (a prefix). (Pure; proved.) -/
theorem runM_hs_prefix (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    histAt ks ops n <+: histAt ks ops n' := by
  have ht : ops.take n' = ops.take n ++ (ops.take n').drop n := by
    have := List.take_append_drop n (ops.take n')
    rw [List.take_take, Nat.min_eq_left hn] at this
    exact this.symm
  unfold histAt runM
  rw [ht, List.foldl_append]
  exact foldl_opStep_prefix ks _ _

/-- The revision only grows along the log. (Pure; proved.) -/
theorem revAfter_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    revAfter ks ops n ≤ revAfter ks ops n' := by
  have := (runM_hs_prefix ks ops n n' hn).length_le
  unfold revAfter MSt.rev
  unfold histAt at this
  omega

theorem foldl_opStep_crev (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.crev ≤ (l.foldl (opStep ks) s).crev := by
  induction l with
  | nil => intro s; exact Int.le_refl _
  | cons o l ih =>
    intro s
    refine Int.le_trans ?_ (ih (opStep ks s o))
    simp only [opStep]
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; omega
    · exact Int.le_refl _

/-- The compaction revision only grows along the log. (Pure; proved.) -/
theorem cmpAfter_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    cmpAfter ks ops n ≤ cmpAfter ks ops n' := by
  have ht : ops.take n' = ops.take n ++ (ops.take n').drop n := by
    have := List.take_append_drop n (ops.take n')
    rw [List.take_take, Nat.min_eq_left hn] at this
    exact this.symm
  unfold cmpAfter runM
  rw [ht, List.foldl_append]
  exact foldl_opStep_crev ks _ _

/-- A member's store revision is the model's. (Pure; proved.) -/
theorem σOf_rev (ks : List GoString) (ops : List OpM) (n : Nat) :
    (σOf ks ops n).rev = revAfter ks ops n := by
  simp [σOf, MvccState.rev, logOfHist, revAfter, MSt.rev, histAt]

theorem σOf_notified (ks : List GoString) (ops : List OpM) (n : Nat) :
    (σOf ks ops n).notifiedLog = (σOf ks ops n).log := rfl

theorem foldl_opStep_granted (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.granted <+: (l.foldl (opStep ks) s).granted := by
  induction l with
  | nil => intro s; exact List.prefix_refl _
  | cons o l ih =>
    intro s
    refine List.IsPrefix.trans ?_ (ih (opStep ks s o))
    simp only [opStep]
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

/-- The ids ever granted only grow along the log. (Pure; proved.) -/
theorem grantedAfter_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    ∀ id ∈ grantedAfter ks ops n, id ∈ grantedAfter ks ops n' := by
  have ht : ops.take n' = ops.take n ++ (ops.take n').drop n := by
    have := List.take_append_drop n (ops.take n')
    rw [List.take_take, Nat.min_eq_left hn] at this
    exact this.symm
  intro id hid
  unfold grantedAfter runM at hid ⊢
  rw [ht, List.foldl_append]
  exact (foldl_opStep_granted ks _ _).subset hid

/-- The lease bucket's records survive re-inserting the bucket at itself. (Pure; proved.) -/
theorem leaseRecsOk_insert (r : GMap GoString backend.BktData) (L : List w64) (h : leaseRecsOk r L) :
    leaseRecsOk (r.insert leaseName ((r.lookup leaseName).getD ∅)) L := by
  obtain ⟨recs, h1, h2, h3⟩ := h
  refine ⟨recs, ?_, h2, h3⟩
  rw [GMap.lookup_insert]; exact h1

end model

end mvccfull
end EtcdGrove
end Perennial
