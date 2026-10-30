/-
Port of `election_proof/inv_storage.v` (at feb5c73d4): the `Storage` interface.

**U8 v2 (2026-10-29): the storage as range ownership** (candidate 17 rev 3,
`notes/spec-first-study/raft-storage-spec.md`, user-approved; `notes/raft-unified-plan.md`, "U8 v2").
Raft does not own the storage's state: the client may put in a snapshot or compact at any time.
The storage's log is owned by **ranges** (`storLog st k dq es`, fractional; a discarded range is the
frozen committed prefix, which only compaction removes), its end exactly (`storEnd st e`), and its
compaction point by persistent lower bounds (`storCompacted st c`). These are fields of the class
`StorageModel` (γ-free; each implementation provides them, with the §1 laws).

The contract raft relies on is `isStorageP SV Bnd st`: ordinary triples for `LastIndex`, `Term`,
`Entries`, `FirstIndex` and `Snapshot` over these ranges, and two laws (`Hbound`, the compaction's
justification `Bnd`; `Hlen`, the no-wrap bound). Its cluster-level pieces, `SV` (the snapshot's
validity, the API's `snapshotValid γ`) and `Bnd` (the API's `nodeAppliedLb`/`snapGiven`), are
parameters: this file is far below the node API. Raft's API fixes them (`isStorage γ id st`).

**Raft's view** (the second half of this file). Raft keeps, inside its log (`ownRaftLog`), a view of
the storage, `StorState` (its compaction point `prev`, the physical log `ents` above it, the batch
`pend` a `Ready` handed out, the published floor `fl`, the frozen end `fr` and the snapshot last
handed out `sg`), and `ownStorage sn st σ`, the ranges, end and authorities it holds for that view:
the frozen prefix `[c, fr]` (`□`), its owned part `(fr, kOut)` (`own 1`), the end unless a batch is
out, and the authorities of `nodeAppliedLb` (at `fl`) and `snapGiven` (at `sg`). The read triples of
the view (`isStorageWith`, `isStorageD sn st`) are **derived** from the contract (`isStorage_of_V`),
with the statements the log's proofs were written against before U8 v2 (review 1's "derived
contract"), and the hand-out, absorption, floor, lending and freezing of the view are lemmas
(`ownStorage_handout`, ...), no longer laws an implementation proves.

`InitialState` is not in the contract (it is unlocked and returns the storage's own pointers:
`issues/raft-memorystorage-initialstate-unlocked.md`).

Lean notes: a multiple return `(#li, #interface.nil)` is `PairV #li #interface.nil`; `global_addr` is
`globalAddr`. Inside `iprop(…)` a Texan triple is `□ (∀ Φ, …)`, so the contracts are persistent by
`infer_instance`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.GhostMap
public import Perennial.GooseLang.Countable

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- **Raft's view of its storage** (U8 v2; until then the storage's state as the contract stated it):
the compaction point `prev` (index and term of the entry raft's resources start at, the dummy), the
physical log `ents` after it (`π` of the design), the batch `pend` a `Ready` handed out (`[]` when
none), the floor `fl` raft published (the authority of the applied lower bounds), the frozen end
`fr` (the frozen prefix is `[prev.index, fr]`) and the snapshot index `sg` last handed out to install
(the authority of `snapGiven`). One record, so that the contract and its clients keep their shape
when what is tracked changes (notes/decisions.md, "Predicate indices"). -/
structure StorState [GooseExts] where
  prev : entryID
  ents : List EntryM
  pend : List EntryM
  fl : w64 := 0
  fr : Nat := 0
  sg : Nat := 0
  /-- (U8 v2, the snapshot's bound) the terms raft certified at committed indices (the authority of
  `raftDL`, raft's reading of the contract's `DL`): every key at most `committed`, of the log's term
  there (`DtOk`, `InvRaftlog.lean`) -/
  dt : GMap Nat w64 := ∅

/-- The term of index `i` in the log `prev :: ents`. `none` outside the range the
storage can answer for. -/
def termAt [GooseExts] (prev : entryID) (ents : List EntryM) (i : w64) : Option w64 :=
  if uint.Z i = uint.Z prev.index' then some prev.term'
  else (fun e : EntryM => e.Term') <$>
         ents[(uint.Z i - uint.Z prev.index' - 1).toNat]?

/-- (U8 v2) Two ranges of the log, `es1` from index `k1` and `es2` from `k2`, agree where they
overlap (`storLog_agree`). -/
def LogAgree [GooseExts] (k1 : Nat) (es1 : List EntryM) (k2 : Nat) (es2 : List EntryM) : Prop :=
  ∀ (i : Nat) (e1 e2 : EntryM), k1 ≤ i → k2 ≤ i → es1[i - k1]? = some e1 → es2[i - k2]? = some e2 →
    e1 = e2

/-- **The storage as range ownership** (U8 v2, candidate 17 rev 3 §1; γ-free). A *parameter* of the
development, not an assumption: every result holds for whichever model a client proves the contract
for. There is deliberately no global instance. -/
class StorageModel (GF : BundledGFunctors) [GooseExts] where
  /-- `storLog st k dq es`: the storage's entries at the indices `k, k+1, …, k+|es|-1` are `es`, or
  compacted (at the compaction point itself only the term is kept). `own 1` lets its holder write the
  range; `□` (`DFrac.discard`) is the frozen committed prefix, which nobody writes again. -/
  storLog : Storage → Nat → DFrac → List EntryM → IProp GF
  /-- `storEnd st e`: the storage's last index is exactly `e - 1` (exclusive). -/
  storEnd : Storage → Nat → IProp GF
  /-- `storCompacted st c` (persistent): the compaction point has reached `c`: `Term(i)` for `i < c`
  and `Entries(lo, …)` for `lo ≤ c` answer `ErrCompacted`; `FirstIndex` answers at least `c + 1`. -/
  storCompacted : Storage → Nat → IProp GF
  storLog_app : ∀ st k dq (a b : List EntryM),
    storLog st k dq (a ++ b) ⊣⊢ storLog st k dq a ∗ storLog st (k + a.length) dq b
  storLog_frac : ∀ st k (dq1 dq2 : DFrac) es,
    storLog st k (dq1 • dq2) es ⊣⊢ storLog st k dq1 es ∗ storLog st k dq2 es
  /-- (U8 v2: only of a non-empty range, which `storLog_nil` would otherwise contradict) -/
  storLog_valid : ∀ st k dq (es : List EntryM), es ≠ [] → storLog st k dq es ⊢ ⌜✓ dq⌝
  storLog_agree : ∀ st k1 k2 dq1 dq2 es1 es2,
    storLog st k1 dq1 es1 ∗ storLog st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝
  storLog_persist : ∀ st k dq es, storLog st k dq es ⊢ |==> storLog st k DFrac.discard es
  storLog_persistent : ∀ st k es, Persistent (storLog st k DFrac.discard es)
  storLog_nil : ∀ st k dq, ⊢ storLog st k dq []
  storEnd_excl : ∀ st e e', storEnd st e ∗ storEnd st e' ⊢ False
  storCompacted_persistent : ∀ st c, Persistent (storCompacted st c)
  storCompacted_zero : ∀ st, ⊢ storCompacted st 0
  storCompacted_mono : ∀ st c c', c' ≤ c → storCompacted st c ⊢ storCompacted st c'

export StorageModel (storLog storEnd storCompacted)

instance storLog_discard_pers {GF : BundledGFunctors} [GooseExts] [StorageModel GF] (st : Storage)
    (k : Nat) (es : List EntryM) : Persistent (storLog (GF := GF) st k DFrac.discard es) :=
  StorageModel.storLog_persistent st k es

instance storCompacted_pers {GF : BundledGFunctors} [GooseExts] [StorageModel GF] (st : Storage)
    (c : Nat) : Persistent (storCompacted (GF := GF) st c) :=
  StorageModel.storCompacted_persistent st c

section termAt
variable [GooseExts]

/-- What the storage holds once the batch `pend` is written the way `MemoryStorage.Append` does:
everything at or above the batch's first index is replaced by the batch. -/
def storApp (σ : StorState) (pend : List EntryM) : List EntryM :=
  match pend with
  | [] => σ.ents
  | e0 :: _ =>
      σ.ents.take (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat ++ pend

/-- `storApp` reads only `prev` and `ents`. -/
theorem storApp_pend (σ : StorState) (q pend : List EntryM) :
    storApp { σ with pend := q } pend = storApp σ pend := by
  cases pend <;> rfl

/-- The view once the batch out is back: the absorption's result. -/
def storAbsorb (σ : StorState) : StorState :=
  { σ with ents := storApp σ σ.pend, pend := [] }

/-- The batch out, if any, starts at or above index `n`: what the read triples ask of a query
(`Term(i)` with `n = i + 1`, `Entries(lo, hi)` with `n = hi`): raft reads only what it holds. -/
def PendFrom (σ : StorState) (n : Int) : Prop :=
  ∀ e0, σ.pend.head? = some e0 → n ≤ uint.Z e0.Index'

/-- The hand-out's premise on the batch `p`: non-empty, starting above the compaction point and at
most one past the physical log, numbered consecutively. -/
def PendOk (σ : StorState) (p : List EntryM) : Prop :=
  p ≠ [] ∧
  ∀ e0, p.head? = some e0 →
    uint.Z σ.prev.index' < uint.Z e0.Index' ∧
    uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 ∧
    ∀ (k : Nat) (e : EntryM), p[k]? = some e → uint.Z e.Index' = uint.Z e0.Index' + (k : Int)

/-- (D19i part 1) The batch starts above the floor (`StorState.fl`). -/
def PendAbove (σ : StorState) (p : List EntryM) : Prop :=
  ∀ e0, p.head? = some e0 → uint.Z σ.fl < uint.Z e0.Index'

/-- (U8 v2) The first index raft does not hold: the batch out's first, or the end. -/
def StorState.kOut (σ : StorState) : Nat :=
  match σ.pend.head? with
  | some e0 => uint.nat e0.Index'
  | none => uint.nat σ.prev.index' + 1 + σ.ents.length

/-- A snapshot's model is countable (for the pin of its validity, `svCert`). -/
instance snapshotM_countable : Pos.Countable SnapshotM :=
  countableOfLeftInverse
    (fun s : SnapshotM => (s.Data', s.Metadata'.ConfState'.Voters', s.Metadata'.ConfState'.Learners',
      s.Metadata'.ConfState'.VotersOutgoing', s.Metadata'.ConfState'.LearnersNext',
      s.Metadata'.ConfState'.AutoLeave', s.Metadata'.Index', s.Metadata'.Term'))
    (fun p => ⟨p.1, ⟨⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩⟩) (fun _ => rfl)

/-- A snapshot as raft records it is countable (for the pin of a received snapshot's certificate,
`ksnCert`). -/
instance snapTrip_countable : Pos.Countable SnapTrip :=
  countableOfLeftInverse
    (fun k : SnapTrip => (k.sid.term', k.sid.index', k.cl.voters, k.cl.learners, k.cl.outgoing,
      k.cl.learnersNext, k.al, k.dat))
    (fun p => ⟨⟨p.1, p.2.1⟩, ⟨p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl)

end termAt

/-! ## The contract over range ownership (U8 v2, candidate 17 rev 3 §2)

`isStorageP SV Bnd st`: the five methods raft reads while running, as ordinary triples over the
range vocabulary, and two laws. It is parameterized by its two cluster-level pieces, which this file
cannot name:

- `SV sv`, what a non-empty stored snapshot is (the API's `snapshotValid γ`);
- `Bnd c`, why the storage is compacted at most to `c` (the API's `∃ k, ⌜c ≤ k⌝ ∗ (nodeAppliedLb γ
  id k ∨ snapGiven γ id k)`);
- `DL i`, why a stored snapshot at index `i` is at most what raft has committed (the API's: the
  node's delivered committed prefix reaches `i`, `deliveredLogLb`, or a snapshot raft handed out
  does, `snapGiven`). (U8 v2, 2026-10-29: `maybeSendSnapshot`'s commit bound, `SnapOk`, does not
  follow from the snapshot's validity alone: a leader's commit index may lag the cluster's.)

Raft's API module fixes both (`isStorage γ id st`); no client supplies them. Persistent.

The laws: `Hbound` (`storCompacted_bound`), under an update at `⊤` (the justification is behind the
implementation's invariant: review 4, M3; at `⊤`, not the design's `↑N`, the weaker obligation, since
raft uses it only at `⊤`), and `Hlen`, the no-wrap bound of the old contract's `Hbounded`, now over
a range (a stored entry's index stays below `2^61`: what makes appending possible, the log's no-wrap
bound not being inductive; `InvRaftlog.lean`). -/

section rangeContract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See above. -/
def isStorageP (SV : SnapshotM → IProp GF) (Bnd : Nat → IProp GF) (DL : Nat → IProp GF)
    (st : Storage) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
  "%Hstok" ∷ ⌜st = interface.ok i⌝ ∗
  "#HLastIndex" ∷ (∀ (e : Nat),
     {{ storEnd st e }}
       (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
     {{ (li : w64), RET (PairV #li #interface.nil);
         storEnd st e ∗ ⌜uint.nat li + 1 = e⌝ }}) ∗
  "#HTerm" ∷ (∀ (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64) (ec : GoInterface),
     {{ storLog st k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
         globalAddr ErrCompacted ↦□ ec }}
       (App (Val #(methods i.ty go!"Term" i.v)) (Val #i0))
     {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
         storLog st k dq es ∗
         (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
          (⌜err = ec⌝ ∗ storCompacted st (uint.nat i0 + 1))) }}) ∗
  -- two pieces, a frozen prefix and an owned tail (possibly empty): N4
  "#HEntries" ∷ (∀ (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM) (lo hi maxSize : w64)
      (ec : GoInterface),
     {{ storLog st k dq1 a ∗ storLog st (k + a.length) dq2 b ∗
         ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧
           uint.nat hi ≤ k + a.length + b.length⌝ ∗
         globalAddr ErrCompacted ↦□ ec }}
       (App (App (App (Val #(methods i.ty go!"Entries" i.v)) (Val #lo)) (Val #hi))
         (Val #maxSize))
     {{ (s : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #s #err);
         storLog st k dq1 a ∗ storLog st (k + a.length) dq2 b ∗
         ((⌜err = ec⌝ ∗ storCompacted st (uint.nat lo)) ∨
          (⌜err = interface.nil⌝ ∗ entsRO s es ∗
           ⌜es ≠ [] ∧ s.cap = s.len ∧
             es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)⌝)) }}) ∗
  "#HFirstIndex" ∷ (∀ (c : Nat),
     {{ storCompacted st c }}
       (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #()))
     {{ (fi : w64), RET (PairV #fi #interface.nil);
         ⌜c + 1 ≤ uint.nat fi⌝ ∗ storCompacted st (uint.nat fi - 1) }}) ∗
  "#HSnapshot" ∷ (∀ (c : Nat) (esu : GoInterface),
     {{ storCompacted st c ∗ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
       (App (Val #(methods i.ty go!"Snapshot" i.v)) (Val #()))
     {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
         ⌜err = esu⌝ ∨
         (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
           ⌜c ≤ uint.nat sv.Metadata'.Index'⌝ ∗
           (⌜sv.Metadata'.Index' = W64 0⌝ ∨ SV sv ∗ DL (uint.nat sv.Metadata'.Index'))) }}) ∗
  "#Hbound" ∷ □ (∀ (c : Nat), storCompacted st c ={⊤}=∗ Bnd c) ∗
  "#Hlen" ∷ □ (∀ (k : Nat) (dq : DFrac) (es : List EntryM),
     storLog st k dq es -∗ ⌜es = [] ∨ k + es.length ≤ 2^61⌝ ∗ storLog st k dq es))

instance isStorageP_pers (SV : SnapshotM → IProp GF) (Bnd : Nat → IProp GF) (DL : Nat → IProp GF)
    (st : Storage) : Persistent (isStorageP SV Bnd DL st) := by
  unfold isStorageP; infer_instance

end rangeContract

/-! ## The snapshots' certificates as raft carries them (U8 v2; γ-free pins) -/

section certs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **The storage's snapshot `sv` is valid**, as raft carries it (persistent, γ-free): the contract's
`SV sv`, for the `SV` pinned at `sn.gsv` (the API's `snapshotValid γ`, which the node level recovers
from the pin). Replaces the certificate registry's `storCert`. -/
def svCert (sn : StorNames) (sv : SnapshotM) : IProp GF :=
  iprop(∃ (SV : SnapshotM → IProp GF), savedPredOwn sn.gsv DFrac.discard SV ∗ □ SV sv)

instance svCert_pers (sn : StorNames) (sv : SnapshotM) : Persistent (svCert (GF := GF) sn sv) := by
  unfold svCert; infer_instance

/-- (U8 v2) **A snapshot raft received is certified**, as raft carries it (persistent, γ-free): `P k`
for the predicate pinned at `sn.gk` (the cluster's certificate `raftSnapCertD γ`, which the node
level pins; `certLink`, `StepGhostMode.lean`). What the log keeps of the snapshots it may send
(`LogState.ksn`, `ownRaftLog`'s `Hkcert`): until U8 v2 they were registered in the storage's
certificate registry (`storCert`). -/
def ksnCert (sn : StorNames) (k : SnapTrip) : IProp GF :=
  iprop(∃ (P : SnapTrip → IProp GF), savedPredOwn sn.gk DFrac.discard P ∗ □ P k)

instance ksnCert_pers (sn : StorNames) (k : SnapTrip) : Persistent (ksnCert (GF := GF) sn k) := by
  unfold ksnCert; infer_instance

/-- Every snapshot of `K` certified (`ksnCert`). -/
def ksnCerts (sn : StorNames) (K : List SnapTrip) : IProp GF :=
  iprop([∗list] k ∈ K, ksnCert sn k)

instance ksnCerts_pers (sn : StorNames) (K : List SnapTrip) :
    Persistent (ksnCerts (GF := GF) sn K) := by
  unfold ksnCerts; infer_instance

theorem ksnCerts_nil (sn : StorNames) : ⊢ ksnCerts (GF := GF) sn [] := by
  unfold ksnCerts; iapply (BigSepL.bigSepL_nil (Φ := fun _ k => ksnCert (GF := GF) sn k)).2
  iempintro

theorem ksnCerts_snoc (sn : StorNames) (K : List SnapTrip) (k : SnapTrip) :
    ⊢ ksnCerts (GF := GF) sn K -∗ ksnCert sn k -∗ ksnCerts sn (K ++ [k]) := by
  unfold ksnCerts
  iintro #HK #Hk
  iapply BigSepL.bigSepL_append.2
  iframe HK
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ k => ksnCert (GF := GF) sn k)).2
  iexact Hk

theorem ksnCerts_mem (sn : StorNames) (K : List SnapTrip) (k : SnapTrip) (h : k ∈ K) :
    ⊢ ksnCerts (GF := GF) sn K -∗ ksnCert sn k := by
  unfold ksnCerts
  iintro #HK
  obtain ⟨i, hi⟩ := List.getElem?_of_mem h
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ k => ksnCert (GF := GF) sn k) hi) $$ HK

end certs

/-! ## Raft's view of its storage (U8 v2)

What raft holds of its storage, for its view `σ` (`StorState`), and the read triples of the view,
derived from the contract. Raft's ghost names (`StorNames`, the log's `LogState.sn`): the authority of
the applied lower bounds it publishes (`ga`, at `σ.fl`), of the snapshot last handed out (`gg`, at
`σ.sg`), and the pin of the contract's `SV` (`gsv`). -/

section view
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's reading of the contract's `Bnd c`: some applied lower bound or snapshot handed out at or
past `c` (the API's `nodeAppliedLb`/`snapGiven` are these lower bounds). -/
def raftBnd (sn : StorNames) (c : Nat) : IProp GF :=
  iprop(∃ (k : Nat), ⌜c ≤ k⌝ ∗ (monoNatLbOwn sn.ga k ∨ monoNatLbOwn sn.gg k))

instance raftBnd_pers (sn : StorNames) (c : Nat) : Persistent (raftBnd (GF := GF) sn c) := by
  unfold raftBnd; infer_instance


/-- (U8 v2) Raft's reading of the contract's `DL i` for a valid snapshot of term `t`: raft certified
the term `t` at `i` (`sn.gd`, whose authority keeps every key at most `committed` and of the log's
term there: `DtOk`), or `i` is strictly below a snapshot raft handed out (`sn.gg`, so below the
compaction point raft holds). -/
def raftDL (sn : StorNames) (i : Nat) (t : w64) : IProp GF :=
  iprop(i ↪[sn.gd]□ t ∨ ∃ (k : Nat), ⌜i < k⌝ ∗ monoNatLbOwn sn.gg k)

instance raftDL_pers (sn : StorNames) (i : Nat) (t : w64) : Persistent (raftDL (GF := GF) sn i t) := by
  unfold raftDL; infer_instance

/-- The contract as raft's log holds it: for some `SV` (pinned at `sn.gsv`), `Bnd` (read as
`raftBnd sn`) and `DL` (read, with a valid snapshot's term, as `raftDL sn`), `SV` persistent. What
`newLogWithSize` takes. -/
def isStorageV (sn : StorNames) (st : Storage) : IProp GF :=
  iprop(∃ (SV : SnapshotM → IProp GF) (Bnd : Nat → IProp GF) (DL : Nat → IProp GF),
    isStorageP SV Bnd DL st ∗
    savedPredOwn sn.gsv DFrac.discard SV ∗ □ (∀ (sv : SnapshotM), SV sv -∗ □ SV sv) ∗
    □ (∀ (c : Nat), Bnd c -∗ raftBnd sn c) ∗
    □ (∀ (sv : SnapshotM), SV sv -∗ DL (uint.nat sv.Metadata'.Index') ={⊤}=∗
      raftDL sn (uint.nat sv.Metadata'.Index') sv.Metadata'.Term'))

instance isStorageV_pers (sn : StorNames) (st : Storage) : Persistent (isStorageV (GF := GF) sn st) := by
  unfold isStorageV; infer_instance

/-- The authorities raft keeps for its view: of the applied lower bounds (at `fl`) and of the
snapshot handed out (at `sg`). Kept also while the ranges are lent (`lentStor`). -/
def storAuths (sn : StorNames) (σ : StorState) : IProp GF :=
  iprop(monoNatAuthOwn sn.ga 1 (uint.nat σ.fl) ∗ monoNatAuthOwn sn.gg 1 σ.sg ∗
    ghostMapAuth sn.gd 1 σ.dt)

/-- **What raft holds of its storage for its view `σ`**: the compaction point `c = prev.index`
(`storCompacted`), the frozen prefix `[c, fr]` (the dummy `e0` at `c`, of `prev`'s term: (T)), its
owned part `(fr, kOut)` of the physical log, the end unless a batch is out (P3), and its authorities.
The batch out (`pend`) is the client's to write from `kOut` on (with the end). -/
def ownStorage (sn : StorNames) (st : Storage) (σ : StorState) : IProp GF :=
  iprop(∃ (e0 : EntryM),
    storCompacted st (uint.nat σ.prev.index') ∗
    storLog st (uint.nat σ.prev.index') DFrac.discard
      (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) ∗
    storLog st (σ.fr + 1) (DFrac.own 1)
      ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (σ.fr - uint.nat σ.prev.index')) ∗
    (⌜σ.pend ≠ []⌝ ∨ storEnd st (uint.nat σ.prev.index' + 1 + σ.ents.length)) ∗
    storAuths sn σ ∗
    ⌜e0.Term' = σ.prev.term' ∧ uint.nat σ.prev.index' ≤ σ.fr ∧ σ.fr + 1 ≤ σ.kOut ∧
      σ.kOut ≤ uint.nat σ.prev.index' + 1 + σ.ents.length ∧ σ.sg ≤ uint.nat σ.prev.index'⌝)

/-- (D19i part 1; U8 v2: over `storCompacted`) The storage's compaction point has reached `n`. -/
def storCut (st : Storage) (n : Int) : IProp GF := storCompacted st n.toNat

instance storCut_pers (st : Storage) (n : Int) : Persistent (storCut (GF := GF) st n) := by
  unfold storCut; infer_instance

/-- (D19i part 1) The storage `st` is compacted at least up to `m` (persistent). -/
def storPast (st : Storage) (m : Int) : IProp GF :=
  iprop(∃ n : Int, ⌜m ≤ n⌝ ∗ storCut st n)

instance storPast_pers (st : Storage) (m : Int) : Persistent (storPast (GF := GF) st m) := by
  unfold storPast; infer_instance

theorem storPast_mono (st : Storage) (m m' : Int) (h : m' ≤ m) :
    storPast (GF := GF) st m ⊢ storPast st m' := by
  unfold storPast
  iintro ⟨%n, %hn, #H⟩
  iexists n
  iframe H
  ipureintro; omega

theorem storPast_one (st : Storage) (x : w64) :
    storPast (GF := GF) st (uint.Z x + 1) ⊢ storPast st 1 :=
  storPast_mono st _ 1 (by have := word.unsigned_range x; omega)

theorem storPast_of_cut (st : Storage) (n : Int) :
    storCut (GF := GF) st n ⊢ storPast st n := by
  unfold storPast
  iintro #H
  iexists n
  iframe H
  ipureintro; omega

/-- **The read triples of raft's view** (U8 v2: derived from the contract, `isStorage_of_V`; until
then the contract itself), against a predicate `P` of the view (`ownStorage sn st`), with the
compaction witness `CT` (`storCut st`) and the snapshot's validity `SC` (`svCert sn`). The
statements are the ones the log's proofs were written against, but for `HSnapshot` (the storage's
snapshot is now known only to be valid, at or past what raft knows is compacted) and `Hbounded`
(raft holds only what is below the batch out). -/
def isStorageWith (P : StorState → IProp GF) (CT : Int → IProp GF) (SC : SnapshotM → IProp GF)
    (st : Storage) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
  "%Hstok" ∷ ⌜st = interface.ok i⌝ ∗
  "#HLastIndex" ∷ (∀ (σ : StorState),
     {{ P σ ∗ ⌜σ.pend = []⌝ }}
       (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
     {{ (li : w64), RET (PairV #li #interface.nil);
         ⌜uint.Z li = uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
         P σ }}) ∗
  "#HFirstIndex" ∷ (∀ (σ : StorState),
     {{ P σ }}
       (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #()))
     {{ (fi : w64), RET (PairV #fi #interface.nil);
         ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z fi ∧
           uint.Z fi ≤ max (uint.Z σ.prev.index') (uint.Z σ.fl) + 1⌝ ∗
         (⌜uint.Z fi = uint.Z σ.prev.index' + 1⌝ ∨ CT (uint.Z fi - 1)) ∗
         P σ }}) ∗
  "#HTerm" ∷ (∀ (σ : StorState) (i0 : w64) (ec : GoInterface),
     {{ P σ ∗
         ⌜uint.Z σ.prev.index' ≤ uint.Z i0 ∧
            uint.Z i0 ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
         ⌜PendFrom σ (uint.Z i0 + 1)⌝ ∗
         globalAddr ErrCompacted ↦□ ec }}
       (App (Val #(methods i.ty go!"Term" i.v)) (Val #i0))
     {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
         (⌜err = interface.nil ∧ termAt σ.prev σ.ents i0 = some t⌝ ∨
          (⌜err = ec ∧ uint.Z i0 < uint.Z σ.fl⌝ ∗ CT (uint.Z i0 + 1))) ∗ P σ }}) ∗
  "#HEntries" ∷ (∀ (σ : StorState)
      (lo hi maxSize : w64) (ec : GoInterface),
     {{ P σ ∗
         ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
            uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝ ∗
         ⌜PendFrom σ (uint.Z hi)⌝ ∗
         globalAddr ErrCompacted ↦□ ec }}
       (App (App (App (Val #(methods i.ty go!"Entries" i.v)) (Val #lo)) (Val #hi))
         (Val #maxSize))
     {{ (s : GoSlice) (es : List EntryM) (err : GoInterface),
         RET (PairV #s #err);
         (⌜err = ec ∧ uint.Z lo ≤ uint.Z σ.fl⌝ ∗ CT (uint.Z lo) ∗ P σ) ∨
         (⌜err = interface.nil⌝ ∗
         entsRO s es ∗
         ⌜es ≠ [] ∧
           (es.length : Int) ≤ uint.Z hi - uint.Z lo ∧
           (∀ e, e ∈ es → e ∈ σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat) ∧
           s.cap = s.len ∧
           es <+: (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
                    (uint.Z lo - uint.Z σ.prev.index' - 1).toNat⌝ ∗
         P σ) }}) ∗
  "#Hbounded" ∷ □ (∀ (σ : StorState),
     P σ -∗
     ⌜(σ.pend = [] → uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61) ∧
       (∀ e0, σ.pend.head? = some e0 → uint.Z e0.Index' ≤ 2^61)⌝ ∗
     P σ) ∗
  "#HSnapshot" ∷ (∀ (σ : StorState) (esu : GoInterface) (n : Int),
     {{ P σ ∗
         globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu ∗
         (⌜n ≤ 0⌝ ∨ CT n) }}
       (App (Val #(methods i.ty go!"Snapshot" i.v)) (Val #()))
     {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
         P σ ∗
         (⌜err = esu⌝ ∨
          (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
           ⌜((σ.prev.index' ≠ W64 0 ∨ 1 ≤ n) → sv.Metadata'.Index' ≠ W64 0) ∧
             uint.Z σ.prev.index' ≤ uint.Z sv.Metadata'.Index' ∧
             n ≤ uint.Z sv.Metadata'.Index'⌝ ∗
           (⌜sv.Metadata'.Index' = W64 0⌝ ∨
            SC sv ∗ ⌜σ.dt.lookup (uint.nat sv.Metadata'.Index') = some sv.Metadata'.Term'⌝))) }}))

/-- The read triples of the view raft holds. -/
def isStorageD (sn : StorNames) (st : Storage) : IProp GF :=
  isStorageWith (ownStorage sn st) (storCut st) (svCert sn) st

instance isStorageWith_pers (P : StorState → IProp GF) (CT : Int → IProp GF)
    (SC : SnapshotM → IProp GF) (st : Storage) : Persistent (isStorageWith P CT SC st) := by
  unfold isStorageWith; infer_instance

instance isStorage_pers (sn : StorNames) (st : Storage) : Persistent (isStorageD (GF := GF) sn st) := by
  unfold isStorageD; infer_instance

/-! ### The client's side of the hand-outs (raft-final, 2026-10-29: moved here from
`InvStorageLaws.lean`, which is internal, so that `interface/` shows the `Ready`/`Advance`
hand-outs in `storLog`/`storEnd` terms) -/

/-- What a client holds for the entries `p` a `Ready` handed out: nothing for no entries, otherwise
the log from their first index `k` on (its current contents `old`), with the end, to write. -/
def appendRight (st : Storage) (p : List EntryM) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ (e0 : EntryM) (old : List EntryM), ⌜p.head? = some e0⌝ ∗
    storLog st (uint.nat e0.Index') (DFrac.own 1) old ∗
    storEnd st (uint.nat e0.Index' + old.length))

/-- ... and what it gives back at `Advance`: the batch written, as a frozen prefix `a` (possibly
empty) and an owned rest, with the end. -/
def appendReceipt (st : Storage) (p a : List EntryM) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ (e0 : EntryM) (b : List EntryM), ⌜p.head? = some e0 ∧ p = a ++ b⌝ ∗
    storLog st (uint.nat e0.Index') DFrac.discard a ∗
    storLog st (uint.nat e0.Index' + a.length) (DFrac.own 1) b ∗
    storEnd st (uint.nat e0.Index' + p.length))

/-- (D19i part 1; U8 v2: the authority's lower bound) The floor raft published is at least `x`:
the API's `nodeAppliedLb`. -/
def storFloor (sn : StorNames) (x : w64) : IProp GF := monoNatLbOwn sn.ga (uint.nat x)

/-- (U8 v2) A snapshot at index `k` was handed out to install: the API's `snapGiven`. -/
def storGiven (sn : StorNames) (k : Nat) : IProp GF := monoNatLbOwn sn.gg k

instance storFloor_pers (sn : StorNames) (x : w64) : Persistent (storFloor (GF := GF) sn x) := by
  unfold storFloor; infer_instance

instance storGiven_pers (sn : StorNames) (k : Nat) : Persistent (storGiven (GF := GF) sn k) := by
  unfold storGiven; infer_instance

end view

end EtcdGrove
end Perennial
