/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/iface/Stores.lean (241f27e).
-/
/-
Interface (redesign R1, session 2): the contracts between `raft` and the stores it is given
(`LogStore`, `StableStore`, `SnapshotStore` interface values), and the relation between Go `Log`
values and the protocol model's entries.

`raft`'s proofs use these contracts; `InmemStore` (the stable store, and the inner store of hr3's
`checkedStore`), `InmemSnapshotStore` and hr3's `checkedStore` prove them.

* The log store's contents are a list of entries (Raft index `k` at position `k-1`). Reads and
  writes are logically atomic: the caller supplies an atomic update of the store's abstract state
  (`own L`, the client's half), committed at the store's linearization point. Writes are appends at
  the end and truncations of a suffix, as raft does them. A write takes, for the duration of the
  call, a fraction of the server's durable-prefix view (`gprot.durView`) showing that it writes
  past the durable prefix: hr3's `checkedStore` checks exactly this before writing (log safety).
* (hraft_robust L0) The stable store is TaDa too, and every atomic update is a crash-token update
  (`|NC=`); writes lend the client's window resource `W` to the store until their commit point (see
  `isLogStore`). (Was: owned by one goroutine, plain specs.)
* The snapshot store has no snapshots: `List` returns none (snapshots are out of scope).
* Reads take a `sync.RWMutex` read lock, so they take the calling thread's quarter token `rtok tid` (a reader
  token is borrowed from a quarter thread pool for the critical section: `Threads/QPool.lean`, D15)
  and give it back.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Install
public import Perennial.Proof.io
public import Dsverify.Proof.github_com.hashicorp.raft.Base
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QTok

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-! ## The stores' namespace and writes (hraft_robust R3, REQUESTS.md Q1/Q2) -/

/-- (hraft_robust, R3 Q1) **The stores' namespace**: the contracts' atomic updates run at `⊤ ∖ ↑storeN`, so
that a durable store may keep its crash invariant (under `storeN`) open while it commits the client's update
(the disk: after `durable.Write` returns, taking the window resource out of its invariant in the same step).
A client's invariants avoid it (raft's are under `nroot.@"raft"`). -/
def storeN : Namespace := nroot .@ "hraftstore"

/-- (hraft_robust, R3 Q2) **A write of the log store**: `StoreLogs`/`StoreLog` of `es` at `first..`, and
`DeleteRange(mn, mx)`. The index of the client's window family (`isLogStore`'s `Wl`). -/
inductive LogOp where
  | store (first : Nat) (es : RLog)
  | del (mn mx : Nat)

/-- (hraft_robust, R3 Q2) **A write of the stable store**: `SetUint64(key, v)`, `Set(key, vb)`. The index of
the client's window family (`isStableStore`'s `Ws`). -/
inductive StableOp where
  | setU (key : List w8) (v : w64)
  | set (key vb : List w8)

/-! ## Log values -/

/-- The Go `Log` value `lv` is the protocol entry `e` at Raft index `k`: index, term and type
match, and its data bytes are `e.data` (read-only forever); `Extensions` is some read-only byte
slice (copied by the transport); `AppendedAt` is not looked at. -/
def logIs (lv : Log) (k : Nat) (e : Entry) : IProp GF :=
  iprop(⌜uint.nat lv.Index' = k ∧ uint.nat lv.Term' = e.term ∧ uint.nat lv.Type' = e.kind⌝ ∗
    lv.Data' ↦*□ e.data ∗ ∃ x : List w8, lv.Extensions' ↦*□ x)

instance logIs_persistent lv k e : Persistent (logIs (GF := GF) lv k e) := by
  unfold logIs; infer_instance

/-- A pointer to a log entry that is never written again (stored, sent, applied). -/
def logPtr (l : Loc) (k : Nat) (e : Entry) : IProp GF :=
  iprop(∃ lv : Log, l ↦□ lv ∗ logIs lv k e)

instance logPtr_persistent l k e : Persistent (logPtr (GF := GF) l k e) := by
  unfold logPtr; infer_instance

/-! ## The log store (stage 3: a partial map) -/

/-- (stage 3) **The log store's abstract state**: the entries it holds, a partial map from Raft
indexes (compaction deletes a prefix, an install's discard everything: no longer a list), and the
value `LastIndex` returns (`hi`: the last index written, as upstream's `LogStore` documents; after a
deletion it is some value, which raft uses only for `shouldSnapshot`'s threshold). -/
structure LogAbs where
  m : GMap Nat Entry
  hi : w64
  /-- (hraft_robust L0) the commit index staged for the next `StoreLogs` (`StageCommitIndex`; a
  store that is not a `CommitTrackingLogStore` never changes it). Volatile: a crash resets it. -/
  staged : w64
  /-- (hraft_robust L0) the commit index written with the last `StoreLogs` (`GetCommitIndex`
  returns it, capped at `hi`). Durable. -/
  ci : w64

/-- `m` with the entries `es` inserted at `first, first+1, …`. -/
def LogAbs.ins (m : GMap Nat Entry) (first : Nat) : RLog → GMap Nat Entry
  | [] => m
  | e :: es => LogAbs.ins (m.insert first e) (first + 1) es

/-- `m` without the entries at `mn..mx`. -/
def LogAbs.del (m : GMap Nat Entry) (mn mx : Nat) : GMap Nat Entry :=
  GMap.filter (fun k _ => decide (¬ (mn ≤ k ∧ k ≤ mx))) m

/-- The empty store (`NewInmemStore`). -/
def LogAbs.empty : LogAbs := ⟨∅, W64 0, W64 0, W64 0⟩

/-- The store after `StoreLogs` of `es` at `first..` (`hi`: the larger of the old one and the last
index written). -/
def LogAbs.store (A : LogAbs) (first : Nat) (es : RLog) : LogAbs :=
  ⟨LogAbs.ins A.m first es,
    if es = [] then A.hi else
      (if uint.nat A.hi < first + es.length - 1 then W64 (first + es.length - 1) else A.hi),
    A.staged, A.staged⟩

/-- (hraft_robust L0) The store after `DeleteRange(mn, mx)`, with the new `LastIndex` value `hi'`
(some value: the contract lets the store choose it). -/
def LogAbs.delete (A : LogAbs) (mn mx : Nat) (hi' : w64) : LogAbs :=
  { A with m := LogAbs.del A.m mn mx, hi := hi' }

/-- (hraft_robust L0) What `GetCommitIndex` returns: the written commit index, at most `hi`. -/
def LogAbs.readCi (A : LogAbs) : w64 := if uint.nat A.hi < uint.nat A.ci then A.hi else A.ci

instance logAbs_countable : Pos.Countable LogAbs :=
  Pos.Countable.ofInjective (fun A => Pos.Countable.encode (A.m, A.hi, A.staged, A.ci))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1; subst h2; subst h3; subst h4; rfl)

/-- What `GetLog(idx, ptr)` leaves, for store contents `m`: the entry copied into `*ptr` and a nil
error, or (no entry at `idx`) a non-nil error, the value of a raft error variable (both stores return
`ErrLogNotFound`). -/
def getLogPost (ptr : Loc) (idx : Nat) (m : GMap Nat Entry) (err : GoInterface) : IProp GF :=
  match m.lookup idx with
  | some e => iprop(⌜err = interface.nil⌝ ∗ ∃ lv : Log, ptr ↦ lv ∗ logIs lv idx e)
  | none => iprop(⌜err ≠ interface.nil⌝ ∗ (∃ c, isRaftErr c err) ∗ ∃ lv : Log, ptr ↦ lv)

/-- **The log store contract** of the interface value `x`, whose abstract state the client owns
through `own` (exclusive, one owner; stage 3: a partial map with the last index written, `LogAbs`).
Every operation is logically atomic (the caller's atomic update is committed at the store's
linearization point) and returns a nil error; reads take the calling thread's quarter token.
(Stage 3: the writes no longer take `durView`/`llogIdx`: they were for hr3's `checkedStore`, which
`Main` no longer uses.)

(hraft_robust L0, R1 §2.1) **Crash-aware form.** Every atomic update is a crash-token update
(`|NC={⊤ \ ↑storeN,∅}=>`, R3 Q1: the stores' namespace left out): the client may open invariants shared
with later generations (`srvDurInv`). A write `op` also takes the client's **window resource** `Wl op`
(R3 Q2: a family fixed with the store, indexed by the write, so that a crash lemma can give back a
resource the client recognizes), which it hands to the atomic update at its commit point (the disk:
once `durable.Write` returns); from its file's rename until then the store holds it, and its crash
lemma gives it back if the new contents survived (so the client can fire, at the crash, the step it
would have fired at the commit). A store without a window (`InmemStore`) passes it on at once. The written commit index (`CommitTrackingLogStore`,
`StageCommitIndex`/`GetCommitIndex`) is in `LogAbs` (`staged`, `ci`); when `x`'s dynamic type is a
`CommitTrackingLogStore`, its two methods are specified too. -/
def isLogStore (x : GoInterfaceOk) (own : LogAbs → IProp GF) (Wl : LogOp → IProp GF) : IProp GF :=
  iprop(
    -- `LastIndex()`: `hi`, atomically
    □ (∀ (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (own A ={∅,⊤ \ ↑storeN}=∗ (rtok tid -∗ Φ (PairV #A.hi #interface.nil)))) -∗
        WP (App (Val #(methods x.ty go!"LastIndex" x.v)) (Val #())) {{ Φ }}) ∗
    -- `FirstIndex()`: some index, no error (raft uses it only as the start of a compaction)
    □ (∀ (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗ (∀ r : w64, rtok tid -∗ Φ (PairV #r #interface.nil)) -∗
        WP (App (Val #(methods x.ty go!"FirstIndex" x.v)) (Val #())) {{ Φ }}) ∗
    -- `GetLog(idx, ptr)`: a copy of the entry at `idx`, or `ErrLogNotFound`, atomically
    □ (∀ (idx : w64) (ptr : Loc) (lv0 : Log) (tid : Nat) (Φ : val → IProp GF),
        ptr ↦ lv0 -∗ rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (own A ={∅,⊤ \ ↑storeN}=∗ ∀ err : GoInterface, getLogPost ptr (uint.nat idx) A.m err -∗
            rtok tid -∗ Φ #err)) -∗
        WP (App (App (Val #(methods x.ty go!"GetLog" x.v)) (Val #idx)) (Val #ptr)) {{ Φ }}) ∗
    -- `StoreLogs(sl)`: insert the entries `es` (pointed to by `ptrs`, at indexes `first..`), and
    -- write the staged commit index; committed (durable) at the atomic update, `W` lent till then
    □ (∀ (sl : GoSlice) (dq : DFrac) (ptrs : List Loc) (first : Nat) (es : RLog)
          (Φ : val → IProp GF),
        ⌜ptrs.length = es.length ∧ first + es.length < 2 ^ 64⌝ -∗
        sl ↦*{dq} ptrs -∗
        ([∗list] k ↦ p ∈ ptrs, ∃ e, ⌜es[k]? = some e⌝ ∗ logPtr p (first + k) e) -∗
        Wl (.store first es) -∗
        (Wl (.store first es) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (own (A.store first es) ={∅,⊤ \ ↑storeN}=∗ (sl ↦*{dq} ptrs -∗ Φ #interface.nil))) -∗
        WP (App (Val #(methods x.ty go!"StoreLogs" x.v)) (Val #sl)) {{ Φ }}) ∗
    -- `StoreLog(l)`: the same for one entry
    □ (∀ (p : Loc) (first : Nat) (e : Entry) (Φ : val → IProp GF),
        ⌜first < 2 ^ 64⌝ -∗ logPtr p first e -∗ Wl (.store first [e]) -∗
        (Wl (.store first [e]) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (own (A.store first [e]) ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
        WP (App (Val #(methods x.ty go!"StoreLog" x.v)) (Val #p)) {{ Φ }}) ∗
    -- `DeleteRange(mn, mx)`: delete the entries at `mn..mx` (none if `mx < mn`); `LastIndex` is some
    -- value afterwards. (`mx < 2^64 - 1`: InmemStore's loop `j <= max` would not end.)
    □ (∀ (mn mx : w64) (Φ : val → IProp GF),
        ⌜uint.nat mx < 2 ^ 64 - 1⌝ -∗ Wl (.del (uint.nat mn) (uint.nat mx)) -∗
        (Wl (.del (uint.nat mn) (uint.nat mx)) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (∀ hi' : w64, own (A.delete (uint.nat mn) (uint.nat mx) hi')
            ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
        WP (App (App (Val #(methods x.ty go!"DeleteRange" x.v)) (Val #mn)) (Val #mx)) {{ Φ }}) ∗
    -- (hraft_robust L0) commit tracking: either the dynamic type is not a `CommitTrackingLogStore`,
    -- or `StageCommitIndex(idx)` sets `staged` (volatile, no window) and `GetCommitIndex()` returns
    -- the written index capped at `hi` (`readCi`), both atomically
    (⌜go.typeSetContains x.ty CommitTrackingLogStore.ty = false⌝ ∨
      ⌜go.typeSetContains x.ty CommitTrackingLogStore.ty = true⌝ ∗
      □ (∀ (idx : w64) (Φ : val → IProp GF),
          (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗ (own { A with staged := idx } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
          WP (App (Val #(methods x.ty go!"StageCommitIndex" x.v)) (Val #idx)) {{ Φ }}) ∗
      □ (∀ (tid : Nat) (Φ : val → IProp GF),
          rtok tid -∗
          (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
            (own A ={∅,⊤ \ ↑storeN}=∗ (rtok tid -∗ Φ (PairV #A.readCi #interface.nil)))) -∗
          WP (App (Val #(methods x.ty go!"GetCommitIndex" x.v)) (Val #())) {{ Φ }})) ∗
    -- (hraft_robust, R5 Q2) `FirstIndex()` atomically: `0` only for an empty store, and at most every
    -- stored index (fix 2 of `NewRaft` compares it with the snapshot's index)
    □ (∀ (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, own A ∗
          (own A ={∅,⊤ \ ↑storeN}=∗ ∀ r : w64,
            ⌜(uint.nat r = 0 → A.m = ∅) ∧ (∀ k e, A.m.lookup k = some e → uint.nat r ≤ k)⌝ -∗
            rtok tid -∗ Φ (PairV #r #interface.nil))) -∗
        WP (App (Val #(methods x.ty go!"FirstIndex" x.v)) (Val #())) {{ Φ }}))

instance isLogStore_persistent x own Wl : Persistent (isLogStore (GF := GF) x own Wl) := by
  unfold isLogStore; infer_instance

/-! ## The stable store -/

/-- The stable store's abstract contents: the `uint64` keys and the byte-slice keys. -/
structure StableAbs where
  ints : GMap (List w8) w64
  bytes : GMap (List w8) (List w8)

/-- (hraft_robust L0: moved from `InmemStoreBase`, raft's crash state keeps a ghost view of it) -/
instance stableAbs_countable : Pos.Countable StableAbs :=
  Pos.Countable.ofInjective
    (fun s => Pos.Countable.encode (s.ints, s.bytes))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; rfl)

/-- The error `errors.New("not found")` (what `Get` of a missing key returns; raft compares its
`Error()` with `"not found"`). -/
def isNotFoundErr (err : GoInterface) : IProp GF :=
  iprop(∃ p : Loc, ⌜err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #p⌝ ∗
    p ↦□ (errors.errorString.mk go!"not found"))

/-- **The stable store contract** of `x`, whose abstract contents the client owns through `own`.
Keys and values are read-only byte slices; reads take the thread's token. (Revised: `Get` returns any
stored value, an empty non-nil slice included.)

(hraft_robust L0, R1 §2.1) **TaDa, crash-aware**, as the log store's (`isLogStore`): every operation
is logically atomic, its atomic update a crash-token update; a write is committed (durable) at its
atomic update and lends the client's window resource `Ws op` (R3 Q2) to the store until then. (Was: owned by one
goroutine, plain specs, which pin no commit point for a crash.) -/
def isStableStore (x : GoInterfaceOk) (own : StableAbs → IProp GF) (Ws : StableOp → IProp GF) :
    IProp GF :=
  iprop(
    □ (∀ (key : GoSlice) (kb : List w8) (tid : Nat) (Φ : val → IProp GF),
        key ↦*□ kb -∗ rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, own st ∗
          (own st ={∅,⊤ \ ↑storeN}=∗ rtok tid -∗ Φ (PairV #((st.ints.lookup kb).getD (W64 0)) #interface.nil))) -∗
        WP (App (Val #(methods x.ty go!"GetUint64" x.v)) (Val #key)) {{ Φ }}) ∗
    □ (∀ (key : GoSlice) (kb : List w8) (v : w64) (Φ : val → IProp GF),
        key ↦*□ kb -∗ Ws (.setU kb v) -∗
        (Ws (.setU kb v) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, own st ∗
          (own { st with ints := st.ints.insert kb v } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
        WP (App (App (Val #(methods x.ty go!"SetUint64" x.v)) (Val #key)) (Val #v)) {{ Φ }}) ∗
    □ (∀ (key : GoSlice) (kb : List w8) (tid : Nat) (Φ : val → IProp GF),
        key ↦*□ kb -∗ rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, own st ∗
          (own st ={∅,⊤ \ ↑storeN}=∗ rtok tid -∗
            ((∀ vb, ⌜st.bytes.lookup kb = some vb⌝ -∗
                ∀ s : GoSlice, s ↦*□ vb -∗ Φ (PairV #s #interface.nil)) ∧
             (⌜∀ vb, st.bytes.lookup kb = some vb → vb = []⌝ -∗
                ∀ err : GoInterface, isNotFoundErr err -∗
                  Φ (PairV #(Perennial.zero_val GoSlice) #err))))) -∗
        WP (App (Val #(methods x.ty go!"Get" x.v)) (Val #key)) {{ Φ }}) ∗
    □ (∀ (key vs : GoSlice) (kb vb : List w8) (Φ : val → IProp GF),
        key ↦*□ kb -∗ vs ↦*□ vb -∗ Ws (.set kb vb) -∗
        (Ws (.set kb vb) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, own st ∗
          (own { st with bytes := st.bytes.insert kb vb } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
        WP (App (App (Val #(methods x.ty go!"Set" x.v)) (Val #key)) (Val #vs)) {{ Φ }}))

instance isStableStore_persistent x own Ws : Persistent (isStableStore (GF := GF) x own Ws) := by
  unfold isStableStore; infer_instance

/-! ## Byte streams (stage 3) -/

/-- (stage 3) **A reader of the byte stream `R` describes that never fails** (`R cs`: the bytes still
to come are `cs`; `eof`: the value of `io.EOF`): `Read(p)` on a non-empty `p` moves the stream's first
`n` bytes into `p` and returns `(n, nil)`, or returns `(n, eof)` having moved the rest of the stream
(nothing left after it). `io.streamReader`'s behaviour with its error restricted to `nil` and
`io.EOF` (what lets raft's restore and the transport's `ReadAll` refute their error branches). -/
def streamReaderOk (src : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (buf cs : List w8) (Φ : val → IProp GF), ⌜0 < buf.length⌝ -∗
    R cs -∗ p ↦* buf -∗
    (∀ (n : w64) (err : GoInterface),
      ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ buf.length ∧ sint.nat n ≤ cs.length ∧
        (err = interface.nil ∨ (err = eof ∧ sint.nat n = cs.length))⌝ -∗
      p ↦* (cs.take (sint.nat n) ++ buf.drop (sint.nat n)) -∗ R (cs.drop (sint.nat n)) -∗
      Φ (PairV #n #err)) -∗
    WP (App (Val #(methods src.ty go!"Read" src.v)) (Val #p)) {{ Φ }})

instance streamReaderOk_persistent src R eof : Persistent (streamReaderOk (GF := GF) src R eof) := by
  unfold streamReaderOk; infer_instance

/-- (stage 3) **A reader that never fails, with a `Close`** (an `io.ReadCloser`: the snapshot store's
`Open` result, which raft hands to the FSM's `Restore`): `Close()` returns nil. -/
def readCloserOk (src : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface) : IProp GF :=
  iprop(streamReaderOk src R eof ∗
    □ (∀ Φ : val → IProp GF, Φ #interface.nil -∗
        WP (App (Val #(methods src.ty go!"Close" src.v)) (Val #())) {{ Φ }}))

instance readCloserOk_persistent src R eof : Persistent (readCloserOk (GF := GF) src R eof) := by
  unfold readCloserOk; infer_instance

/-! ## The snapshot store -/

/-- (stage 2; since stage 3 only `InmemSnapshotStore`'s, which `Main` no longer uses) **The empty
snapshot store contract**: there are no snapshots (`List` returns an empty list, no error; it takes and
gives back the thread's token). -/
def isSnapshotStore (x : GoInterfaceOk) : IProp GF :=
  iprop(
    □ (∀ (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗
        (∀ s : GoSlice, s ↦* ([] : List Loc) -∗ rtok tid -∗ Φ (PairV #s #interface.nil)) -∗
        WP (App (Val #(methods x.ty go!"List" x.v)) (Val #())) {{ Φ }}))

instance isSnapshotStore_persistent x : Persistent (isSnapshotStore (GF := GF) x) := by
  unfold isSnapshotStore; infer_instance

/-! ## The snapshot store (stage 3: `examples/snapstore`) -/

/-- (stage 3) The snapshot store's abstract state: its latest closed snapshot, if any (metadata, as
`List`/`Open` return it, and bytes). -/
abbrev SnapLatest : Type := Option (SnapshotMeta × List w8)

/-- (hraft_robust: moved from `examples/snapstore/Base`; raft pins its latest snapshot at boot) -/
instance snapshotMeta_countable : Pos.Countable SnapshotMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.Version', m.ID', m.Index', m.Term', m.Peers',
      m.Configuration'.Servers', m.ConfigurationIndex', m.Size'))
    (by
      intro a b h
      have h := Pos.encode_inj h
      obtain ⟨a1, a2, a3, a4, a5, ⟨a6⟩, a7, a8⟩ := a
      obtain ⟨b1, b2, b3, b4, b5, ⟨b6⟩, b7, b8⟩ := b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7 h8; rfl)

/-- (stage 3) **The order of snapshots** (upstream `FileSnapshotStore`'s: by term, then index): a
snapshot `(m, b)` closed into a store whose latest is `old` becomes the latest unless `old` is newer
(a strictly larger term, or the same term and a larger index). -/
def newerSnap (old : SnapLatest) (m : SnapshotMeta) (b : List w8) : SnapLatest :=
  match old with
  | none => some (m, b)
  | some (m0, b0) =>
    if uint.nat m0.Term' < uint.nat m.Term' ∨
        (uint.nat m0.Term' = uint.nat m.Term' ∧ uint.nat m0.Index' ≤ uint.nat m.Index')
    then some (m, b) else some (m0, b0)

/-- (stage 3) **A snapshot sink** (`SnapshotSink` interface value `k` with id `id`, from the store's
`Create`): its owner's state `own (some bs)` (open, `bs` written so far) or `own none` (closed or
cancelled). `Write(p)` appends all of `p` and returns `(len p, nil)` while open; `Close()` of an open
sink, given the close obligation `Q bs` for the bytes written, runs the commit fixed for this sink at
`Create` (review T1-5: for this sink's id; hraft_robust L0: a crash-token update, `Q bs` being the
window resource a durable store holds from its file's rename to its sync) and returns nil with the commit's result `R bs`, and is a
no-op returning nil once closed; `Cancel()` drops the sink and returns nil; `ID()` returns `id`. Its
dynamic type is not an `io.ReaderFrom` (so `io.Copy` into it writes with `Write`: the install's copy
of the snapshot stream). -/
def isSink (k : GoInterfaceOk) (id : GoString) (own : Option (List w8) → IProp GF)
    (Q R : List w8 → IProp GF) : IProp GF :=
  iprop(
    ⌜go.typeSetContains k.ty io.ReaderFrom.ty = false⌝ ∗
    □ (∀ (p : GoSlice) (dq : DFrac) (bs c : List w8) (Φ : val → IProp GF),
        own (some bs) -∗ p ↦*{dq} c -∗
        (own (some (bs ++ c)) -∗ p ↦*{dq} c -∗ Φ (PairV #(W64 c.length) #interface.nil)) -∗
        WP (App (Val #(methods k.ty go!"Write" k.v)) (Val #p)) {{ Φ }}) ∗
    □ (∀ (bs : List w8) (Φ : val → IProp GF),
        own (some bs) -∗ Q bs -∗ (own none -∗ R bs -∗ Φ #interface.nil) -∗
        WP (App (Val #(methods k.ty go!"Close" k.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (Φ : val → IProp GF),
        own none -∗ (own none -∗ Φ #interface.nil) -∗
        WP (App (Val #(methods k.ty go!"Close" k.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (o : Option (List w8)) (Φ : val → IProp GF),
        own o -∗ (own none -∗ Φ #interface.nil) -∗
        WP (App (Val #(methods k.ty go!"Cancel" k.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (Φ : val → IProp GF), Φ #id -∗
        WP (App (Val #(methods k.ty go!"ID" k.v)) (Val #())) {{ Φ }}))

instance isSink_persistent k id own Q R : Persistent (isSink (GF := GF) k id own Q R) := by
  unfold isSink; infer_instance

/-- (stage 3) The metadata a sink of `Create(ver, idx, term, cfg, cfgIdx, _)` with id `id` closes with
`bs`: `Size = |bs|`, no `Peers`. -/
def sinkMeta (ver idx term cfgIdx : w64) (cfg : Configuration) (id : GoString) (bs : List w8) :
    SnapshotMeta :=
  SnapshotMeta.mk ver id idx term slice.nil cfg cfgIdx (W64 bs.length)

/-- (stage 3) What `Open(id)` returns for the latest `old`: the latest's metadata and a reader over a
copy of its bytes if its id is `id`, an error otherwise. -/
def openPost (old : SnapLatest) (id : GoString) (eof : GoInterface) (v : val) : IProp GF :=
  match old with
  | some (m, b) =>
    if m.ID' = id then
      iprop(∃ (mp : Loc) (rd : GoInterfaceOk) (R : List w8 → IProp GF),
        ⌜v = PairV (PairV #mp #(GoInterface.ok rd)) #interface.nil⌝ ∗ mp ↦ m ∗
        readCloserOk rd R eof ∗ R b ∗ ⌜go.typeSetContains rd.ty io.WriterTo.ty = false⌝)
    else iprop(∃ err : GoInterface, ⌜v = PairV (PairV #null #interface.nil) #err ∧ err ≠ interface.nil⌝)
  | none => iprop(∃ err : GoInterface, ⌜v = PairV (PairV #null #interface.nil) #err ∧ err ≠ interface.nil⌝)

/-- (stage 3) **The snapshot store contract** of `x` (`examples/snapstore`, upstream
`FileSnapshotStore`'s semantics with one retained snapshot), whose abstract state (the latest closed
snapshot, `SnapLatest`) the client owns through `own` (TaDa: the client keeps its own invariant
about it). Every call returns a nil error except `Open` of a snapshot that is no longer the latest.
* `Create(version, index, term, cfg, cfgIdx, trans)`: a fresh sink `k` with its id `id`; the caller
  then fixes, for this id, the commit (an atomic update that makes the
  latest `newerSnap old (sinkMeta … id bs) bs`) and the commit's result `R` (review T1-5: the id the
  commit uses is the sink's `ID()`; `Close` returns `R`; (SNAP-2) the commit receives the bound of the
  bytes, `|bs| < 2^63`, which the store has from its Go slice), and gets the sink, open and empty;
  (hraft_robust R3 Q2) its close obligation is the store's window family at the sink's metadata,
  `Qc (sinkMeta … id bs) bs` (fixed with the store, so that its crash lemma gives back a resource the
  client recognizes);
* `List()`: the latest's metadata (a slice of 0 or 1 pointers), atomically;
* `Open(id)`: atomically, the latest's metadata and a reader over a copy of its bytes if its id is
  `id` (`readCloserOk`, with `io.EOF`'s value `eof`), otherwise an error (`openPost`). -/
def isSnapStore (x : GoInterfaceOk) (own : SnapLatest → IProp GF) (eof : GoInterface)
    (Qc : SnapshotMeta → List w8 → IProp GF) : IProp GF :=
  iprop(
    □ (∀ (ver idx term cfgIdx : w64) (cfg : Configuration) (trans : GoInterface) (Φ : val → IProp GF),
        (∀ (k : GoInterfaceOk) (id : GoString),
          (∀ (R : List w8 → IProp GF),
            (∀ (bs : List w8), ⌜bs.length < 2 ^ 63⌝ -∗ Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, own old ∗
              (own (newerSnap old (sinkMeta ver idx term cfgIdx cfg id bs) bs) ={∅,⊤ \ ↑storeN}=∗ R bs)) -∗
            |==> ∃ own' : Option (List w8) → IProp GF,
              isSink k id own' (fun bs => Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs) R ∗
              own' (some [])) -∗
          Φ (PairV #(GoInterface.ok k) #interface.nil)) -∗
        WP (App (App (App (App (App (App (Val #(methods x.ty go!"Create" x.v)) (Val #ver))
          (Val #idx)) (Val #term)) (Val #cfg)) (Val #cfgIdx)) (Val #trans)) {{ Φ }}) ∗
    □ (∀ (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, own old ∗
          (own old ={∅,⊤ \ ↑storeN}=∗ ∀ (sl : GoSlice) (ps : List Loc),
            sl ↦* ps -∗
            (match old with
              | none => ⌜ps = []⌝
              | some (m, _) => ∃ p : Loc, ⌜ps = [p]⌝ ∗ p ↦ m) -∗
            rtok tid -∗ Φ (PairV #sl #interface.nil))) -∗
        WP (App (Val #(methods x.ty go!"List" x.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (id : GoString) (tid : Nat) (Φ : val → IProp GF),
        rtok tid -∗
        (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, own old ∗
          (own old ={∅,⊤ \ ↑storeN}=∗ ∀ v : val, openPost old id eof v -∗ rtok tid -∗ Φ v)) -∗
        WP (App (Val #(methods x.ty go!"Open" x.v)) (Val #id)) {{ Φ }}))

instance isSnapStore_persistent x own eof Qc : Persistent (isSnapStore (GF := GF) x own eof Qc) := by
  unfold isSnapStore; infer_instance

end contracts

end github_com.hashicorp.raft

end Perennial
