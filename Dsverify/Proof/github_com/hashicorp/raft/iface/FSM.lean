/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/iface/FSM.lean (241f27e).
-/
/-
Interface (redesign R1): the contract between `raft` and the user's `FSM` (hr3's `*store`).

`raft`'s FSM goroutine (`runFSM`) calls `Apply(l)` on each committed command, in increasing
index order, never twice for one index, after the server committed it (`durLb γ i k`, and the
entry is the committed log's, `CIdx γ k e`). It passes, for every index it skipped since the
previous call, the fact that the committed entry there is no command. The FSM's state is the
client's `fsmOwn k0` (`k0`: the index of the last command applied, `0` before the first); the
response `r` of the command at `k` satisfies the client's persistent `respP k r`, which `raft`
hands to whoever submitted the command (the future's `Error()`/`Response()`).

(Stage 3) `Snapshot` and `Restore` are called: the FSM goroutine snapshots its state at its
position `s` when the snapshot goroutine asks (`fsmSnapshotCh`), and restores a snapshot an install
received (`fsmMutateCh`'s restore futures); the client's persistent `snapP s b` says what the
snapshot bytes `b` mean. `raft` never asks for `BatchingFSM` (the proof of `runFSM` shows the type
assertion fails from the client's dynamic type, a fact the client provides: `fsmNotBatching`).

(Stage 4) If the client's dynamic type is a `ConfigurationStore` (hr3's store is), `runFSM` calls
`StoreConfiguration(index, c)` on each committed configuration entry, in index order with the commands,
with the decoded configuration; the FSM's state (`fsmOwn k0`, the last command) does not change.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

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

/-- The committed entries at the indexes strictly between `k0` and `k` are no commands. -/
def noCmdBetween (γ : GNames) (k0 k : Nat) : IProp GF :=
  iprop([∗list] x ∈ List.range' (k0 + 1) (k - (k0 + 1)),
    ∃ e' : Entry, CIdx γ x e' ∗ ⌜e'.kind ≠ kCommand⌝)

instance noCmdBetween_persistent γ k0 k : Persistent (noCmdBetween (GF := GF) γ k0 k) := by
  unfold noCmdBetween; infer_instance

/-- (stage 3) **An `FSMSnapshot` value** `snap` of the FSM's state at index `s` (what `Snapshot()`
returns): `Persist(sink)`, on any goroutine (concurrently with `Apply`), given a sink (`isSink`,
open and empty) whose close obligation `Q` accepts every snapshot of `s` (`snapP s b`), writes some
`b` with `snapP s b`, closes the sink and returns nil with the commit's result `R b` (hraft_robust R4b:
the own snapshot's commit returns the latest's index lower bound `latLb`, for the compaction); `Release()` returns. -/
def fsmSnapOk (snap : GoInterfaceOk) (snapP : Nat → List w8 → IProp GF) (s : Nat) : IProp GF :=
  iprop(
    □ (∀ (k : GoInterfaceOk) (id : GoString) (own : Option (List w8) → IProp GF)
          (Q R : List w8 → IProp GF) (Φ : val → IProp GF),
        isSink k id own Q R -∗ □ (∀ b, snapP s b -∗ Q b) -∗ own (some []) -∗
        (own none -∗ (∃ b, R b) -∗ Φ #interface.nil) -∗
        WP (App (Val #(methods snap.ty go!"Persist" snap.v)) (Val #(GoInterface.ok k))) {{ Φ }}) ∗
    □ (∀ (Φ : val → IProp GF), Φ #() -∗
        WP (App (Val #(methods snap.ty go!"Release" snap.v)) (Val #())) {{ Φ }}))

instance fsmSnapOk_persistent snap snapP s : Persistent (fsmSnapOk (GF := GF) snap snapP s) := by
  unfold fsmSnapOk; infer_instance

/-- **The FSM contract** of the interface value `x`, the FSM of server `i` in protocol `γ`. The
client's state `fsmOwn k0` (exclusive) tracks the index of the last applied command; `respP k r`
(persistent, see `isFSM_respP_persistent`) is what the response `r` of the command at index `k`
means; (stage 3) `snapP s b` (persistent) is what it means for the bytes `b` to be a snapshot of the
committed log up to `s` (the client's; the same for every server: snapshots travel between them).
* `Apply(l)`: the committed command `e` at `k`, the next command after `k0`, handed to the FSM
  (durable at `i`, `durLb γ i k`);
* (stage 3) `Snapshot()`: the FSM's state at `s` (its last command at `k0 ≤ s`, no command in
  `(k0, s]`) as an `FSMSnapshot` (`fsmSnapOk … s`), never an error;
* (stage 3) `Restore(rc)`: from a reader that never fails (`readCloserOk`) of a snapshot `b` of
  `s` (`snapP s b`), past the FSM's last command (`k0 ≤ s`: raft's restore moves the FSM forward,
  fix `db9dde4`; hr3's ghost index of the last command applied is monotone), the FSM's state becomes the snapshot's (its last command at some `k0' ≤ s`, no
  command in `(k0', s]`), and it returns nil. -/
def isFSM (x : GoInterfaceOk) (γ : GNames) (i : SID) (fsmOwn : Nat → IProp GF)
    (respP : Nat → GoInterface → IProp GF) (snapP : Nat → List w8 → IProp GF) : IProp GF :=
  iprop(
    -- the responses' and snapshots' meanings are persistent
    □ (∀ (k : Nat) (r : GoInterface), respP k r -∗ □ respP k r) ∗
    □ (∀ (s : Nat) (b : List w8), snapP s b -∗ □ snapP s b) ∗
    -- `Apply(l)`: the committed command `e` at index `k`, the next command after `k0`
    □ (∀ (l : Loc) (k0 k : Nat) (e : Entry) (Φ : val → IProp GF),
        fsmOwn k0 -∗ logPtr l k e -∗ ⌜k0 < k ∧ e.kind = kCommand⌝ -∗ CIdx γ k e -∗
        durLb γ i k -∗ noCmdBetween γ k0 k -∗
        (∀ r : GoInterface, fsmOwn k -∗ respP k r -∗ Φ #r) -∗
        WP (App (Val #(methods x.ty go!"Apply" x.v)) (Val #l)) {{ Φ }}) ∗
    -- `Snapshot()`: the state at `s`
    □ (∀ (k0 s : Nat) (r : GoInterface) (Φ : val → IProp GF),
        fsmOwn k0 -∗ ⌜k0 ≤ s⌝ -∗ noCmdBetween γ k0 (s + 1) -∗ (⌜k0 = 0⌝ ∨ respP k0 r) -∗
        (∀ snap : GoInterfaceOk, fsmOwn k0 -∗ fsmSnapOk snap snapP s -∗
          Φ (PairV #(GoInterface.ok snap) #interface.nil)) -∗
        WP (App (Val #(methods x.ty go!"Snapshot" x.v)) (Val #())) {{ Φ }}) ∗
    -- `Restore(rc)`: from a snapshot of `s`
    □ (∀ (k0 s : Nat) (rd : GoInterfaceOk) (R : List w8 → IProp GF) (b : List w8)
          (eof : GoInterface) (Φ : val → IProp GF),
        fsmOwn k0 -∗ ⌜k0 ≤ s⌝ -∗ globalAddr io.EOF ↦□ eof -∗ readCloserOk rd R eof -∗ R b -∗
        snapP s b -∗
        (∀ (k0' : Nat) (r : GoInterface), fsmOwn k0' -∗ ⌜k0' ≤ s⌝ -∗ noCmdBetween γ k0' (s + 1) -∗
          (⌜k0' = 0⌝ ∨ respP k0' r) -∗ Φ #interface.nil) -∗
        WP (App (Val #(methods x.ty go!"Restore" x.v)) (Val #(GoInterface.ok rd))) {{ Φ }}) ∗
    -- (stage 4) `StoreConfiguration(index, c)`, if the FSM is a `ConfigurationStore`: the committed
    -- configuration entry `e` at `k` past the last command `k0`, `c` its decoded servers (owned)
    □ (⌜go.typeSetContains x.ty ConfigurationStore.ty = true⌝ →
       ∀ (k0 k : Nat) (e : Entry) (c : Configuration) (ss : List Server) (Φ : val → IProp GF),
        fsmOwn k0 -∗ ⌜k0 < k ∧ e.kind = kConfig ∧ e.data = encodeServers ss ∧ srvsOk γ ss⌝ -∗
        CIdx γ k e -∗ durLb γ i k -∗ c.Servers' ↦* ss -∗
        (fsmOwn k0 -∗ Φ #()) -∗
        WP (App (App (Val #(methods x.ty go!"StoreConfiguration" x.v)) (Val #(W64 k))) (Val #c))
          {{ Φ }}))

instance isFSM_persistent x γ i fsmOwn respP snapP :
    Persistent (isFSM (GF := GF) x γ i fsmOwn respP snapP) := by
  unfold isFSM; infer_instance

/-- The FSM's dynamic type does not implement `BatchingFSM` (so `runFSM`'s type assertion fails): a
fact about the client's type. (Stage 4, REPL4-1: it implements `ConfigurationStore`, `isFSM`'s
`StoreConfiguration` row; stage 3: it implemented neither.) -/
def fsmNotBatching [GoLocalContext] [GoSemanticsFunctions] (x : GoInterfaceOk) : Prop :=
  go.typeSetContains x.ty BatchingFSM.ty = false ∧ go.typeSetContains x.ty ConfigurationStore.ty = true

theorem isFSM_respP_persistent (x : GoInterfaceOk) (γ : GNames) (i : SID)
    (fsmOwn : Nat → IProp GF) (respP : Nat → GoInterface → IProp GF)
    (snapP : Nat → List w8 → IProp GF) (k : Nat) (r : GoInterface) :
    isFSM x γ i fsmOwn respP snapP ∗ respP k r ⊢ □ respP k r := by
  unfold isFSM
  iintro ⟨⟨#Hp, -⟩, Hr⟩
  iapply Hp $$ %k %r Hr

/-- (stage 3) The snapshots' meaning is persistent. -/
theorem isFSM_snapP_persistent (x : GoInterfaceOk) (γ : GNames) (i : SID)
    (fsmOwn : Nat → IProp GF) (respP : Nat → GoInterface → IProp GF)
    (snapP : Nat → List w8 → IProp GF) (s : Nat) (b : List w8) :
    isFSM x γ i fsmOwn respP snapP ∗ snapP s b ⊢ □ snapP s b := by
  unfold isFSM
  iintro ⟨⟨-, #Hp, -⟩, Hr⟩
  iapply Hp $$ %s %b Hr

/-- (stage 2) **The FSM had processed index `s`** (persistent; the FSM's read side, raft ↔ client):
the last command the FSM goroutine applied was at `k0 ≤ s` (`0`: none) with response `r`
(`respP k0 r`), no committed command lies in `(k0, s]`, and `s` is in server `i`'s durable prefix.
raft's FSM goroutine gives it when it answers a barrier (after processing the barrier's batch:
`s` is the barrier's index) or a verify future (`s`: the end of the batches it processed before);
the client (hr3) reads its FSM's state afterwards and finds there at least the commands `1..s` of
the committed log (its `respP` says what the FSM had applied at `k0`). -/
def fsmAt (γ : GNames) (respP : Nat → GoInterface → IProp GF) (i : SID) (s : Nat) : IProp GF :=
  iprop(∃ (k0 : Nat) (r : GoInterface), (⌜k0 = 0⌝ ∨ respP k0 r) ∗ ⌜k0 ≤ s⌝ ∗
    noCmdBetween γ k0 (s + 1) ∗ durLb γ i s)

/-- (stage 2, law E) **Introducing `fsmAt`**: the last command applied at `k0 ≤ s` (`0`: none) with
its response, no command in `(k0, s]`, `s` durable at `i`. -/
theorem fsmAt_intro (γ : GNames) (respP : Nat → GoInterface → IProp GF) (i : SID) (k0 s : Nat)
    (r : GoInterface) (h : k0 ≤ s) :
    (⌜k0 = 0⌝ ∨ respP k0 r) ∗ noCmdBetween γ k0 (s + 1) ∗ durLb γ i s ⊢ fsmAt γ respP i s := by
  unfold fsmAt
  iintro ⟨Hr, #Hnc, #Hd⟩
  iexists k0, r
  iframe Hr
  isplitr
  · ipureintro; exact h
  iframe #

/-- (stage 2, law E) **Eliminating `fsmAt`** (the client's read side). -/
theorem fsmAt_elim (γ : GNames) (respP : Nat → GoInterface → IProp GF) (i : SID) (s : Nat) :
    fsmAt γ respP i s ⊢ ∃ (k0 : Nat) (r : GoInterface), (⌜k0 = 0⌝ ∨ respP k0 r) ∗ ⌜k0 ≤ s⌝ ∗
      noCmdBetween γ k0 (s + 1) ∗ durLb γ i s := by
  unfold fsmAt
  iintro H
  iexact H

end contracts

end github_com.hashicorp.raft

end Perennial
