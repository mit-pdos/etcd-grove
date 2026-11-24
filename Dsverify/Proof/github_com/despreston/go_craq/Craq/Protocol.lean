/-
The CRAQ protocol's ghost state, invariant and laws (stage 1 interface; `notes/stage1-plan.md`).

Everything here is stated over the global ghost state (`[G : GooseGlobalGS …]`): the node proofs
reach it through `HeapGS.goose_globalGS`, the start (`Top.lean`) allocates it.

**The abstract state.** `ownState γ σ` (the client spec's `own_state`) is half of a ghost
variable holding the list of linearized puts, newest first (`kvOfPuts`); the invariant holds the
other half.

**Versions and records.** The coordinator assigns versions 1, 2, … (`nextHalf γ n`: the last
assigned; its half and the invariant's). Version `v`'s record (`recs`, a ghost map, persistent
elements) holds its key, its value, the name of its receipt (`post`, a saved proposition) and of
its collection token (`col`). `valsElem γ v k x`: version `v` is the write of `x` to `k`
(persistent; unique per version).

**Commits.** The commit log `L` (mono-list of `(k, v)`, appended by the tail) gives each key's
committed version `cvOf L k` (0: none). Half of its authority is the **tail token**
`tailTok γ L`: whoever holds it commits; the invariant holds the other half. `cvLb γ k v`
(persistent): `cvOf ≥ v` from some point on.

**Linearization.** A client operation's update `opAU γ i Φ` is remote's linearization point
(`remote.lin`, a fancy update from `clientMask = ⊤ ∖ craqEop`; notes/dsv-craq.md, P1; the lab's
was an Iris atomic update at `clientN`). A put's update is deposited at assignment (`assign`) and
fired by the tail's commit of any version `≥` its own (`commit`: every assigned version of the key in
`(cvOf L k, v]` in order, the prefix); its receipt waits in the record for the coordinator's
`ticket` (`collect`). A get is linearized at the tail (`read`).

**Nodes.** Per chain address `a`: `roleHalf γ a r` (the node's role as last told by the
coordinator: `(active tail?, successor's address)`, halves with the node and the coordinator),
`nlog` (the node's commit log; `covers γ a L`: node `a`'s committed versions cover `cvOf L`, for
good), `joinTicket γ a`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Wire
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- The key-value map's inputs. -/
inductive KvInput where
  | get (k : GoString)
  | put (k x : GoString)
deriving DecidableEq

/-- Its outputs (`got none`: the key was never written). -/
inductive KvOutput where
  | got (v : Option GoString)
  | done
deriving DecidableEq

/-! The model: a key-value map of strings, from the empty map (the lab's `kv GoString GoString`). -/
namespace KvM
abbrev State := GoString → Option GoString
abbrev Input := KvInput
abbrev Output := KvOutput
def init : State := fun _ => none
/-- The step as a function: the state after `i` and its output. -/
def stepF (i : Input) (s : State) : State × Output :=
  match i with
  | .get k => (s, .got (s k))
  | .put k x => ((fun k' => if k' = k then some x else s k'), .done)
/-- The step as a relation (the lab's). -/
def step (s : State) (i : Input) (s' : State) (o : Output) : Prop := stepF i s = (s', o)
end KvM

/-- The state after the puts `l` (newest first). -/
def kvOfPuts (l : List (GoString × GoString)) : KvM.State :=
  fun k => (l.find? (fun e => decide (e.1 = k))).map (·.2)

/-- A commit log: `(key, version)` pairs. -/
abbrev CLog := List (GoString × w64)

/-- The highest version of `k` in the log (0 if none). -/
def cvOf (L : CLog) (k : GoString) : w64 :=
  L.foldl (fun m e => if e.1 = k ∧ uint.Z m < uint.Z e.2 then e.2 else m) (W64 0)

/-- A version's record: key, value, receipt's saved proposition, collection token. -/
abbrev RecInfo := GoString × GoString × GName × GName

namespace RecInfo
abbrev key (r : RecInfo) : GoString := r.1
abbrev val (r : RecInfo) : GoString := r.2.1
abbrev post (r : RecInfo) : GName := r.2.2.1
abbrev col (r : RecInfo) : GName := r.2.2.2
end RecInfo

/-- The value of `k` after the commits `L` with the records `R` (none if not committed). -/
def absOf (L : CLog) (R : GMap w64 RecInfo) (k : GoString) : Option GoString :=
  if cvOf L k = W64 0 then none else (R.lookup (cvOf L k)).map RecInfo.val

/-- The invariant's pure part. -/
def craqWf (l : List (GoString × GoString)) (L : CLog) (n : w64) (R : GMap w64 RecInfo) : Prop :=
  (∀ v : w64, (R.lookup v).isSome ↔ (1 ≤ uint.Z v ∧ uint.Z v ≤ uint.Z n)) ∧
  (∀ k, kvOfPuts l k = absOf L R k) ∧
  (∀ k, cvOf L k ≠ W64 0 → ∃ ri, R.lookup (cvOf L k) = some ri ∧ ri.key = k) ∧
  (∀ v ri, R.lookup v = some ri → kvOk ri.key ri.val)

/-- The ghost names of a run. -/
structure CraqNames where
  abs : GName
  cv : GName
  next : GName
  recs : GName
  role : GoString → GName
  nlog : GoString → GName
  join : GoString → GName

/-- The protocol's invariant's namespace (disjoint from the rpc model's). -/
def craqN : Namespace := ndot nroot "craq"

/-- The node invariants' namespace (`NodeP.nodeN`). -/
def craqNodeN : Namespace := ndot nroot "craq_node"

/-- The invariants a linearization point may have open: the protocol's and the nodes'
(`remote.RBase.Eop`). -/
def craqEop : CoPset := ↑craqN ∪ ↑craqNodeN

/-- The mask of a client operation's update (the lab's `↑clientN`). -/
def clientMask : CoPset := ⊤ \ craqEop

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The client spec's `own_state`: the abstract state (half of the puts' ghost variable). -/
def ownState (γ : CraqNames) (σ : KvM.State) : IProp GF :=
  iprop(∃ l : List (GoString × GoString), ⌜σ = kvOfPuts l⌝ ∗ ghostVar γ.abs (1 : Qp).half l)

/-- A client operation's update: remote's linearization point (`remote.lin`, one-shot), from
`clientMask`, for the caller's postcondition `Q` of the output. -/
def opAU (γ : CraqNames) (i : KvM.Input) (Q : KvM.Output → IProp GF) : IProp GF :=
  iprop(|={clientMask, ∅}=> ∃ σ, ownState γ σ ∗
    (ownState γ (KvM.stepF i σ).1 ={∅, clientMask}=∗ Q (KvM.stepF i σ).2))

/-- A put's receipt: its update's postcondition (a put's output is `done`). -/
def putReceipt (_k _x : GoString) (Q : KvM.Output → IProp GF) : IProp GF := Q .done

/-- A record's resources: once committed, its receipt (or, once collected, the token); before,
the put's atomic update. -/
def recRes (γ : CraqNames) (ri : RecInfo) (done : Bool) : IProp GF :=
  if done then iprop(∃ P : IProp GF, savedPropOwn ri.post .discard P ∗ (P ∨ token ri.col))
  else iprop(∃ Q : KvM.Output → IProp GF,
    savedPropOwn ri.post .discard (putReceipt ri.key ri.val Q) ∗
    opAU γ (.put ri.key ri.val) Q)

/-- The protocol's invariant. -/
def craqInv (γ : CraqNames) : IProp GF :=
  iprop(∃ (l : List (GoString × GoString)) (L : CLog) (n : w64) (R : GMap w64 RecInfo),
    ghostVar γ.abs (1 : Qp).half l ∗ monoListAuthOwn γ.cv (1 : Qp).half L ∗
    ghostVar γ.next (1 : Qp).half n ∗ ghostMapAuth γ.recs 1 R ∗ ⌜craqWf l L n R⌝ ∗
    ([∗map] v ↦ ri ∈ R, ghostMapElem γ.recs v .discard ri) ∗
    [∗map] v ↦ ri ∈ R, recRes γ ri (decide (uint.Z v ≤ uint.Z (cvOf L ri.key))))

/-- The invariant is allocated (persistent). -/
def isCraq (γ : CraqNames) : IProp GF := inv craqN (craqInv γ)

/-- The tail token: half of the commit log's authority. -/
def tailTok (γ : CraqNames) (L : CLog) : IProp GF := monoListAuthOwn γ.cv (1 : Qp).half L

/-- `k`'s committed version is at least `v` (persistent). -/
def cvLb (γ : CraqNames) (k : GoString) (v : w64) : IProp GF :=
  iprop(⌜v = W64 0⌝ ∨ ∃ L : CLog, monoListLbOwn γ.cv L ∗ ⌜uint.Z v ≤ uint.Z (cvOf L k)⌝)

/-- Version `v` is the write of `x` to `k`, a put the protocol handles (persistent). -/
def valsElem (γ : CraqNames) (v : w64) (k x : GoString) : IProp GF :=
  iprop(⌜kvOk k x⌝ ∗ ∃ p c : GName, ghostMapElem γ.recs v .discard ((k, x, p, c) : RecInfo))

/-- The coordinator's half of the last assigned version. -/
def nextHalf (γ : CraqNames) (n : w64) : IProp GF := ghostVar γ.next (1 : Qp).half n

/-- The right to collect version `v`'s receipt, for the update's postcondition `Q`. -/
def ticket (γ : CraqNames) (v : w64) (k x : GoString)
    (Q : KvM.Output → IProp GF) : IProp GF :=
  iprop(∃ p c : GName, ghostMapElem γ.recs v .discard ((k, x, p, c) : RecInfo) ∗
    savedPropOwn p .discard (putReceipt k x Q) ∗ token c)

/-- What a get at the tail tells about the value it read: version `v` is `k`'s committed one,
and the get returned `r`. -/
def readFacts (γ : CraqNames) (k : GoString) (v : w64) (r : Option GoString) : IProp GF :=
  iprop(⌜v = W64 0 ↔ r = none⌝ ∗ ∀ x, ⌜r = some x⌝ -∗ valsElem γ v k x)

/-! ### Per node -/

/-- The role values: (the active tail?, the successor's address). -/
abbrev Role := Bool × GoString

/-- Node `a`'s role as the coordinator last told it (halves: the node and the coordinator). -/
def roleHalf (γ : CraqNames) (a : GoString) (r : Role) : IProp GF :=
  ghostVar (γ.role a) (1 : Qp).half r

/-- Node `a`'s committed versions cover `cvOf L`, for good (persistent). -/
def covers (γ : CraqNames) (a : GoString) (L : CLog) : IProp GF :=
  iprop(∃ L' : CLog, monoListLbOwn (γ.nlog a) L' ∗ ⌜∀ k, uint.Z (cvOf L k) ≤ uint.Z (cvOf L' k)⌝)

/-- Node `a`'s commit log (its authority; the node's). -/
def nlogAuth (γ : CraqNames) (a : GoString) (L : CLog) : IProp GF := monoListAuthOwn (γ.nlog a) 1 L

/-- Node `a` may join once. -/
def joinTicket (γ : CraqNames) (a : GoString) : IProp GF := token (γ.join a)

instance isCraq_persistent (γ : CraqNames) : Persistent (isCraq (GF := GF) γ) := by
  unfold isCraq; infer_instance
instance cvLb_persistent (γ : CraqNames) (k : GoString) (v : w64) :
    Persistent (cvLb (GF := GF) γ k v) := by unfold cvLb; infer_instance
instance valsElem_persistent (γ : CraqNames) (v : w64) (k x : GoString) :
    Persistent (valsElem (GF := GF) γ v k x) := by unfold valsElem; infer_instance

theorem valsElem_kvOk (γ : CraqNames) (v : w64) (k x : GoString) :
    valsElem (GF := GF) γ v k x ⊢ ⌜kvOk k x⌝ := by
  unfold valsElem; iintro ⟨%h, -⟩; ipureintro; exact h
instance readFacts_persistent (γ : CraqNames) (k : GoString) (v : w64) (r : Option GoString) :
    Persistent (readFacts (GF := GF) γ k v r) := by unfold readFacts; infer_instance
instance covers_persistent (γ : CraqNames) (a : GoString) (L : CLog) :
    Persistent (covers (GF := GF) γ a L) := by unfold covers; infer_instance
instance ownState_timeless (γ : CraqNames) (σ : KvM.State) :
    Timeless (ownState (GF := GF) γ σ) := by unfold ownState; infer_instance

end defs

/-! ## Laws (the protocol's API; proved in `Protocol/Laws.lean`) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The start: the invariant, the client's half of the abstract state (empty), the tail token
(no commit), the coordinator's half of the version counter (none assigned), and per chain
address both halves of its role (not the tail, no successor), its empty commit log and its join
ticket. -/
abbrev craq_alloc.spec : Prop :=
  ∀ (ads : List GoString) (hads : ads.Nodup),
    ⊢@{IProp GF} |={⊤}=> ∃ γ : CraqNames, isCraq γ ∗ ownState γ KvM.init ∗ tailTok γ [] ∗
      nextHalf γ (W64 0) ∗
      ([∗list] a ∈ ads, roleHalf γ a ((false, go!"") : Role) ∗
        roleHalf γ a ((false, go!"") : Role) ∗ nlogAuth γ a [] ∗ joinTicket γ a)

/-- A tail token's log bounds every `cvLb`. -/
abbrev tailTok_cvLb.spec : Prop :=
  ∀ (γ : CraqNames) (L : CLog) (k : GoString) (v : w64),
    tailTok (GF := GF) γ L ∗ cvLb γ k v ⊢ ⌜uint.Z v ≤ uint.Z (cvOf L k)⌝

/-- The tail token's committed versions are committed. -/
abbrev tailTok_lb.spec : Prop :=
  ∀ (γ : CraqNames) (L : CLog) (k : GoString),
    tailTok (GF := GF) γ L ⊢ tailTok γ L ∗ cvLb γ k (cvOf L k)

abbrev cvLb_zero.spec : Prop :=
  ∀ (γ : CraqNames) (k : GoString),
    ⊢ cvLb (GF := GF) γ k (W64 0)

abbrev cvLb_mono.spec : Prop :=
  ∀ (γ : CraqNames) (k : GoString) (v v' : w64) (h : uint.Z v' ≤ uint.Z v),
    cvLb (GF := GF) γ k v ⊢ cvLb γ k v'

/-- A version is one write. -/
abbrev valsElem_agree.spec : Prop :=
  ∀ (γ : CraqNames) (v : w64) (k x k' x' : GoString),
    valsElem (GF := GF) γ v k x ∗ valsElem γ v k' x' ⊢ ⌜k = k' ∧ x = x'⌝

/-- Versions start at 1. -/
abbrev valsElem_pos.spec : Prop :=
  ∀ (γ : CraqNames) (E : CoPset) (_hE : ↑craqN ⊆ E) (v : w64) (k x : GoString),
    isCraq (GF := GF) γ ∗ valsElem γ v k x ={E}=∗ ⌜1 ≤ uint.Z v⌝

/-- Nothing is committed in the empty log: every node covers it. -/
abbrev covers_nil.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString), ⊢ |==> covers (GF := GF) γ a []

/-- The coordinator assigns the next version to a put, depositing its atomic update. -/
abbrev assign.spec : Prop :=
  ∀ (γ : CraqNames) (E : CoPset) (hE : ↑craqN ⊆ E) (n : w64)
    (hn : uint.Z n < 2 ^ 64 - 1) (k x : GoString) (hkx : kvOk k x)
    (Q : KvM.Output → IProp GF),
    isCraq (GF := GF) γ ∗ nextHalf γ n ∗ opAU γ (.put k x) Q ={E}=∗
      nextHalf γ (n + W64 1) ∗ valsElem γ (n + W64 1) k x ∗ ticket γ (n + W64 1) k x Q

/-- The coordinator collects a committed put's receipt. -/
abbrev collect.spec : Prop :=
  ∀ (γ : CraqNames) (E : CoPset) (hE : ↑craqN ⊆ E) (v : w64) (k x : GoString)
    (Q : KvM.Output → IProp GF),
    isCraq (GF := GF) γ ∗ ticket γ v k x Q ∗ cvLb γ k v ∗ £ 2 ={E}=∗ putReceipt k x Q

/-- The tail commits version `v` of `k`: if it is newer than `k`'s committed version, every
assigned version of `k` up to it is linearized, in order. -/
abbrev commit.spec : Prop :=
  ∀ (γ : CraqNames) (E : CoPset) (_hE : ↑craqN ∪ clientMask ⊆ E) (L : CLog) (v : w64) (k x : GoString),
    isCraq (GF := GF) γ ∗ tailTok γ L ∗ valsElem γ v k x ∗ £ 1 ={E}=∗
      tailTok γ (if uint.Z (cvOf L k) < uint.Z v then L ++ [(k, v)] else L)

/-- The log after a commit. -/
abbrev cvOf_commit.spec : Prop :=
  ∀ (L : CLog) (k k' : GoString) (v : w64),
    cvOf (if uint.Z (cvOf L k) < uint.Z v then L ++ [(k, v)] else L) k' =
      if k' = k ∧ uint.Z (cvOf L k) < uint.Z v then v else cvOf L k'

/-- The tail linearizes a get of `k`: it returns `k`'s committed version's value. -/
abbrev read.spec : Prop :=
  ∀ (γ : CraqNames) (E : CoPset) (_hE : ↑craqN ∪ clientMask ⊆ E) (L : CLog) (k : GoString)
    (Q : KvM.Output → IProp GF),
    isCraq (GF := GF) γ ∗ tailTok γ L ∗ opAU γ (.get k) Q ∗ £ 1 ={E}=∗
      tailTok γ L ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗ readFacts γ k (cvOf L k) (σ k)

/-! ### Per node -/

/-- The two halves of a role agree. -/
abbrev roleHalf_agree.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (r r' : Role),
    roleHalf (GF := GF) γ a r ∗ roleHalf γ a r' ⊢ ⌜r = r'⌝

/-- Both halves change the role. -/
abbrev roleHalf_update.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (r r' r'' : Role),
    roleHalf (GF := GF) γ a r ∗ roleHalf γ a r' ==∗ roleHalf γ a r'' ∗ roleHalf γ a r''

/-- A node's commit log covers itself. -/
abbrev nlog_covers.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (Ln : CLog),
    nlogAuth (GF := GF) γ a Ln ⊢ nlogAuth γ a Ln ∗ covers γ a Ln

/-- What a node's log covers, its current log covers. -/
abbrev nlog_covers_le.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (Ln L : CLog),
    nlogAuth (GF := GF) γ a Ln ∗ covers γ a L ⊢ ⌜∀ k, uint.Z (cvOf L k) ≤ uint.Z (cvOf Ln k)⌝

/-- A node logs a commit. -/
abbrev nlog_append.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (Ln : CLog) (k : GoString) (v : w64),
    nlogAuth (GF := GF) γ a Ln ==∗ nlogAuth γ a (Ln ++ [(k, v)])

/-- Covering a log covers every log below it. -/
abbrev covers_mono.spec : Prop :=
  ∀ (γ : CraqNames) (a : GoString) (L L' : CLog),
    (∀ k, uint.Z (cvOf L' k) ≤ uint.Z (cvOf L k)) → covers (GF := GF) γ a L ⊢ covers γ a L'

/-- A log's versions after appending one. -/
abbrev cvOf_append.spec : Prop :=
  ∀ (L : CLog) (k k' : GoString) (v : w64),
    cvOf (L ++ [(k, v)]) k' =
      if k' = k ∧ uint.Z (cvOf L k) < uint.Z v then v else cvOf L k'

end laws

end github_com.despreston.go_craq

end Perennial
