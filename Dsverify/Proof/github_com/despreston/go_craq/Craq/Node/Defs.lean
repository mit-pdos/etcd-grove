/-
The node package's internal definitions: the node invariant, the lock invariant (`n.mu`) and the
body of `isNode` (`Slots.lean`).

**Node invariant** (`nodeInv`, an Iris `inv` at `nodeN`): half of the store's contents `S`, the
node's commit log `Ln` (`nlogAuth`) with `cvOf Ln k = S.maxCommitted k`, and the items' facts
(`itemFacts`: every item is a version, `valsElem`; a committed one is committed, `cvLb`).

**Lock invariant** (`lockInv`): the role flags `IsHead`/`IsTail`, the neighbors map (each entry
none or a client of its address, `nbrOk`), the latest map `lat`, the other half of the store
(`lat k = S.maxCommitted k`), the node's role half `(IsTail, successor's address)`, and, while
`IsTail`, the tail token `tailTok L` with `lat k = cvOf L k`.

Every mutation of the store happens under the lock (the lock's half and the invariant's half
make the whole); unlocked reads use the invariant's half.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

/-- The node invariants' namespace (disjoint from `craqN`, `clientN` and the rpc model's). -/
def nodeN : Namespace := craqNodeN

/-- The latest map's value for `k` (0 if absent). -/
def latOf (lat : GMap GoString w64) (k : GoString) : w64 := (lat !! k).getD (W64 0)

/-- The neighbors map's entry at position `p` (the zero neighbor if absent). -/
def nbrAt [GooseExts] (nbrs : GMap w64 node.neighbor) (p : w64) : node.neighbor :=
  (nbrs !! p).getD (node.neighbor.mk interface.nil go!"")

/-- The successor's address. -/
def nextAddr [GooseExts] (nbrs : GMap w64 node.neighbor) : GoString := (nbrAt nbrs (W64 1)).address'

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- A neighbor entry: none (nil client, empty address), or a client of its address. -/
def nbrOk (cfg : Cfg GF) (nb : node.neighbor) : IProp GF :=
  iprop(⌜nb.rpc' = interface.nil ∧ nb.address' = go!""⌝ ∨ isNodeClient cfg nb.rpc' nb.address')

instance nbrOk_persistent (cfg : Cfg GF) (nb : node.neighbor) :
    Persistent (nbrOk (hG := hG) cfg nb) := by
  unfold nbrOk; infer_instance

/-- An item's facts: it is a version; if committed, it is committed. -/
def itemFact (γ : CraqNames) (e : GoString × w64 × GoString × Bool) : IProp GF :=
  iprop(valsElem γ e.2.1 e.1 e.2.2.1 ∗ (if e.2.2.2 then cvLb γ e.1 e.2.1 else iprop(True)))

instance itemFact_persistent (γ : CraqNames) (e : GoString × w64 × GoString × Bool) :
    Persistent (itemFact (GF := GF) γ e) := by
  unfold itemFact; split <;> infer_instance

instance itemFact_timeless (γ : CraqNames) (e : GoString × w64 × GoString × Bool) :
    Timeless (itemFact (GF := GF) γ e) := by
  unfold itemFact valsElem cvLb; split <;> infer_instance

/-- The store's items' facts. -/
def itemFacts (γ : CraqNames) (S : StoreS) : IProp GF := iprop([∗list] e ∈ S, itemFact γ e)

instance itemFacts_persistent (γ : CraqNames) (S : StoreS) :
    Persistent (itemFacts (GF := GF) γ S) := by
  unfold itemFacts; infer_instance

instance itemFacts_timeless (γ : CraqNames) (S : StoreS) :
    Timeless (itemFacts (GF := GF) γ S) := by
  unfold itemFacts; infer_instance

/-- The node invariant: half of the store, the node's commit log, the items' facts. -/
def nodeInv (cfg : Cfg GF) (a : GoString) (γs : GName) : IProp GF :=
  iprop(∃ (S : StoreS) (Ln : CLog), storeOwn γs (1 : Qp).half S ∗ nlogAuth cfg.γ a Ln ∗
    ⌜∀ k, cvOf Ln k = S.maxCommitted k⌝ ∗ itemFacts cfg.γ S)

/-- While the active tail: the tail token, whose versions are the latest map's. -/
def tailRes (cfg : Cfg GF) (t : Bool) (lat : GMap GoString w64) : IProp GF :=
  if t then iprop(∃ L : CLog, tailTok cfg.γ L ∗ ⌜∀ k, latOf lat k = cvOf L k⌝) else iprop(True)

/-- The lock's resources at given values of the protected state (all but the role). -/
def lockedState (cfg : Cfg GF) (γs : GName) (n nbM latM : Loc) (h t : Bool)
    (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS) : IProp GF :=
  iprop(structFieldRef node.Node go!"IsHead" n ↦ h ∗ structFieldRef node.Node go!"IsTail" n ↦ t ∗
    nbM ↦$ nbrs ∗ latM ↦$ lat ∗ ([∗map] _p ↦ nb ∈ nbrs, nbrOk cfg nb) ∗
    storeOwn γs (1 : Qp).half S ∗ ⌜∀ k, latOf lat k = S.maxCommitted k⌝ ∗ tailRes cfg t lat)

/-- The lock invariant of `n.mu`. -/
def lockInv (cfg : Cfg GF) (a : GoString) (γs : GName) (n nbM latM : Loc) : IProp GF :=
  iprop(∃ (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS),
    lockedState cfg γs n nbM latM h t nbrs lat S ∗ roleHalf cfg.γ a ((t, nextAddr nbrs) : Role))

/-- The node's fields and its lock and invariant (persistent), with its store's name `γs` and
its maps `nbM`, `latM`. -/
def nodeFields (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName)
    (nbM latM : Loc) : IProp GF :=
  iprop(∃ (f : GoFunc) (lg : Loc) (ch : GoChan),
    structFieldRef node.Node go!"store" n ↦□ st ∗ isStore st γs ∗
    structFieldRef node.Node go!"transport" n ↦□ f ∗ isFactory cfg f ∗
    structFieldRef node.Node go!"address" n ↦□ a ∗ structFieldRef node.Node go!"pubAddr" n ↦□ a ∗
    structFieldRef node.Node go!"cdrAddress" n ↦□ cfg.cAddr ∗
    structFieldRef node.Node go!"log" n ↦□ lg ∗
    structFieldRef node.Node go!"committed" n ↦□ ch ∗ ⌜ch = chan.nil ∧ lg ≠ null⌝ ∗
    structFieldRef node.Node go!"neighbors" n ↦□ nbM ∗
    structFieldRef node.Node go!"latest" n ↦□ latM ∗
    sync.isMutex (structFieldRef node.Node go!"mu" n) (lockInv cfg a γs n nbM latM) ∗
    inv nodeN (nodeInv cfg a γs))

instance nodeFields_persistent (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface)
    (γs : GName) (nbM latM : Loc) : Persistent (nodeFields (hG := hG) cfg n a st γs nbM latM) := by
  unfold nodeFields; infer_instance

/-- `isNode`'s body. -/
def isNodeDef (cfg : Cfg GF) (n : Loc) (a : GoString) : IProp GF :=
  iprop(∃ (st : GoInterface) (γs : GName) (nbM latM : Loc), nodeFields cfg n a st γs nbM latM)

instance isNodeDef_persistent (cfg : Cfg GF) (n : Loc) (a : GoString) :
    Persistent (isNodeDef (hG := hG) cfg n a) := by
  unfold isNodeDef; infer_instance

/-- `nodeStartRes`'s body: the unconnected coordinator client in `n.cdr`. -/
def startResDef (cfg : Cfg GF) (n : Loc) : IProp GF :=
  iprop(∃ cc : GoInterface, structFieldRef node.Node go!"cdr" n ↦□ cc ∗ freshCoordClient cfg cc)

end defs

end NodeP

end github_com.despreston.go_craq

end Perennial
