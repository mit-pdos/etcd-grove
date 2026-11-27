/-
The coordinator package's definitions: the replicas as the coordinator's lock sees them, the lock
invariant (`coordLock`), and the persistent facts about the coordinator (`coordDef`, the body of
the sealed slot `isCoord`).

**Replicas.** `rs : List Rep`: per replica its node pointer, address and `connected` flag. Each
replica's node struct has `address ↦□` and `rpc ↦□` a client of its address (`nodeFacts`); the
lock owns its `connected` field and, while it is connected, the coordinator's half of its role:
the last replica is the active tail with no successor, the others are not the tail and record
their successor's address, unless that successor is disconnected (`nextOk`: a node is activated
only as the new last after its successor, the removed tail, was fenced, which needs the
successor connected).

**Chain addresses.** Per chain address: its join ticket (it announced itself), or, for an address
not among the replicas, its role half `(false, "")` (never joined). So an `AddNode` (which brings
the address's ticket) finds the address's role half, and the replicas' addresses stay distinct.
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

/-- A replica as the coordinator's lock sees it: its node pointer, address and `connected`
flag. -/
structure Rep where
  loc : Loc
  addr : GoString
  conn : Bool

/-- The successor's address `x` that replica `i` records is right: none for the last; the next
replica's address, if that one is connected. -/
def nextOk (rs : List Rep) (i : Nat) (x : GoString) : Prop :=
  (i + 1 = rs.length → x = go!"") ∧
  ∀ r', rs[i + 1]? = some r' → r'.conn = true → x = r'.addr

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- Node struct `n` (persistent): its address `a` and a client of `a`. -/
def nodeFacts (cfg : Cfg GF) (n : Loc) (a : GoString) : IProp GF :=
  iprop(structFieldRef coordinator.node go!"address" n ↦□ a ∗
    ∃ c : GoInterface, structFieldRef coordinator.node go!"rpc" n ↦□ c ∗ isNodeClient cfg c a)

instance nodeFacts_persistent (cfg : Cfg GF) (n : Loc) (a : GoString) :
    Persistent (nodeFacts (hG := hG) cfg n a) := by
  unfold nodeFacts; infer_instance

/-- Replica `i`'s role resource: while connected, the coordinator's half of its role. -/
def roleRes (cfg : Cfg GF) (rs : List Rep) (i : Nat) (r : Rep) : IProp GF :=
  if r.conn then iprop(∃ x : GoString, roleHalf cfg.γ r.addr (decide (i + 1 = rs.length), x) ∗
    ⌜nextOk rs i x⌝)
  else iprop(True)

/-- Replica `i`'s resources in the lock (besides its node facts): its `connected` field and
role half. -/
def connRole (cfg : Cfg GF) (rs : List Rep) (i : Nat) (r : Rep) : IProp GF :=
  iprop(structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗ roleRes cfg rs i r)

/-- A chain address: joined (its ticket), or not a replica with its role half
`(false, "")`. -/
def joinRes (cfg : Cfg GF) (rs : List Rep) (a : GoString) : IProp GF :=
  iprop(joinTicket cfg.γ a ∨ (⌜a ∉ rs.map Rep.addr⌝ ∗ roleHalf cfg.γ a ((false, go!"") : Role)))

/-- The pure facts of the replicas: distinct chain addresses. -/
def repsWf (cfg : Cfg GF) (rs : List Rep) : Prop :=
  (rs.map Rep.addr).Nodup ∧ ∀ r ∈ rs, r.addr ∈ cfg.chain

/-- The coordinator's lock invariant (`cdr.mu`). -/
def coordLock (cfg : Cfg GF) (c : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (rs : List Rep) (ver : w64) (hd tl : Loc),
    "Hreplicas" ∷ structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
    "Hsl" ∷ sl ↦* rs.map Rep.loc ∗
    "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
    "Hversion" ∷ structFieldRef coordinator.Coordinator go!"version" c ↦ ver ∗
    "Hnext" ∷ nextHalf cfg.γ ver ∗
    "Hhead" ∷ structFieldRef coordinator.Coordinator go!"head" c ↦ hd ∗
    "Htail" ∷ structFieldRef coordinator.Coordinator go!"tail" c ↦ tl ∗
    "%Hwf" ∷ ⌜repsWf cfg rs⌝ ∗
    "#Hnfs" ∷ ([∗list] r ∈ rs, nodeFacts cfg r.loc r.addr) ∗
    "Hreps" ∷ ([∗list] i ↦ r ∈ rs, connRole cfg rs i r) ∗
    "Hjoin" ∷ ([∗list] a ∈ cfg.chain, joinRes cfg rs a) ∗
    "Htok" ∷ (if rs = [] then tailTok cfg.γ [] else iprop(True)))

/-- The coordinator `c` (persistent). -/
def coordDef (cfg : Cfg GF) (c : Loc) : IProp GF :=
  iprop(⌜cfg.chain.length < 2 ^ 31 - 1⌝ ∗
    ∃ f : GoFunc, structFieldRef coordinator.Coordinator go!"tport" c ↦□ f ∗ isFactory cfg f ∗
    sync.isMutex (structFieldRef coordinator.Coordinator go!"mu" c) (coordLock cfg c))

instance coordDef_persistent (cfg : Cfg GF) (c : Loc) :
    Persistent (coordDef (hG := hG) cfg c) := by
  unfold coordDef; infer_instance

end defs

end github_com.despreston.go_craq

end Perennial
