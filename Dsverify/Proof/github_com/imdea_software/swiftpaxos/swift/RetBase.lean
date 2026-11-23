/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RetBase.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The returned-rows store's leaf definitions** (notes/lifecycle-plan.md "Revision 5", R5.0 1;
notes/lifecycle-table.md revision 5, §3.7-§3.9). They sit below `DescNode.lean`, whose node
invariant `swift.nodeInvD` holds the store (D32 (a), D34's G-led), so that the store's records can
name the descriptor's fields and facts without an import cycle (check 4, D2).

* Moved here from `Deliver.lean` (same names): the descriptor's values `swift.DescV`, the
  execution record's entries `swift.ExE`, `exAt`/`exLb`/`exIn`; from `SyncStepD.lean`:
  `swift.rvSync`.
* The descriptor's protocol facts, over `N r` (not the descriptor context, which is defined
  later): `rowPhaseOk` (pure), `phaseWhy`, `depWhy` (G-ldr, D33's `execW`), `stopFacts`.
* The store's kinds: a stored token's record `RecK` (`empty`, `sync`, `exec`, `rest d γi`,
  `released`) and a claim's kind `ClK` (`fresh`, `sync`, `rest d γi`; table rev 5, C2), with
  `recOf`; why a token is in the store, `retWhy`; the claims `claimTok` and the ledger's
  receipts `outRcpt` (C1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ShInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeaf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

/-- An executed command: its id, command, and the dependencies it was executed after. -/
abbrev swift.ExE := swift.CommandId × sp.Cmd × List swift.CommandId

/-- The descriptor's fields `deliver` uses (Go values; `c` the model's command, `vs` its value
slice, `D` the dependencies of `dep`, `Hs` the hashes of `hs`). -/
structure swift.DescV where
  phase : w64
  c : sp.Cmd
  vs : GoSlice
  dep : GoSlice
  D : List swift.CommandId
  hs : GoSlice
  Hs : List swift.SHash
  propose : Loc
  seq : Bool
  msgs : Loc

/-- A command's rows at the replica in a ballot: pre-acceptance, path, accepted, committed. -/
abbrev swift.RowV := Option (List sp.CmdId) × Option (List sp.CmdId) × Bool × Bool

def swift.rowEmpty : swift.RowV := (none, none, false, false)

/-- The rows a sync entry's token is installed with (`MSync`'s commands are accepted). -/
def swift.rvSync : swift.RowV := (none, none, true, false)

/-- **The phase and the rows agree** (table rev 4/5 §3.7; PF13b, PF13c, E7): see the table. -/
def swift.rowPhaseOk (N r b : Nat) (dv : swift.DescV) (rv : swift.RowV) : Prop :=
  (dv.propose = null → (dv.phase = W64 0 ∨ dv.phase = W64 3) ∧ dv.D = []) ∧
  (dv.propose ≠ null →
    uint.nat dv.phase ≤ 3 ∧
    (dv.phase = W64 0 → dv.D = [] ∧ r ≠ sp.leaderOf N b) ∧
    (dv.phase = W64 1 → rv.1 = some (dv.D.map toCmdId)) ∧
    (dv.phase = W64 2 → rv.2.2.1 = true) ∧
    (rv.1.isSome → 1 ≤ uint.nat dv.phase) ∧
    (rv.2.2.1 = true ∨ rv.2.2.2 = true →
      2 ≤ uint.nat dv.phase ∨ (r = sp.leaderOf N b ∧ 1 ≤ uint.nat dv.phase)))

/-- A stored token's record (table rev 5, C2). -/
inductive swift.RecK where
  | empty
  | sync
  | exec
  | rest (d : Loc) (γi : GName)
  | released
  deriving DecidableEq

/-- A claim's kind: what record it claims (table rev 5, C2). -/
inductive swift.ClK where
  | fresh
  | sync
  | rest (d : Loc) (γi : GName)
  deriving DecidableEq

/-- The record a claim of kind `ck` claims. -/
def swift.recOf : swift.ClK → swift.RecK
  | .fresh => .empty
  | .sync => .sync
  | .rest d γi => .rest d γi

def swift.RecK.enc : swift.RecK → Nat ⊕ (Loc × GName)
  | .empty => .inl 0
  | .sync => .inl 1
  | .exec => .inl 2
  | .released => .inl 3
  | .rest d γi => .inr (d, γi)

instance swift.RecK.countable : Pos.Countable swift.RecK :=
  .ofInjective (fun k => Pos.Countable.encode k.enc)
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [swift.RecK.enc])

def swift.ClK.enc : swift.ClK → Nat ⊕ (Loc × GName)
  | .fresh => .inl 0
  | .sync => .inl 1
  | .rest d γi => .inr (d, γi)

instance swift.ClK.countable : Pos.Countable swift.ClK :=
  .ofInjective (fun k => Pos.Countable.encode k.enc)
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [swift.ClK.enc])

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-! ## The execution record's persistent facts (moved from Deliver.lean) -/

/-- Entry `i` of the execution record of epoch `b` is `e` (persistent). -/
def swift.exAt (γxm : GName) (b i : Nat) (e : swift.ExE) : IProp netDistGF :=
  ghostMapElem γxm (b, i) DFrac.discard e

/-- The execution record of epoch `b` starts with `X` (persistent). -/
def swift.exLb (γxm : GName) (b : Nat) (X : List swift.ExE) : IProp netDistGF :=
  iprop([∗list] i ↦ e ∈ X, swift.exAt γxm b i e)

/-- `x` was executed in epoch `b` (persistent): what a retired descriptor's caller learns. -/
def swift.exIn (γxm : GName) (b : Nat) (x : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (X : List swift.ExE) (e : swift.ExE), swift.exLb γxm b (X ++ [e]) ∗ ⌜e.1 = x⌝)

/-! ## The descriptor's protocol facts -/

/-- **Why a `PRE_ACCEPT` descriptor is pre-accepted** (persistent; table rev 4 §3.7). -/
def swift.phaseWhy (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(⌜dv.phase ≠ W64 1⌝ ∨ sp.preacc γ r b (toCmdId x) (dv.D.map toCmdId))

/-- `y` is a command of `b`'s `MSync` (persistent). -/
def swift.syncIn (γ : sp.Names) (b : Nat) (y : sp.CmdId) : IProp netDistGF :=
  iprop(∃ M : sp.SyncMsg, sp.syncIs γ b M ∗ ⌜y ∈ sp.syncOrder M⌝)

/-- **At `b`'s leader, the descriptor's `dep` is the one this leader pre-accepted, or the command
is a sync command of `b`** (persistent; table rev 5, G-ldr, for D33's `execW`). At the leader
`dep` is written only by `handlePropose` (:520, with :521's pre-acceptance) and by
`handleSyncEntry` (recovery.go:710). Round 53 (D73 (1), 52-1): at a follower, from `ACCEPT` on,
`dep` is the leader's (`fastAckFromLeader` adopts it, swift.go:643) with the leader's sequence
(`sp.locDeps` of the leader's ack, Inv.lean) or a sync command's; the trivial follower disjunct
and a pre-acceptance's are for `START`/`PRE_ACCEPT` only. Round 54 (D74 (2), 53-4): the sync
disjunct is the leader's; a follower's sync entry has the leader's prefix (`msgOk (.sync)`'s
`locLb` of `syncSeq M`, through `handleSync` and `syncMP`). Round 55 (D77 (1), 53-3'): or, at a
follower, `x` was executed in `b` (`exIn γxm b x`; nested in the first disjunct so that the
constructions in HandleSyncEntry.lean, a run-loop file, are unchanged): `fastAckFromLeader`'s `ACCEPT` without the
adoption when `delivered.Has` is true (swift.go:643); `deliver` refutes it with its ticket. Round 56 (D79 (2), R2-a): the leader's sync disjunct is at
`COMMIT` (T24 writes it with the phase; the leader's `fastAckFromLeader` refutes it with its own
pre-acceptance, which a base command cannot have: `sp.preacc_notBase`), so a leader's executed
base command is reported in `COMMIT`. -/
def swift.depWhy (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop((⌜(r ≠ sp.leaderOf N b ∧ uint.nat dv.phase ≤ 1) ∨ dv.propose = null ∨ dv.phase = W64 0⌝ ∨
      (⌜r ≠ sp.leaderOf N b⌝ ∗ swift.exIn γxm b x)) ∨
    (⌜r = sp.leaderOf N b ∨ uint.nat dv.phase ≤ 1⌝ ∗ sp.preacc γ r b (toCmdId x) (dv.D.map toCmdId)) ∨
    (⌜r = sp.leaderOf N b ∧ dv.phase = W64 3⌝ ∗ swift.syncIn γ b (toCmdId x)) ∨
    (⌜r ≠ sp.leaderOf N b⌝ ∗ ∃ D : List sp.CmdId,
      sp.locDeps γ (sp.leaderOf N b) b (toCmdId x) D ∗ ⌜(dv.D.map toCmdId).Perm D⌝))

/-- **A stopped descriptor's snapshot facts** (persistent; DV2): no proposal, or the proposal
(read-only), the dependencies' contents, and why its phase and `dep` are what they are. Round 52
(51-5, D71 (3); 49-3): and the proposal's `propIs` (from the owner's `repPre`; T19, T7e). -/
def swift.stopFacts (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(⌜dv.propose = null⌝ ∨
    ((∃ gv : replica.defs.GPropose, dv.propose ↦□ gv) ∗ dv.dep ↦*□ dv.D ∗
      swift.phaseWhy γ N r b x dv ∗ swift.depWhy γ γxm N r b x dv ∗
      swift.propIs γ dv.propose (toCmdId x) dv.c))

/-- **The row facts an owner keeps about its token** (round 35, table rev 7c §3.13, G-rrec): what
`descSt` holds about `x`'s row `rv` besides `rowPhaseOk` (AcksSpecs' `rowAcc` and the commit
facts, over `γ r` instead of the record): a committed row's fact, an accepted row's fact, a
pre-accepted or pathed row's proposal, the proposal read-only, and `COMMIT` with a proposal only
at a committed row. A rest record keeps them, so that the run loop's next inline call (T7 start)
rebuilds the owner's `descSt` from the store's token. -/
def swift.rowFacts (γ : sp.Names) (r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) : IProp netDistGF :=
  iprop((⌜rv.2.2.2 = false⌝ ∨ sp.committed γ r b (toCmdId x)) ∗
    (⌜rv.2.2.1 = false⌝ ∨ sp.accepted γ r b (toCmdId x)) ∗
    ⌜rv.1.isSome ∨ rv.2.1.isSome ∨ rv.2.2.1 = true ∨ rv.2.2.2 = true → dv.propose ≠ null⌝ ∗
    (⌜dv.propose = null⌝ ∨ ∃ gv : replica.defs.GPropose, dv.propose ↦□ gv) ∗
    ⌜dv.phase = W64 3 → rv.2.2.2 = true ∨ dv.propose = null⌝)

/-! ## The store's records, claims and receipts -/

/-- **The incarnation `γi` is committed in the epoch of ballot `b`** (round 56, D79 (1), 52-3;
persistent): the epochs' map `γcg` has `b ↦ some γk` (inserted where the epoch's `DescG` is
allocated, `swift.descDS_alloc`) and `γi` is committed in `γk` (`swift.incW` at the epoch's `g`,
`γk = g.γk`). A rest record holds it, so that the report finds its incarnation in the stopped
epoch's commit record (`incInv`, `swift.stopPS`). -/
def swift.cgW (γcg : GName) (b : Nat) (γi : GName) : IProp netDistGF :=
  iprop(∃ γk γsg : GName, ghostMapElem γcg (b, false) DFrac.discard (some γk : Option GName) ∗
    ghostMapElem γk γi DFrac.discard γsg)

/-- **The free permit of ballot `b`** (round B1, D82 (4); exclusive, epoch-level): the epochs'
map's second key of `b`, `(b, true)`, unspent (`none`). Minted with `b`'s registration
(`swift.descDS_alloc`), held by the run loop through the epoch (`descDS`, `descDSH`) and its stop
(`swift.stopPS`), spent before `handleSync`'s free (`swift.freeP_spend`). The report holds it, so
it sees no `released` record of `b` (`swift.freeSp`). -/
def swift.freeP (γcg : GName) (b : Nat) : IProp netDistGF :=
  ghostMapElem γcg (b, true) (DFrac.own 1) (none : Option GName)

/-- **Ballot `b`'s free permit spent** (round B1, D82 (4); persistent): what a `released` record
of `b` holds (`retWhy .released`, `swift.store_release`). It contradicts the unspent permit. -/
def swift.freeSp (γcg : GName) (b : Nat) : IProp netDistGF :=
  iprop(∃ γ0 : GName, ghostMapElem γcg (b, true) DFrac.discard (some γ0 : Option GName))

instance swift.freeSp_persistent (γcg : GName) (b : Nat) : Persistent (swift.freeSp γcg b) := by
  unfold swift.freeSp; infer_instance

instance swift.freeSp_timeless (γcg : GName) (b : Nat) : Timeless (swift.freeSp γcg b) := by
  unfold swift.freeSp; infer_instance

instance swift.freeP_timeless (γcg : GName) (b : Nat) : Timeless (swift.freeP γcg b) := by
  unfold swift.freeP; infer_instance

instance swift.cgW_persistent (γcg : GName) (b : Nat) (γi : GName) :
    Persistent (swift.cgW γcg b γi) := by
  unfold swift.cgW; infer_instance

instance swift.cgW_timeless (γcg : GName) (b : Nat) (γi : GName) :
    Timeless (swift.cgW γcg b γi) := by
  unfold swift.cgW; infer_instance

/-- **Why a token is in the store** (table rev 5 §3.0 Node, §3.7): its record `rk` for the key
`K = (b, y)` with rows `rv`. A rest record (`rest d γi`: the token of a descriptor `d` at rest,
stopped or between two of the run loop's inline calls) holds half of `d`'s `phase` and `dep`,
a quarter of its `propose`, and half of its incarnation's `γi`, so that its holder (the claim
`rest d γi`) and the report find `d`'s values. Round B1 (D82 (4)): a `released` record holds its
ballot's spent free permit (`swift.freeSp`). -/
def swift.retWhy (γ : sp.Names) (γxm γcg : GName) (str : swift.CommandId → GoString) (N r : Nat)
    (K : Nat × sp.CmdId) (rv : swift.RowV) : swift.RecK → IProp netDistGF
  | .empty => iprop(⌜rv = swift.rowEmpty⌝)
  | .sync => iprop(⌜rv = swift.rvSync⌝ ∗ swift.syncIn γ K.1 K.2)
  | .exec => iprop(∃ x : swift.CommandId, ⌜toCmdId x = K.2⌝ ∗ swift.exIn γxm K.1 x)
  | .rest d γi => iprop(∃ (x : swift.CommandId) (dv : swift.DescV),
      ⌜toCmdId x = K.2 ∧ swift.rowPhaseOk N r K.1 dv rv⌝ ∗
      ghostVar γi (1 : Qp).half (str x, d) ∗
      typedPointsto (swift.dfld d go!"phase") dv.phase (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"dep") dv.dep (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.dfld d go!"propose") dv.propose (DFrac.own (1 : Qp).half.half) ∗
      swift.stopFacts γ γxm N r K.1 x dv ∗ swift.rowFacts γ r K.1 x dv rv ∗
      swift.cgW γcg K.1 γi)
  | .released => swift.freeSp γcg K.1

/-- **A claim** on the stored token of `K`, of kind `ck` (exclusive; minted with the token,
table rev 5 T28, C2). -/
def swift.claimTok (γcl : GName) (K : Nat × sp.CmdId) (ck : swift.ClK) : IProp netDistGF :=
  ghostMapElem γcl K (DFrac.own 1) ck

/-- **The ledger's receipt** of a key `K` taken out of the store: the registry share `(j, qj)`
the ledger keeps for it (table rev 5, C1). -/
def swift.outRcpt (γout : GName) (K : Nat × sp.CmdId) (jq : Nat × Qp) : IProp netDistGF :=
  ghostMapElem γout K (DFrac.own 1) jq

/-- **The execution ticket of the key `K`** (round 46, D-SWC2-5/D57; moved below the store from
DeliverE.lean, whose `swift.xTix γxu b x` is this at `(b, toCmdId x)`): exclusive, minted with the
row token's insert into the rows' map, consumed when `deliver` executes the command. -/
def swift.xTixK (γxu : GName) (K : Nat × sp.CmdId) : IProp netDistGF :=
  ghostMapElem γxu K (DFrac.own 1) ()

/-- The tickets' authority: the keys minted (round 46, D57: next to the rows' authority in
`storeD`, its keys among the rows' keys). -/
def swift.xuAuth (γxu : GName) (U : GMap (Nat × sp.CmdId) Unit) : IProp netDistGF :=
  ghostMapAuth γxu 1 U

/-- **The ticket or its use** (round 46): what travels with `K`'s row token (in the store's
record, in the owner's `rowTokO`): the ticket, or the command executed in `K`'s epoch. -/
def swift.tixOr (γxu γxm : GName) (K : Nat × sp.CmdId) : IProp netDistGF :=
  iprop(swift.xTixK γxu K ∨ ∃ x : swift.CommandId, ⌜toCmdId x = K.2⌝ ∗ swift.exIn γxm K.1 x)

end defs

section instances
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

instance swift.exAt_persistent (γxm : GName) (b i : Nat) (e : swift.ExE) :
    Persistent (swift.exAt γxm b i e) := by unfold swift.exAt; infer_instance

instance swift.exLb_persistent (γxm : GName) (b : Nat) (X : List swift.ExE) :
    Persistent (swift.exLb γxm b X) := by unfold swift.exLb swift.exAt; infer_instance

instance swift.exIn_persistent (γxm : GName) (b : Nat) (x : swift.CommandId) :
    Persistent (swift.exIn γxm b x) := by unfold swift.exIn; infer_instance

/-- `exIn` is timeless (round 55: it is in `depWhy`, hence in the rest record). -/
instance swift.exIn_timeless (γxm : GName) (b : Nat) (x : swift.CommandId) :
    Timeless (swift.exIn γxm b x) := by
  unfold swift.exIn swift.exLb swift.exAt; infer_instance

instance swift.tixOr_timeless (γxu γxm : GName) (K : Nat × sp.CmdId) :
    Timeless (swift.tixOr γxu γxm K) := by
  unfold swift.tixOr swift.xTixK swift.exIn swift.exLb swift.exAt; infer_instance

instance swift.phaseWhy_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.phaseWhy γ N r b x dv) := by
  unfold swift.phaseWhy; infer_instance

instance swift.syncIn_persistent (γ : sp.Names) (b : Nat) (y : sp.CmdId) :
    Persistent (swift.syncIn γ b y) := by unfold swift.syncIn; infer_instance

instance swift.depWhy_persistent (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.depWhy γ γxm N r b x dv) := by
  unfold swift.depWhy; infer_instance

instance swift.rowFacts_persistent (γ : sp.Names) (r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) (rv : swift.RowV) : Persistent (swift.rowFacts γ r b x dv rv) := by
  unfold swift.rowFacts; infer_instance

instance swift.stopFacts_persistent (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.stopFacts γ γxm N r b x dv) := by
  unfold swift.stopFacts; infer_instance

instance swift.propIs_timeless (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c : sp.Cmd) :
    Timeless (swift.propIs γ gp x c) := by
  unfold swift.propIs sp.cmdIs; infer_instance

/-- `locDeps` is timeless (round 54: it is in `depWhy`, hence in the rest record). -/
instance swift.locDeps_timeless (γ : sp.Names) (r b : Nat) (x : sp.CmdId) (D : List sp.CmdId) :
    Timeless (sp.locDeps γ r b x D) := by
  have h : ∀ s, Timeless (sp.locLb γ r b s) := fun s => by
    unfold sp.locLb
    exact BigSepL.bigSepL_timeless (fun {_ _} _ => by unfold sp.locAt sp.cmdIs; infer_instance)
  unfold sp.locDeps; infer_instance

instance swift.retWhy_timeless (γ : sp.Names) (γxm γcg : GName) (str : swift.CommandId → GoString)
    (N r : Nat) (K : Nat × sp.CmdId) (rv : swift.RowV) (rk : swift.RecK) :
    Timeless (swift.retWhy γ γxm γcg str N r K rv rk) := by
  cases rk <;> dsimp only [swift.retWhy] <;>
    (try unfold swift.syncIn) <;> (try unfold swift.exIn swift.exLb swift.exAt) <;>
    (try unfold swift.stopFacts swift.phaseWhy swift.depWhy swift.syncIn) <;>
    (try unfold swift.rowFacts sp.committed sp.accepted) <;>
    (try unfold sp.syncIs) <;> (try unfold sp.preacc) <;> infer_instance

end instances

end Perennial.github_com.imdea_software.swiftpaxos
