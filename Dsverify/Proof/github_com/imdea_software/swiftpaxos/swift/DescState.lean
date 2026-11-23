/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescState.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The descriptors' state** (round 14, sv-swb; notes/prove-swift.md §20): the refinement of
`RunInv.lean`'s provisional `swift.descState`, designed for its three users:

* the descriptors (`getCmdDescWith`/`newDesc`, `handleDesc`, `handleMsg`): their message
  predicate `swift.descMP` (the acks, the proposal, a history slot, a sync entry);
* `stopDescs`/`handleSync` (sv-swa's requests, main session's message of round 14): when the
  epoch stops, the whole `cmdDescs` view with each entry's descriptor recoverable as
  `swift.descFree DF d` (`swift.descsStopped`, SyncSpecs.lean) (round 14's proposal halves,
  `propsHeld`, are gone with D16: proposals are read-only);
* the run loop between arms (`swift.runInv`).

Design (definitions only; their users' proofs are open):

* `swift.descHome γ DF d y`: what a descriptor of `y` at rest holds for the run loop:
  `descFree DF d` (`γ`, `y` unused since D16).
* `swift.descEnt … k v`: a `cmdDescs` entry `k ↦ v` in the descriptors' invariant: `v` is the
  descriptor `d` of `y` (`k = str y`, its record `descIs`), and either at home (`descHome`:
  stopped, or a sequential descriptor between two of the run loop's `handleMsg`s) or running
  (`Run d y`, the goroutine's stop protocol: the invariant's half of `active` at `true` and its
  `stopChan` bag, whose `wg.Done()` follows the goroutine's switch of the entry to home; `Run`
  is a parameter until `handleDesc`'s proof fixes it).
* `swift.descInv`: the view `cmapView γdc Mc` (the other half is cmap's) with every entry's
  `descEnt`, until the run loop stops the epoch (`γst`: its half `false` in `descStateR`; at the
  stop it swaps both halves to `true` and takes the contents). Namespace `swift.descN`
  (disjoint from cmap's: `descInv` opens inside cmap's atomic updates, as `delivInv`).
  A descriptor goroutine's `cmdDescs.Remove` (history slot) removes its entry with its
  `descEnt` (its `Run`: the goroutine then frees the descriptor itself).
* `swift.descStateR rp x DF Run`: `cmdDescs` (whole), its `isCMapV`/`readerV` over `descR`,
  the records' authority, the invariant and the run loop's `γst` half.

`stopDescs` (recovery.go:741) then: each round's `IterCb` sends a `WaitGroup` to every active,
non-sequential descriptor; after `wg.Wait()` each signalled entry is home; the last round signals
none, so (reading `active`, which needs the stronger `IterCb` spec requested of sv-swc, §19)
every entry is home: open `descInv` with the `γst` half, take `cmapView γdc Mc` and each entry's
`descHome` — `descsStopped γd DF rp` (the `descFree`s).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescDefs
public import Perennial.Proof.sync.WaitGroupJoin
public import Dsverify.Proof.github_com.orcaman.concurrent_map.RemoveLDefs
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The descriptors' invariant's namespace. -/
def swift.descN : Namespace := ndot nroot "swiftpaxos.descs"

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The descriptors' message predicate** of `x`'s descriptor in epoch `b`: an ack or a
string (`ackMsgP`, HandleMsg.lean), a proposal message (`propMsgR`, RunSpecs.lean; round 28, G7:
with `handle_stepD`'s fresh row token), a history slot (`SL`: the reply goroutine's, with
`handleMsg.slotSpecI` to be restated), a sync entry (`SE`: sv-swa's `getCmdDesc.syncSpecI`
payload). It does not mention the descriptor's own state (no cycle with `descF`). -/
def swift.descMP (c : swift.DC) (b : Nat) (x : swift.CommandId)
    (SL SE : GoInterface → IProp netDistGF) (m : GoInterface) : IProp netDistGF :=
  iprop(swift.ackMsgP c b x m ∨
    (∃ (pm gp : Loc) (cc : sp.Cmd) (dep hs : GoSlice) (sq : w64) (ld : Bool) (s : sp.Seq)
        (B D P : List sp.CmdId) (H : swift.SHash),
      ⌜m = interface.mkOk (go.GoType.PointerType swift.proposeMsg.ty) #pm⌝ ∗
      swift.propMsgR c.γ pm gp x cc dep hs sq c.N c.r b ld s B D P H ∗
      swift.claimTok c.γcl (b, toCmdId x) .fresh) ∨
    SL m ∨ SE m)

/-- What a descriptor of `y` at rest holds for the run loop (see the file header). -/
def swift.descHome (γ : sp.Names) (DF : Loc → IProp netDistGF) (d : Loc) (y : swift.CommandId) :
    IProp netDistGF :=
  iprop(swift.descFree DF d)

/-! ### Round 18: the concrete stop protocol (notes/prove-swift.md §24) -/

/-- Round 37 (D37): the lent state's ghost variable `γb` holds a cmap pin's data. -/
instance swift.pinD_countable : Pos.Countable github_com.orcaman.concurrent_map.PinD :=
  .ofInjective (fun π => Pos.Countable.encode (π.n, π.shs, π.i, π.p, π.q, π.Mi))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h'
      subst h1 h2 h3 h4 h5 h6; rfl)

/-- Round 38 (R9-2): the lock-lends' ghost map records a cmap lock token. -/
instance swift.cmapLock_countable : Pos.Countable github_com.orcaman.concurrent_map.CmapLock :=
  .ofInjective (fun t => Pos.Countable.encode (t.n, t.shs, t.p, t.Mi))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'; obtain ⟨h1, h2, h3, h4⟩ := h'
      subst h1 h2 h3 h4; rfl)

/-- **The kind of a lock-lend's lender** (round 38, table rev 9 §3R9.5, D-R9-3): the run loop
(`run`: its T20 refuter is the round's element `γs k ↦ false`) or a loan holder (`own iL j`: a
quarter of its loan receipt `γlj iL ↦ (j, ¼)`; the inline owner has `j = 0`). -/
inductive swift.LendK where
  | run
  | own (iL j : Nat)

instance swift.lendK_countable : Pos.Countable swift.LendK :=
  .ofInjective (fun l => Pos.Countable.encode (match l with
      | .run => (none : Option (Nat × Nat))
      | .own iL j => some (iL, j)))
    (by
      rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- **A share-pool over any fractional share `S`** (round 38, plan R9a.1; as `epochPool`): the
loans' authority `L`, the pool's own share `q0` and the closing wand. -/
def swift.poolS (S : Qp → IProp netDistGF) (Q : Qp) (γp : GName) (q0 : Qp) (L : GMap Nat Qp) :
    IProp netDistGF :=
  iprop(ghostMapAuth γp 1 L ∗ S q0 ∗ (S q0 -∗ ([∗map] _i ↦ q ∈ L, S q) -∗ S Q))

/-- **The fraction of `cmdDescs` a sub-pool share `q` carries** (round 38, R9-1/D-R9-1: `κ = ½ / Qd`
per unit; plan R9a.1): `q / (2 Qd)`, so the whole sub-pool `Qd` carries `½`. -/
def swift.descK (Qd q : Qp) : Qp :=
  ⟨q.val / (2 * Qd.val), Rat.div_pos q.2 (Rat.mul_pos (by decide) Qd.2)⟩

theorem swift.descK_add (Qd q1 q2 : Qp) : swift.descK Qd (q1 + q2) = swift.descK Qd q1 + swift.descK Qd q2 := by
  apply Subtype.ext
  simp only [swift.descK, Qp.val_add]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

theorem swift.descK_Qd (Qd : Qp) : swift.descK Qd Qd = (1 : Qp).half := by
  apply Subtype.ext
  simp only [swift.descK, Qp.val_half, Qp.val_one]
  have h : Qd.val ≠ 0 := Rat.ne_of_gt Qd.2
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev, ← Rat.mul_assoc,
    Rat.mul_comm Qd.val]; rw [Rat.mul_comm Qd.val⁻¹, Rat.mul_inv_cancel _ h]

/-- A share `q` of the epoch with `X q` (round 38, R9-1: the descriptors' sub-pool lends
`cmdDescs`' fraction with the epoch share; `X := descX …`). -/
def swift.epochShareX (n : swift.EpN) (v : swift.EpV) (X : Qp → IProp netDistGF) (q : Qp) :
    IProp netDistGF :=
  iprop(swift.epochShare n v q ∗ X q)

/-- The descriptors' sub-pool (round 38, R9-1): `poolS` over `epochShareX`. -/
abbrev swift.epochPoolX (n : swift.EpN) (v : swift.EpV) (X : Qp → IProp netDistGF) (Q : Qp)
    (γp : GName) (q0 : Qp) (L : GMap Nat Qp) : IProp netDistGF :=
  swift.poolS (swift.epochShareX n v X) Q γp q0 L

/-- **The descriptors' state of one epoch** (round 18): the per-epoch ghost names and the
epoch's values the descriptors' sub-pool shares. `γdc`: `cmdDescs`' view; `γst`: the stop
flag; `γs`: the keys signalled in the current `stopDescs` round (a ghost map, authority
`stopDescs`'); `γb`: `stopDescs`' borrows of an entry's `seq` (a token count, authority
`stopDescs`'); `γk`: the keys of the running goroutines (authority in `descInv`, an element
per goroutine: how a goroutine finds its own entry); `γq`: the descriptors' epoch sub-pool
(a share `Qd` of the epoch `ev`, lent to the goroutines). -/
structure swift.DescG where
  γdc : GName
  γst : GName
  γs : GName
  γb : GName
  γk : GName
  γq : GName
  ev : swift.EpV
  Qd : Qp
  /-- round 23 (D18 G5): the message predicate of `y`'s descriptor in this epoch (a running
  goroutine's entry holds its `msgs` channel's bag at `mp y`, so the run loop can send) -/
  mp : swift.CommandId → GoInterface → IProp netDistGF
  /-- round 26 (D23 G9): the run loop's sequential descriptors (a ghost map `d ↦ y`; the entry's
  `sq d y` holds the element whole, the run loop's `swift.seqStore` the authority) -/
  γS : GName
  /-- round 26 (D23 G9): a sequential descriptor's state between two of the run loop's inline
  `handleMsg`s, held by the run loop outside `descInv` (`swift.seqStore`; `swift.soOk`) -/
  so : Loc → swift.CommandId → IProp netDistGF
  /-- round 29 (D26 G11): the sequential descriptors made by goroutines (their dependency lookups,
  `depSpecI`): a ghost map `d ↦ y` in the shared invariant `swift.seqInbox` (the run loop moves an
  entry to its own store, `γS`, when it first handles it inline) -/
  γS2 : GName
  /-- round 37 (table rev 8 §3.14 G-circ, D38): the **raw** form of a new sequential descriptor
  (kind-free, `swift.soRaw`, SeqPark.lean): the only form the goroutines' inbox holds, so the inbox
  (`seqInbox`, in every owner's environment) reads no `so` (`g.sr ⊢ g.so`, `soOk`) -/
  sr : Loc → swift.CommandId → IProp netDistGF
  /-- round 35 (table rev 7 §3.11, D36; G-rcpt): the entries' receipts, keyed by the
  **incarnation** `γi` (value `(j, qj)`: the registry share `descGo` holds; ½ in the entry's
  `descGo`, ½ in the goroutine's `c.kf`). Inserted at `γi`'s allocation (T2', a name fresh for
  the map), set at the spawn's loan (T4). -/
  γj : GName
  /-- round 34 (table rev 5 C1): the loans' receipts (key `iL`, value `(j, qj)`: the registry
  share `loanRec` holds; ½ in the record, ½ in the holder's `c.env`) -/
  γlj : GName
  /-- round 38 (table rev 9/9a §3R9.5, R9-2 + C3, D41/D42): the lock-lends of the entries
  (`GMap GoString (CmapLock × LendK × GoInterface)`: the lender's lock token, its kind and the
  entry's value; authority in `descInv`, ½ in the deposit (`entL`), ½ with the lender) -/
  γw : GName

/-- **The fraction `q` of the sub-pool's `cmdDescs`** (round 38, R9-1; table §3R9.4 `X q`): the
field at `descK g.Qd q` with the map's (persistent) `isCMapV`. A loan holder's `envK` keeps it, so
its `r.cmdDescs` loads (swift.go:861, :1054; not atomic, E8) are owned. -/
def swift.descX (rp : Loc) (γd : GName) (g : swift.DescG) (dm : GoSlice) (q : Qp) : IProp netDistGF :=
  iprop(typedPointsto (swift.fld rp go!"cmdDescs") dm (DFrac.own (swift.descK g.Qd q)) ∗
    github_com.orcaman.concurrent_map.isCMapV dm g.γdc (swift.descR γd))

/-- **The run loop's lock-lend refuter** (round 38, table §3R9.5, D-R9-3): `run`: the round's
element of `k` at `false` (only the run loop holds `γs`'s authority, ∅ outside `stopDescs`);
`own iL j`: a quarter of the lender's loan receipt (`rcptAuth` with no loan refutes it, T20). -/
def swift.lendRef (g : swift.DescG) (k : GoString) : swift.LendK → IProp netDistGF
  | .run => ghostMapElem g.γs k (DFrac.own 1) false
  | .own iL j => ghostMapElem g.γlj iL (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half)

/-- **A descriptor's `msgs` channel's bag** (round 26, D23 G8): its predicate is the epoch's `MPy`
with a persistent witness `W` the channel's creator fixed (a goroutine's: its incarnation's commit
witness `ghostMapElem g.γk γi DFrac.discard true`, `swift.incW`); every sender has `□ W` from the
entry it read under the shard lock. -/
def swift.bagW (m : Loc) (MPy : GoInterface → IProp netDistGF) : IProp netDistGF :=
  iprop(∃ (γm : ChanNames) (W : IProp netDistGF),
    isChanBag γm m (fun v => iprop(MPy v ∗ □ W)) ∗ □ W)

instance swift.bagW_persistent (m : Loc) (MPy : GoInterface → IProp netDistGF) :
    Persistent (swift.bagW m MPy) := by
  unfold swift.bagW; infer_instance

/-- A descriptor at home in the invariant (round 18): `descHome γ (descDF DR) d y` but for
the half of `seq` (value `s`) the entry keeps outside (`descEnt`). Round 24 (sv-swb): with
the bag of its `msgs` channel at `MPy` (persistent; a stopped goroutine's entry keeps it, so the
run loop's `getCmdDescWith` can still send on the channel it reads under the shard lock). -/
def swift.descHomeS (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (MPy : GoInterface → IProp netDistGF) (d : Loc) (y : swift.CommandId)
    (s : Bool) : IProp netDistGF :=
  iprop(∃ (m sc sl fa : Loc) (a : Bool),
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) ∗
    swift.bagW m MPy ∗
    swift.dfld d go!"stopChan" ↦ sc ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    swift.msgSetFree sl ∗ swift.msgSetFree fa ∗
    swift.dfld d go!"active" ↦ a ∗ typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half) ∗
    ⌜a = true → s = true⌝ ∗ DR d)

/-- A goroutine's "not yet signalled" token (exclusive; a stop request carries the other one
it would need, so a second request is contradictory). -/
def swift.sgTok (γsg : GName) : IProp netDistGF := ghostVar γsg (1 : Qp) true

/-- **A stop request** (round 18; the `*WaitGroup` `wg` sent on the descriptor `d`'s
`stopChan` `sc` for key `k`): the right to `Done` with `P :=` the round's element of `k`
(`stopDescs` collects them at `Wait`), the goroutine's signal token, (round 37, table rev 8
G-req/G-lend) half of that element (the signalled entry's `descGo` has the other half), and no
share of `stopChan` (a request still queued when the descriptor is freed costs nothing). -/
def swift.stopMP (γs γsg : GName) (k : GoString) (_d _sc : Loc) (wg : Loc) : IProp netDistGF :=
  iprop(sync.join.ownDone wg (ghostMapElem γs k (DFrac.own 1) true) ∗
    swift.sgTok γsg ∗ ghostMapElem γs k (DFrac.own (1 : Qp).half) true)

/-- **A descriptor's stop channel's bag** (round 27, D23 G8): `stopMP` with a persistent witness
`W` the channel's creator fixed (a goroutine's incarnation's commit witness `swift.incW`, so a stop
request can be its first message); the sender (`stopDescs`) has `□ W` from the entry. -/
def swift.stopBag (γc : ChanNames) (sc : Loc) (P : Loc → IProp netDistGF) : IProp netDistGF :=
  iprop(∃ W : IProp netDistGF, isChanBag γc sc (fun wg => iprop(P wg ∗ □ W)) ∗ □ W)

instance swift.stopBag_persistent (γc : ChanNames) (sc : Loc) (P : Loc → IProp netDistGF) :
    Persistent (swift.stopBag γc sc P) := by
  unfold swift.stopBag; infer_instance

/-- The commit witness of the incarnation `γi` (round 27, D23 G8). Round 40 (table rev 10a
§3R10.21, B1, D46): its value is the name `γsg` of the incarnation's stop-signal token (the stop
bag's name), so two holders that each name the stop bag agree on it (`swift.incW_agree`). -/
def swift.incW (g : swift.DescG) (γi γsg : GName) : IProp netDistGF :=
  ghostMapElem g.γk γi DFrac.discard γsg

instance swift.incW_persistent (g : swift.DescG) (γi γsg : GName) :
    Persistent (swift.incW g γi γsg) := by
  unfold swift.incW; infer_instance

/-- Two commit witnesses of one incarnation name one stop bag (round 40, B1). -/
theorem swift.incW_agree (g : swift.DescG) (γi γsg γsg' : GName) :
    swift.incW g γi γsg ∗ swift.incW g γi γsg' ⊢ ⌜γsg = γsg'⌝ := by
  iintro ⟨H1, H2⟩
  iunfold swift.incW at H1 H2
  ihave %h := ghostMapElem_agree γi g.γk _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- **A running goroutine's entry's stop state** (round 40, table rev 10 P39-1, rev 10a): by `active`
(value `a`) unsignalled (the signal token) or signalled (half of the round's element), with half of
`stopChan` (the `a = false` branch is dead, PF21, kept: D45 (1)), or **stopping** (left by the stop
arm's ghost take T19a.g, until T19h): half of the round's element at `true`, half of `stopChan` and
a quarter of the entry's receipt (deposited by the goroutine, which keeps the other quarter to agree
the receipt's value at T19h: gap 40-4, table rev 10a §3R10.21), `active` wholly with the goroutine. -/
def swift.goSt (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc) (y : swift.CommandId)
    (a : Bool) (sc : Loc) (γsg γi : GName) (j : Nat) (qj : Qp) : IProp netDistGF :=
  iprop((typedPointsto (swift.dfld d go!"active") a (DFrac.own (1 : Qp).half) ∗
      (if a then
        iprop((swift.sgTok γsg ∨ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true) ∗
            typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half))
      else typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half))) ∨
    (ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
      typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, qj)))

/-- **A running goroutine's entry** (round 18, the concrete `Run`; notes/prove-swift.md §24):
a share of its `cntL` loan's element (`j`; a share of the run loop's freeze flag, `j = 0`, is
also allowed: contradicted once frozen), half of `active` (the goroutine holds the other
half), a quarter of `seq` (`entS` holds a half, the goroutine's `descF` a quarter; round 23,
D18 G4), half of `msgs` with its bag at `g.mp y` (the goroutine's `descF` has the other half;
round 23, D18 G5: the run loop reads `msgs` under the shard lock and sends), the stop channel's
bag, and by `active`:
unsignalled (the signal token; round 19: no thread token, `stopDescs` uses `sync.join`) or
signalled in the current round (round 37, table rev 8 G-lend/G-req: half of the round's element of
its key, the request carries the other half), with half of `stopChan` either way, or stopped
(`active = false`: half of `stopChan`; table rev 8b K3: the stop arm takes the element's half when
it writes `active`). Round 40 (table rev 10/10a, P39-1, B1): the stop state is `goSt`, with the
stopping alternative; the commit witness names the stop bag's `γsg`; `γi` is flattened. -/
def swift.descGo (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc)
    (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (j : Nat) (qj : Qp) (a : Bool) (sc : Loc) (γc : ChanNames) (γsg : GName) (m : Loc)
      (γi : GName),
    ghostMapElem γn j (DFrac.own qj) false ∗
    swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
    ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qj) ∗
    typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half) ∗ swift.bagW m (g.mp y) ∗
    swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
    swift.goSt g str d y a sc γsg γi j qj)

/-- **An entry's state** (round 18): its `seq` (value `s`, fixed while the entry is in the map:
half here, half in the state) and the descriptor at home (`descHomeS`) or running (`Run d y`,
`seq = false`; the concrete `Run` holds a quarter of `seq`), or (round 23, D18 G3) a sequential
descriptor between two of the run loop's `handleMsg`s (`Sq d y`, `seq = true`: its owner
state). -/
def swift.entI (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (Run Sq : Loc → swift.CommandId → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF) (d : Loc) (y : swift.CommandId)
    (s : Bool) : IProp netDistGF :=
  iprop((⌜s = false⌝ ∗ swift.descHomeS γ DR (MP y) d y s) ∨ (⌜s = false⌝ ∗ Run d y) ∨
      (⌜s = true⌝ ∗ Sq d y))

/-- **An entry's state with its outer part whole** (round 38, table rev 9 §3R9.5 `entO none ∗ entI`;
P1): the outer `seq` ½ and `msgs` ¼ (fixed while the entry is bound, PF17) and the inner part
`entI`. What the run loop's read-lend (T18l) takes whole. -/
def swift.entS (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (Run Sq : Loc → swift.CommandId → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF) (d : Loc) (y : swift.CommandId) :
    IProp netDistGF :=
  iprop(∃ (s : Bool) (m : Loc), typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half) ∗
    swift.entI γ DR Run Sq MP d y s)

/-- **A lock-lent entry** (round 38, table rev 9a §3R9.5 `entO (some (t, ρ, v)) ∗ entI`; P1, R9-2,
C3): the outer part at half (the lender holds `seq` ¼ and `msgs` ⅛), the lender's deposit (its
lock token at `t`, its refuter) and `γw`'s half naming it, and the inner part untouched (T19 may
run). -/
def swift.entL (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (Run Sq : Loc → swift.CommandId → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF) (g : swift.DescG) (k : GoString)
    (v : GoInterface) (t : github_com.orcaman.concurrent_map.CmapLock) (ρ : swift.LendK)
    (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (s : Bool) (m : Loc),
    typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half.half) ∗
    ghostMapElem g.γw k (DFrac.own (1 : Qp).half) (t, ρ, v) ∗
    github_com.orcaman.concurrent_map.cmapLocked g.γdc k (some v) t ∗ swift.lendRef g k ρ ∗
    swift.entI γ DR Run Sq MP d y s)

/-- What `stopDescs` needs of a sequential entry's state `Sq` (round 23, D18 G3): it reads
`active` (true) and gives the state back; once frozen it is at home (`descHomeS … true`, the
fields `descFree` drops). -/
def swift.sqOk (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (Sq : Loc → swift.CommandId → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF) : Prop :=
  (∀ d y, Sq d y ⊢ ∃ qa : Qp, typedPointsto (swift.dfld d go!"active") true (DFrac.own qa) ∗
      (typedPointsto (swift.dfld d go!"active") true (DFrac.own qa) -∗ Sq d y)) ∧
  (∀ d y, Sq d y ⊢ ∃ qs : Qp, typedPointsto (swift.dfld d go!"seq") true (DFrac.own qs) ∗ True) ∧
  (∀ d y, Sq d y ⊢ ∃ (m : Loc) (qm : Qp), typedPointsto (swift.dfld d go!"msgs") m (DFrac.own qm) ∗
      (typedPointsto (swift.dfld d go!"msgs") m (DFrac.own qm) -∗ Sq d y))

/-- **The run loop's sequential descriptors** (round 26, D23 G9): each one's state between two
inline `handleMsg`s (`g.so`), keyed by the descriptor (`γS`; the entry's `swift.sqE g d y` holds the
element), or retired (the store holds the element back). -/
def swift.seqStore (g : swift.DescG) : IProp netDistGF :=
  iprop(∃ S : GMap Loc swift.CommandId, ghostMapAuth g.γS 1 S ∗
    [∗map] d ↦ y ∈ S, g.so d y ∨ ghostMapElem g.γS d (DFrac.own 1) y)

/-- The sequential inbox's invariant's namespace (round 29, D26 G11). -/
def swift.seqN : Namespace := ndot nroot "swiftpaxos.seqs"

/-- The sequential inbox's namespace (round 29, G11) is disjoint from the descriptors' and cmap's. -/
theorem swift.seqN_desc_sub : ↑swift.seqN ⊆ (⊤ \ ↑swift.descN : CoPset) := by
  have h : ↑swift.seqN ## (↑swift.descN : CoPset) := by
    unfold swift.seqN swift.descN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨he, h'⟩⟩

theorem swift.seqN_sub3 :
    ↑swift.seqN ⊆ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ ↑swift.descN : CoPset) := by
  have h : ↑swift.seqN ## (↑swift.descN : CoPset) := by
    unfold swift.seqN swift.descN
    exact ndot_ne_disjoint nroot (by decide)
  have h2 : ↑swift.seqN ## (↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
    unfold swift.seqN github_com.orcaman.concurrent_map.cmapN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff, LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => h2 e ⟨he, h'⟩⟩, fun h' => h e ⟨he, h'⟩⟩

/-- **The goroutines' sequential descriptors** (round 29, D26 G11; `inv swift.seqN`): `seqStore`'s
shape at `γS2`. A goroutine's dependency lookup (`depSpecI`) that makes a sequential descriptor
adds its owner state here (inside the invariant); the run loop, at its first inline `handleMsg`
of it, moves it to its own store (`swift.seqTake`: the entry's element switches from `γS2` to
`γS`). Not a split authority (D26's wording): a goroutine's insert needs the whole authority. -/
def swift.seqInbox (g : swift.DescG) : IProp netDistGF :=
  iprop(∃ S : GMap Loc swift.CommandId, ghostMapAuth g.γS2 1 S ∗
    [∗map] d ↦ y ∈ S, g.sr d y ∨ ghostMapElem g.γS2 d (DFrac.own 1) y)

/-- **The concrete sequential entry state** (round 27; round 42, D48 (4): written directly, `DescG.sq` deleted):
(round 29: no element) half of `active` (true), a quarter of `seq` (true), half of `msgs`. -/
def swift.sqC (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗
    ∃ m : Loc, typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half))

/-- **A sequential entry's state** (round 29, G11): the element of the store holding its owner
state (the run loop's `γS` or the inbox's `γS2`) and `sqC` (which holds no element since round
29, so the element's store is known where the entry is read). -/
def swift.sqE (g : swift.DescG) (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ γe : GName, ⌜γe = g.γS ∨ γe = g.γS2⌝ ∗ ghostMapElem γe d (DFrac.own 1) y ∗ swift.sqC d y)

/-- **A new sequential descriptor** (round 27, D23 G9; round 37, table rev 8 G-sqγi and rev 8b
K9): what the spawn holds at Upsert's commit for a descriptor `newDesc` made sequential (`seq = true`;
the entry keeps the other half of `seq`): `msgs` with its bag at the incarnation's predicate
`MPi` (the epoch's `g.mp y` with the commit witness `incW g γi`), the witness, half of the
incarnation `γi` (the owner's; `incInv` holds the other half, committed live), `active`,
`stopChan`, the share map's element and the rest (`descRaw`). Round 38 (table rev 9 P1): `msgs` at
¾; the creator keeps the outer ¼ for the entry's `entS`. -/
def swift.seqNew (g : swift.DescG) (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (γsh : GName)
    (γi γsg : GName) (sqv fqv : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop)
    (γm : ChanNames) (m sc : Loc) (q : Qp) (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"msgs") m (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) ∗
    isChanBag γm m (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) ∗ □ swift.incW g γi γsg ∗
    ghostVar γi (1 : Qp).half (c.str y, d) ∗
    swift.dfld d go!"active" ↦ true ∗
    typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half) ∗
    swift.dfld d go!"stopChan" ↦ sc ∗ ghostMapElem γsh d (DFrac.own 1) q ∗
    swift.descRaw c RC (fun v => iprop(g.mp y v ∗ □ swift.incW g γi γsg)) y g.ev.b sqv fqv szS szF
      memS memF γm d)

/-- **The creation of a sequential descriptor's states** (round 37; table rev 8b K2, the creation
clause of round 27's `soOk` at `g.sr`): a new sequential descriptor made at the record `c0` (the
replica's kind-free record) with the reply channels' object `RC` is the entry's state `sqC` and
the raw owner state `g.sr`. Reads `g.sr`, `g.mp`, never `g.so`, so an owner's context
(`ownCtx`) can hold it (G-circ). -/
def swift.srOk (c0 : swift.DC) (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) : Prop :=
  ∀ (γi γsg : GName) (sqv fqv : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop)
    (γm : ChanNames) (m sc : Loc) (q : Qp) (d : Loc) (y : swift.CommandId),
    swift.seqNew g c0 RC c0.γsh γi γsg sqv fqv szS szF memS memF γm m sc q d y ⊢ swift.sqC d y ∗ g.sr d y

/-- What the run loop needs of a sequential entry's state with its own (round 26, D23 G9; round 29:
the store's element is in `sqE`, clause 1 is now: two owner states of one descriptor exclude each
other, for `seqTake`'s move from the inbox), at the freeze the two together at home, (round 37,
K2) their creation (`srOk`), a share of `active` in the owner's state, and (round 37, G-circ) the
inbox's raw form is an owner state. Round 40 (table rev 10 P39-2, clause 6): a raw inbox form holds
the share map's element of its descriptor whole (`sqE_toSI` refutes an inbox element with an
owner's half). -/
def swift.soOk (γ : sp.Names) (DR : Loc → IProp netDistGF) (c0 : swift.DC)
    (RC : Loc → w32 → IProp netDistGF) (g : swift.DescG) : Prop :=
  (∀ d y y', g.so d y ∗ g.so d y' ⊢ (False : IProp netDistGF)) ∧
  (∀ d y, swift.sqC d y ∗ g.so d y ⊢ swift.descHomeS γ DR (g.mp y) d y true) ∧
  swift.srOk c0 RC g ∧
  (∀ d y, g.so d y ⊢ ∃ (a : Bool) (qa : Qp),
      typedPointsto (swift.dfld d go!"active") a (DFrac.own qa) ∗ True) ∧
  (∀ d y, g.sr d y ⊢ g.so d y) ∧
  (∀ (d : Loc) (y : swift.CommandId) (q : Qp), g.sr d y ∗ ghostMapElem c0.γsh d (DFrac.own (1 : Qp).half) q ⊢
    (False : IProp netDistGF))

/-- **The concrete sequential owner state** (round 27, PROVISIONAL; `descDS_alloc`'s `g.so`): the
rest of a descriptor at home (`descHomeS` but for `sqC`'s shares). It only covers a new sequential
descriptor (its message sets as `msgSetFree`): the run loop's inline `handleMsg` (`seqSpecD`) needs
the owner's state (`descOwnF`, the sets with their handler) here, which `seqSpecD`'s proof is to
add (a disjunct, with its freeze to `descHomeS`). -/
def swift.soC (DR : Loc → IProp netDistGF) (MP : swift.CommandId → GoInterface → IProp netDistGF)
    (d : Loc) (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (m sc sl fa : Loc),
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ swift.bagW m (MP y) ∗
    swift.dfld d go!"stopChan" ↦ sc ∗
    swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
    swift.msgSetFree sl ∗ swift.msgSetFree fa ∗
    typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") true (DFrac.own (1 : Qp).half.half) ∗ DR d)

/-- **An incarnation's state** (round 26, D23 G8): `r = (k, d, live)`; live: the entry `k ↦ d`
is in the view and the owner (goroutine or the run loop's `seqStore`) holds the other half of
`γi`; retired (the owner removed `k`): the whole of `γi`. -/
def swift.incSt (γi : GName) (Mc : GMap GoString GoInterface) (r : GoString × Loc × Bool) :
    IProp netDistGF :=
  if r.2.2 then
    iprop(ghostVar γi (1 : Qp).half (r.1, r.2.1) ∗
      ⌜Mc !! r.1 = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.2.1)⌝)
  else ghostVar γi (1 : Qp) (r.1, r.2.1)

/-- **The committed incarnations** (round 26, D23 G8; replaces `K`): `γk`'s authority over the
incarnations committed to the view (a commit witness `ghostMapElem g.γk γi DFrac.discard true`
each), each one's state, and at most one live incarnation per key. -/
def swift.incInv (g : swift.DescG) (Mc : GMap GoString GoInterface) : IProp netDistGF :=
  iprop(∃ (I : GMap GName GName) (R : GName → GoString × Loc × Bool), ghostMapAuth g.γk 1 I ∗
    ([∗map] γi ↦ _b ∈ I, swift.incSt γi Mc (R γi)) ∗
    ⌜∀ i j, I !! i ≠ none → I !! j ≠ none → (R i).2.2 = true → (R j).2.2 = true →
      (R i).1 = (R j).1 → i = j⌝)

/-- A `cmdDescs` entry in the descriptors' invariant (see the file header; round 18): `v` is
the descriptor `d` of `y` (`k = str y`; round 23, D18 G6: no `descIs` record), and its state
`entS` (sequential states `sqC`), or lent
to `stopDescs` for one visit of its round (`stopDescs` reads `active` and `seq` with the state in
hand, under the shard's read lock, and puts it back when it signals). Round 37 (D37, table rev 8
G-lend): the lent state names the lender's pin (`γb`'s half at `some π`, half of the pin: the
locked `Remove` refutes it, `cmapLocked_pin_false`) and holds the round's element of `k` at
`false` (inserted by the lend: a stop request's half at `true` refutes it). -/
def swift.entW (γ : sp.Names) (g : swift.DescG) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (k : GoString) (v : GoInterface) :
    Option (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface) → Loc →
      swift.CommandId → IProp netDistGF
  | none, d, y => iprop(swift.entS γ DR Run (swift.sqE g) g.mp d y ∨
      ∃ π : github_com.orcaman.concurrent_map.PinD,
        ghostVar g.γb (1 : Qp).half (some π) ∗
        github_com.orcaman.concurrent_map.cmapPin g.γdc k v π.half ∗
        ghostMapElem g.γs k (DFrac.own 1) false)
  | some (t, ρ, v'), d, y => iprop(⌜v' = v⌝ ∗ swift.entL γ DR Run (swift.sqE g) g.mp g k v t ρ d y)

/-- (Round 38, table rev 9a §3R9.5: the entry's lock-lend state `o = W !! k`: `none`, whole or
read-lent; `some (t, ρ, v)`, lock-lent, `entL`.) -/
def swift.descEnt (γ : sp.Names) (γd : GName) (g : swift.DescG) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (str : swift.CommandId → GoString)
    (o : Option (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface))
    (k : GoString) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (d : Loc) (y : swift.CommandId),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y⌝ ∗
    swift.entW γ g DR Run k v o d y)

/-- The records of the descriptors' sub-pool's loans (round 18): each loan's holder is a
registered goroutine (a share of its `cntL` element; or of the run loop's flag). -/
def swift.loanRec (γn γlj : GName) (L : GMap Nat Qp) : IProp netDistGF :=
  iprop([∗map] i ↦ _q ∈ L, ∃ (j : Nat) (qj : Qp), ghostMapElem γn j (DFrac.own qj) false ∗
    ghostMapElem γlj i (DFrac.own (1 : Qp).half) (j, qj))

/-- **The ledger's half in the epoch** (round 34; table rev 5/6 §3.7, plan R5.2): `Out`'s
authority half (the other is `nodeInvD`'s) and, per key out of the store, the registry share its
receipt `outRcpt K (j, qj)` names (so no holder unregisters, and no freeze happens, while out). -/
def swift.ledgerD (γn γout : GName) : IProp netDistGF :=
  iprop(∃ Out : GMap (Nat × sp.CmdId) (Nat × Qp), ghostMapAuth γout (1 : Qp).half Out ∗
    [∗map] _K ↦ jq ∈ Out, ghostMapElem γn jq.1 (DFrac.own jq.2) false)

/-- **The receipts' authorities** (round 34; table rev 5 C1): `γlj`, keyed by the sub-pool's
loans; (round 35, table rev 7 §3.11, D36) `γj`, keyed by the incarnations, with no domain
constraint (a sequential creation leaves a stale key; keys are inserted only at names allocated
fresh for the map). -/
def swift.rcptAuth (g : swift.DescG) (L : GMap Nat Qp) : IProp netDistGF :=
  iprop(∃ LJ : GMap Nat (Nat × Qp), ghostMapAuth g.γlj 1 LJ ∗
    ⌜∀ i, LJ.lookup i ≠ none → L.lookup i ≠ none⌝ ∗
    ∃ J : GMap GName (Nat × Qp), ghostMapAuth g.γj 1 J)

/-- **The descriptors' invariant** (see the file header; round 18): until the run loop stops
the epoch (`γst`), the view `cmdDescs` with every entry's `descEnt`, the running goroutines'
keys `K` (each in the view), and the descriptors' epoch sub-pool with its loans' records.
Round 24: once stopped, the sub-pool's loan authority, empty (every loan came back): a
goroutine's own loan token then refutes `st = true` (`swift.loan_not_stopped`), its "epoch not
stopped" fact (it has no `γst` half). -/
def swift.descInv (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) : IProp netDistGF :=
  iprop(∃ st : Bool, ghostVar g.γst (1 : Qp).half st ∗
    if st then ghostMapAuth g.γq 1 (∅ : GMap Nat Qp) else
      ∃ (Mc : GMap GoString GoInterface) (q0 : Qp) (L : GMap Nat Qp) (dm1 : GoSlice)
        (W : GMap GoString (github_com.orcaman.concurrent_map.CmapLock × swift.LendK × GoInterface)),
        github_com.orcaman.concurrent_map.cmapView g.γdc Mc ∗
        ghostMapAuth g.γw 1 W ∗ ⌜∀ k, W !! k ≠ none → Mc !! k ≠ none⌝ ∗
        ([∗map] k ↦ v ∈ Mc, swift.descEnt γ γd g DR Run str (W !! k) k v) ∗
        swift.incInv g Mc ∗
        swift.epochPoolX ep g.ev (swift.descX ep.rp γd g dm1) g.Qd g.γq q0 L ∗
        swift.loanRec γn g.γlj L ∗
        swift.ledgerD γn γout ∗ swift.rcptAuth g L)

/-- **The descriptors' part of the run loop's invariant** (refines `swift.descState`; see the
file header; round 18: at the epoch's `g`, with `stopDescs`' authorities, empty between its
rounds; round 23, D18 G6: no `γd` records). -/
def swift.descStateR (γ : sp.Names) (rp : Loc) (x : swift.RunX) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (g : swift.DescG) : IProp netDistGF :=
  iprop(∃ dm1 : GoSlice,
    typedPointsto (swift.fld rp go!"cmdDescs") dm1 (DFrac.own (1 : Qp).half) ∗
    github_com.orcaman.concurrent_map.isCMapV dm1 g.γdc (swift.descR x.γd) ∗
    github_com.orcaman.concurrent_map.readerV dm1 g.γdc (swift.descR x.γd) ∗
    inv swift.descN (swift.descInv γ x.γd x.γn x.γout g (x.epN rp) DR Run x.str) ∗
    ghostVar g.γst (1 : Qp).half false ∗ swift.cntFrozen x.γn false ∗
    ghostMapAuth g.γs 1 (∅ : GMap GoString Bool) ∗
    ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ swift.seqStore g ∗
    inv swift.seqN (swift.seqInbox g))

/-- **A stored home's proposal facts** (round 58, D82 (1), (4); persistent; `descRestH`'s): `dep`'s
contents, and no proposal, or the proposal's `propIs` at `cmd`'s command `c` and, at `b`'s leader,
the replica's own prefix with `y` and `dep`'s contents as its dependencies (`repPre`'s
`ldrPrefix`). -/
def swift.homeP (γ : sp.Names) (N r b : Nat) (y : sp.CmdId) (p : Loc) (c : sp.Cmd) (dep : GoSlice) :
    IProp netDistGF :=
  iprop(∃ D : List swift.CommandId, dep ↦*□ D ∗
    (⌜p = null⌝ ∨ (swift.propIs γ p y c ∗
      (⌜r ≠ sp.leaderOf N b⌝ ∨ ∃ s : sp.Seq, sp.locLb γ r b s ∗
        ⌜(y, c) ∈ s ∧ (D.map toCmdId).Perm (sp.depsIn s y)⌝))))

instance swift.homeP_persistent (γ : sp.Names) (N r b : Nat) (y : sp.CmdId) (p : Loc) (c : sp.Cmd)
    (dep : GoSlice) : Persistent (swift.homeP γ N r b y p c dep) := by
  unfold swift.homeP sp.locLb; infer_instance

/-- `homeP` from the owner's `repPre` and `dep`'s contents (round 58). -/
theorem swift.repPre_homeP (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    swift.repPre γ N r b x dv ∗ dv.dep ↦*□ dv.D ⊢
      swift.homeP γ N r b (toCmdId x) dv.propose dv.c dv.dep := by
  iintro ⟨#H, #HD⟩
  iunfold swift.homeP
  iexists dv.D
  iframe HD
  iunfold swift.repPre at H
  icases H with (%Hn | ⟨-, -, #Hl, #HpI⟩)
  · ileft; ipureintro; exact Hn
  iright
  iframe HpI
  iunfold swift.ldrPrefix at Hl
  iexact Hl

/-- **A stopped descriptor's rest with its token stored** (round 35; table rev 5 C5, T19): as
`descRestA` but with half of `phase` and `dep` and three quarters of `propose` (the store's rest
record `rest d γi` holds the others). Round 58 (D82 (1), (4)): the claim's key `K` is `(b, y)` at
the epoch's ballot `b`, with the owner's `proposeDep` facts (`pdOk` at `b`, `y`) and its `cmd` tied
to its proposal (`propIs` of `y` at `cmd`'s command). -/
def swift.descRestH (γ : sp.Names) (sN : swift.StN) (γsh : GName) (b : Nat) (K : Nat × sp.CmdId)
    (d : Loc) : IProp netDistGF :=
  iprop(∃ (q : Qp) (ph sn : w64) (c : sp.Cmd) (vs dep hs pd sb : GoSlice) (p ap wa : Loc)
      (sl : Bool) (df : GoFunc),
    ghostMapElem γsh d (DFrac.own 1) q ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
    typedPointsto (swift.dfld d go!"phase") ph (DFrac.own (1 : Qp).half) ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk c.op c.key vs ∗ vs ↦*□ c.val ∗ ⌜c.op ≠ W8 3⌝ ∗
    typedPointsto (swift.dfld d go!"dep") dep (DFrac.own (1 : Qp).half) ∗
    swift.dfld d go!"hs" ↦ hs ∗ swift.dfld d go!"seqnum" ↦ sn ∗
    typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half.half) ∗
    swift.dfld d go!"proposeDep" ↦ pd ∗
    swift.dfld d go!"afterPropagate" ↦ ap ∗ swift.ocfAny ap ∗
    swift.dfld d go!"slowPath" ↦ sl ∗ swift.dfld d go!"defered" ↦ df ∗
    swift.dfld d go!"waitingAck" ↦ wa ∗ swift.dfld d go!"storedBallots" ↦ sb ∗
    ∃ (y : swift.CommandId) (c0 : swift.DC), swift.pdOk c0 b y pd hs sn ∗
      ⌜K = (b, toCmdId y) ∧ c0.γ = γ ∧ c0.N = sN.N ∧ c0.r = sN.r⌝ ∗
      swift.homeP γ sN.N sN.r b (toCmdId y) p c dep)

/-- **A tokenless descriptor's rest with its owner's facts** (round 57, D80 (4); `descRestS`'s
tokenless disjunct): `descRestA` at the values the owner left, with `propose` fixed at `null`
(`rowTokO`'s tokenless branch; a raw descriptor's `newDesc` value), `dep`'s contents read-only
(`dsl ↦*□ D`), and `proposeDep`'s facts (`pdOk`, at some ballot `b` and command `y`, over the
replica's names `γ`, `sn.N`, `sn.r`; with `hs` and `seqnum` the home's own fields). The pool's `DR`
stays `descRestA` (`swift.descRestT_A`). -/
def swift.descRestT (γ : sp.Names) (sn : swift.StN) (γsh : GName) (b : Nat) (d : Loc) :
    IProp netDistGF :=
  iprop(∃ (q : Qp) (ph sq : w64) (c : sp.Cmd) (vs dsl hs pd sb : GoSlice) (ap wa : Loc)
      (sl : Bool) (df : GoFunc) (D : List swift.CommandId),
    ghostMapElem γsh d (DFrac.own 1) q ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
    swift.dfld d go!"phase" ↦ ph ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk c.op c.key vs ∗ vs ↦*□ c.val ∗ ⌜c.op ≠ W8 3⌝ ∗
    swift.dfld d go!"dep" ↦ dsl ∗ dsl ↦*□ D ∗ swift.dfld d go!"hs" ↦ hs ∗
    swift.dfld d go!"seqnum" ↦ sq ∗
    swift.dfld d go!"propose" ↦ (null : Loc) ∗ swift.dfld d go!"proposeDep" ↦ pd ∗
    (⌜pd = slice.nil⌝ ∨ ∃ (c0 : swift.DC) (y : swift.CommandId) (γi : GName),
      swift.pdOk c0 b y pd hs sq ∗ ⌜c0.γ = γ ∧ c0.N = sn.N ∧ c0.r = sn.r⌝ ∗
      ghostVar γi (1 : Qp).half (sn.str y, d) ∗ swift.cgW sn.γcg b γi) ∗
    swift.dfld d go!"afterPropagate" ↦ ap ∗ swift.ocfAny ap ∗
    swift.dfld d go!"slowPath" ↦ sl ∗ swift.dfld d go!"defered" ↦ df ∗
    swift.dfld d go!"waitingAck" ↦ wa ∗ swift.dfld d go!"storedBallots" ↦ sb)

/-- **The rest of a descriptor at home** (round 35; table rev 5 C5, R4/R8): its fields whole
(no token: a sequential descriptor, or a goroutine stopped without one), or, its token stored at
T19, `descRestH` with the claim `rest d γi` on the store's record (the node invariant's name, so
that `handleSync`'s free (T23, `swift.descRestS_forget`, Store.lean) takes the record back). -/
def swift.descRestS (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat) (γsh : GName)
    (b : Nat) (d : Loc) : IProp netDistGF :=
  iprop(swift.descRestT γ sn γsh b d ∨
    (inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      ∃ (K : Nat × sp.CmdId) (γi : GName), swift.claimTok sn.γcl K (.rest d γi) ∗
        swift.descRestH γ sn γsh b K d))

/-- The descriptors' home rest of the replica `x` (round 35, C5). Round 58 (D82 (1)): indexed by
the epoch's ballot `b` (the home's `pdOk` and stored claim are of `b`). -/
abbrev swift.RunX.DR (x : swift.RunX) (γ : sp.Names) (b : Nat) : Loc → IProp netDistGF :=
  swift.descRestS γ x.γv x.γe x.γo x.sn x.k x.γsh b

/-- **The epoch `g` is registered in the epochs' map** (round 56, D79 (1), 52-3; persistent): `γcg`
has `g`'s ballot ↦ `g`'s commit-witness map `γk` (`swift.descDS_alloc`). An owner has it (`ownCtx`),
so its rest record names its incarnation's commit witness by ballot (`swift.cgW`); the stopped
epoch's facts (`swift.stopPS`) have it, so the report reads such a record against `incInv`. -/
def swift.cgG (x : swift.RunX) (g : swift.DescG) : IProp netDistGF :=
  ghostMapElem x.γcg (g.ev.b, false) DFrac.discard (some g.γk : Option GName)

instance swift.cgG_persistent (x : swift.RunX) (g : swift.DescG) : Persistent (swift.cgG x g) := by
  unfold swift.cgG; infer_instance

instance swift.cgG_timeless (x : swift.RunX) (g : swift.DescG) : Timeless (swift.cgG x g) := by
  unfold swift.cgG; infer_instance

/-- An owner's commit witness at its epoch's registration gives the rest record's `cgW`. -/
theorem swift.cgW_of (x : swift.RunX) (g : swift.DescG) (γi γsg : GName) :
    swift.cgG x g ∗ swift.incW g γi γsg ⊢ swift.cgW x.γcg g.ev.b γi := by
  iintro ⟨#Hg, #Hw⟩
  iunfold swift.cgW
  iexists g.γk, γsg
  iunfold swift.cgG at Hg
  iunfold swift.incW at Hw
  iframe Hg Hw

/-- A rest record's `cgW` at a registered epoch's ballot names that epoch's commit witness. -/
theorem swift.cgW_incW (x : swift.RunX) (g : swift.DescG) (γi : GName) :
    swift.cgW x.γcg g.ev.b γi ∗ swift.cgG x g ⊢ ∃ γsg, swift.incW g γi γsg := by
  iintro ⟨#Hw, #Hg⟩
  iunfold swift.cgW at Hw
  icases Hw with ⟨%γk, %γsg, #Hc, #Hk⟩
  iunfold swift.cgG at Hg
  ihave %he := ghostMapElem_agree (g.ev.b, false) x.γcg _ _ _ _ $$ Hc Hg
  obtain rfl : γk = g.γk := Option.some.inj he
  iexists γsg
  iunfold swift.incW
  iexact Hk

/-- **The stopped view's facts at the run loop's names** (round 53, D70 (3)(a), D73 (4); 51-2 (a),
lifecycle-table 11b.12): `epStopped`'s parameter `PS`. The stopped epoch's descriptors' commit
record `incInv g Mc` (`swift.descInv_take_frozen`'s, which StopDescsProof kept dropping) and every
key's command (`descEntH`'s `k = str y`, which `descsStopped`'s entries drop). Round B1 (D82 (4)):
and the stopped epoch's free permit (`swift.freeP`, unspent): the report holds it, `handleSync`
spends it before its free. -/
def swift.stopPS (x : swift.RunX) (c : Nat) (Mc : GMap GoString GoInterface) : IProp netDistGF :=
  iprop((▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
    swift.freeP x.γcg c ∗
    [∗map] k ↦ v ∈ Mc, ∃ (d : Loc) (y : swift.CommandId),
      ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = x.str y⌝)

theorem swift.descRestT_S (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γsh : GName) (b : Nat) (d : Loc) :
    swift.descRestT γ sn γsh b d ⊢ swift.descRestS γ γv γe γo sn k γsh b d := by
  iintro H
  iunfold swift.descRestS
  ileft; iexact H

/-- The tokenless home's facts forgotten (round 57): the pool's `descRestA`. -/
theorem swift.descRestT_A (γ : sp.Names) (sn : swift.StN) (γsh : GName) (b : Nat) (d : Loc) :
    swift.descRestT γ sn γsh b d ⊢ swift.descRestA γsh d := by
  iintro H
  iunfold swift.descRestT at H
  icases H with ⟨%q, %ph, %sq, %c, %vs, %dsl, %hs, %pd, %sb, %ap, %wa, %sl, %df, %D, Hsh, #Hmx,
    Hph, Hcmd, #Hvs, %Hop, Hdep, -, Hhs, Hsq, Hp, Hpd, -, Hap, Hocf, Hsl, Hdf, Hwa, Hsb⟩
  iunfold swift.descRestA
  iexists q, ph, sq, c, vs, dsl, hs, pd, sb, null, ap, wa, sl, df
  iframe
  iframe Hmx Hvs
  ipureintro; exact Hop

/-- **A raw descriptor's tokenless home** (round 57): `newDesc`'s values (`propose`, `dep`,
`proposeDep` nil) have the facts trivially. -/
theorem swift.descRestT_raw (γ : sp.Names) (sn : swift.StN) (γsh : GName) (b : Nat) (d : Loc) (q : Qp)
    (ph sq : w64) (c : sp.Cmd) (vs hs sb : GoSlice) (ap wa : Loc) (sl : Bool) (df : GoFunc)
    (hop : c.op ≠ W8 3) :
    ghostMapElem γsh d (DFrac.own 1) q ∗
      sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗
      swift.dfld d go!"phase" ↦ ph ∗
      swift.dfld d go!"cmd" ↦ state.Command.mk c.op c.key vs ∗ vs ↦*□ c.val ∗
      swift.dfld d go!"dep" ↦ slice.nil ∗ swift.dfld d go!"hs" ↦ hs ∗
      swift.dfld d go!"seqnum" ↦ sq ∗
      swift.dfld d go!"propose" ↦ (null : Loc) ∗ swift.dfld d go!"proposeDep" ↦ slice.nil ∗
      swift.dfld d go!"afterPropagate" ↦ ap ∗ swift.ocfAny ap ∗
      swift.dfld d go!"slowPath" ↦ sl ∗ swift.dfld d go!"defered" ↦ df ∗
      swift.dfld d go!"waitingAck" ↦ wa ∗ swift.dfld d go!"storedBallots" ↦ sb ⊢
    swift.descRestT γ sn γsh b d := by
  iintro ⟨Hsh, #Hmx, Hph, Hcmd, #Hvs, Hdep, Hhs, Hsq, Hp, Hpd, Hap, Hocf, Hsl, Hdf, Hwa, Hsb⟩
  ihave #Hn : (slice.nil ↦*□ ([] : List swift.CommandId) : IProp netDistGF) $$ []
  · iapply ownSlice_nil
  iunfold swift.descRestT
  iexists q, ph, sq, c, vs, slice.nil, hs, slice.nil, sb, ap, wa, sl, df, []
  iframe
  iframe Hmx Hvs Hn
  isplitr
  · ipureintro; exact hop
  ileft; ipureintro; rfl

end defs

section poolLaws
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-! ### Round 38 (P1): `msgs`' home ¾ and outer ¼ -/

theorem swift.qp_34_14 : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 :=
  Subtype.ext (by simp only [Qp.val_add, Qp.val_half, Qp.val_one]; grind)

theorem swift.pt_34_14 {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v w : V) :
    (typedPointsto (V := V) l v (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) ∗
      typedPointsto (V := V) l w (DFrac.own (1 : Qp).half.half) : IProp netDistGF) ⊢
    ⌜v = w⌝ ∗ typedPointsto (V := V) l v (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  subst h
  isplitr
  · ipureintro; rfl
  have hh := typedPointsto_frac_add (GF := netDistGF) (V := V) l v ((1 : Qp).half + (1 : Qp).half.half)
    (1 : Qp).half.half
  rw [swift.qp_34_14] at hh
  iapply hh.2
  iframe

theorem swift.pt_14_12 {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v w : V) :
    (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half.half) ∗
      typedPointsto (V := V) l w (DFrac.own (1 : Qp).half) : IProp netDistGF) ⊢
    ⌜v = w⌝ ∗ typedPointsto (V := V) l w (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  subst h
  isplitr
  · ipureintro; rfl
  iapply (typedPointsto_frac_add (GF := netDistGF) (V := V) l v (1 : Qp).half (1 : Qp).half.half).2
  iframe

theorem swift.pt_1_34 {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v : V) :
    (typedPointsto (V := V) l v (DFrac.own 1) : IProp netDistGF) ⊢
    typedPointsto (V := V) l v (DFrac.own ((1 : Qp).half + (1 : Qp).half.half)) ∗
      typedPointsto (V := V) l v (DFrac.own (1 : Qp).half.half) := by
  have hh := typedPointsto_frac_add (GF := netDistGF) (V := V) l v ((1 : Qp).half + (1 : Qp).half.half)
    (1 : Qp).half.half
  rw [swift.qp_34_14] at hh
  exact hh.1

/-! ### Round 38 (plan R9a.1): the generic pool's laws (copies of EpochPool's) -/

theorem swift.poolS_init (S : Qp → IProp netDistGF) (Q : Qp) :
    S Q ⊢ |==> ∃ γp, swift.poolS S Q γp Q ∅ := by
  iintro HQ
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Qp) with ⟨%γp, Ha⟩
  imodintro
  iexists γp
  unfold swift.poolS
  iframe
  iintro H -
  iexact H

/-- A pool at a name allocated beforehand (round 38: the descriptors' sub-pool's share mentions
the epoch's `DescG`, which names the pool). -/
theorem swift.poolS_init_at (S : Qp → IProp netDistGF) (Q : Qp) (γp : GName) :
    ghostMapAuth γp 1 (∅ : GMap Nat Qp) ∗ S Q ⊢ swift.poolS S Q γp Q ∅ := by
  iintro ⟨Ha, HQ⟩
  unfold swift.poolS
  iframe
  iintro H -
  iexact H

theorem swift.poolS_lend (S : Qp → IProp netDistGF) (hS : ∀ q1 q2, S (q1 + q2) ⊣⊢ S q1 ∗ S q2)
    (Q : Qp) (γp : GName) (q0 : Qp) (L : GMap Nat Qp) (i : Nat) (hi : L.lookup i = none) :
    swift.poolS S Q γp q0 L ⊢
      |==> (swift.poolS S Q γp q0.half (L.insert i q0.half) ∗ S q0.half ∗
        swift.epochLoan γp i q0.half) := by
  unfold swift.poolS swift.epochLoan
  iintro ⟨Ha, Hs, Hc⟩
  ihave Hnew := ghost_map_insert (GF := netDistGF) i q0.half hi $$ Ha
  imod Hnew with ⟨Ha, Hl⟩
  have hsplit := hS q0.half q0.half
  rw [Qp.half_add_half] at hsplit
  icases hsplit.1 $$ Hs with ⟨Hs1, Hs2⟩
  imodintro
  iframe Ha Hs1 Hl Hs2
  iintro Hq Hm
  icases (BigSepM.bigSepM_insert hi).1 $$ Hm with ⟨Hi, Hm⟩
  iapply Hc $$ [Hq Hi] Hm
  iapply hsplit.2
  iframe

theorem swift.poolS_return (S : Qp → IProp netDistGF) (hS : ∀ q1 q2, S (q1 + q2) ⊣⊢ S q1 ∗ S q2)
    (Q : Qp) (γp : GName) (q0 : Qp) (L : GMap Nat Qp) (i : Nat) (q : Qp) :
    swift.poolS S Q γp q0 L ∗ S q ∗ swift.epochLoan γp i q ⊢
      |==> swift.poolS S Q γp (q0 + q) (GMap.delete i L) := by
  unfold swift.poolS swift.epochLoan
  iintro ⟨⟨Ha, Hs, Hc⟩, Hq, Hl⟩
  ihave %Hlk := ghost_map_lookup $$ Ha Hl
  imod ghost_map_delete (GF := netDistGF) $$ Ha Hl with Ha
  imodintro
  iframe Ha
  isplitl [Hs Hq]
  · iapply (hS q0 q).2
    iframe
  iintro Hs Hm
  icases (hS q0 q).1 $$ Hs with ⟨Hs0, Hsq⟩
  iapply Hc $$ Hs0
  iapply (BigSepM.bigSepM_delete Hlk).2
  iframe

theorem swift.poolS_stopped (S : Qp → IProp netDistGF) (Q : Qp) (γp : GName) (q0 : Qp)
    (L : GMap Nat Qp) :
    swift.poolS S Q γp q0 L ∗ ([∗map] _i ↦ q ∈ L, S q) ⊢ S Q := by
  unfold swift.poolS
  iintro ⟨⟨-, Hs, Hc⟩, Hm⟩
  iapply Hc $$ Hs Hm

theorem swift.descX_split (rp : Loc) (γd : GName) (g : swift.DescG) (dm : GoSlice) (q1 q2 : Qp) :
    swift.descX rp γd g dm (q1 + q2) ⊣⊢ swift.descX rp γd g dm q1 ∗ swift.descX rp γd g dm q2 := by
  unfold swift.descX
  rw [swift.descK_add]
  constructor
  · iintro ⟨H, #Hc⟩
    icases (typedPointsto_frac_add _ _ _ _).1 $$ H with ⟨H1, H2⟩
    iframe H1 H2 Hc
  · iintro ⟨⟨H1, #Hc⟩, ⟨H2, -⟩⟩
    iframe Hc
    iapply (typedPointsto_frac_add _ _ _ _).2
    iframe

theorem swift.descX_Qd (rp : Loc) (γd : GName) (g : swift.DescG) (dm : GoSlice) :
    swift.descX rp γd g dm g.Qd ⊣⊢
      typedPointsto (swift.fld rp go!"cmdDescs") dm (DFrac.own (1 : Qp).half) ∗
        github_com.orcaman.concurrent_map.isCMapV dm g.γdc (swift.descR γd) := by
  unfold swift.descX
  rw [swift.descK_Qd]
  exact .rfl

theorem swift.epochShareX_split (n : swift.EpN) (v : swift.EpV) (X : Qp → IProp netDistGF)
    (hX : ∀ q1 q2, X (q1 + q2) ⊣⊢ X q1 ∗ X q2) (q1 q2 : Qp) :
    swift.epochShareX n v X (q1 + q2) ⊣⊢ swift.epochShareX n v X q1 ∗ swift.epochShareX n v X q2 := by
  unfold swift.epochShareX
  constructor
  · iintro ⟨H, Hx⟩
    icases (swift.epochShare_split n v q1 q2).1 $$ H with ⟨H1, H2⟩
    icases (hX q1 q2).1 $$ Hx with ⟨X1, X2⟩
    iframe
  · iintro ⟨⟨H1, X1⟩, ⟨H2, X2⟩⟩
    isplitl [H1 H2]
    · iapply (swift.epochShare_split n v q1 q2).2; iframe
    · iapply (hX q1 q2).2; iframe

/-- The descriptors' sub-pool share is fractional (round 38, R9-1). -/
theorem swift.epochShareDX_split (n : swift.EpN) (v : swift.EpV) (rp : Loc) (γd : GName)
    (g : swift.DescG) (dm : GoSlice) (q1 q2 : Qp) :
    swift.epochShareX n v (swift.descX rp γd g dm) (q1 + q2) ⊣⊢
      swift.epochShareX n v (swift.descX rp γd g dm) q1 ∗
        swift.epochShareX n v (swift.descX rp γd g dm) q2 :=
  swift.epochShareX_split n v _ (swift.descX_split rp γd g dm) q1 q2

end poolLaws

end Perennial.github_com.imdea_software.swiftpaxos
