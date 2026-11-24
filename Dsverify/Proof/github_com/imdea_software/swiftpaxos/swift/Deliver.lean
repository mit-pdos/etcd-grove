/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Deliver.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.deliver(desc, cmdId)` (swift.go; S3): the execution of a command by its descriptor's owner,
the internal spec and what it is stated over (notes/prove-swift.md §1.3; the swift group's,
not frozen).

**The execution record** (`execL`'s lock invariant; round 46: `swift.execLInvE`, DeliverE.lean,
which replaced this file's `execLInv`, as `descCtxE` replaced `descCtx` and `deliver.specE` the
old `deliver.specI`/`reply.specI`/`replyWit`): the commands executed in
the current epoch `bX`, in order, `X` (each with its command and the dependencies it was
executed after), the state machine's contents `σ = applyX X` at the `State` pointer of the
epoch, `execLog` with one entry per executed command, and the persistent facts of each entry
(`exEntOk`, round 33: the log entry, committed here in `bX` or the leader's own optimistic
execution with its acceptance or pre-acceptance, and at the leader G-ldr's fact; its
dependencies executed before it). Each entry is also a persistent fact `exAt γxm bX i e` (a monotone ghost
map, the record's authority under the lock): the reply's witness (`exLb`).

**`delivered`** (`swift.delivInv`, an invariant): its keys are the strings of commands of `X`
(`str`, `CommandId.String`'s function, injective). Under `execL`, `deliver`'s check
`delivered.Has(dep)` then says `dep ∈ X`. This needs the map's contents (the map's ghost view `cmapView γdl`)
read and written atomically: `swift.cmapHasV.spec`, `swift.cmapSetV.spec`, instances of the
cmap's strong specs over its ghost view `γdl` (`cmapView`; Proof/swift/CmapBridge.lean). `handleSync`'s removals keep `delivInv` (a removal only shrinks `M`); its
reset of `X` (a new epoch) needs `M = ∅` then (its business: the strong `IterCb`).
Removal mode (round 11, `swift.delivRm`): `delivInv` holds a half of the mirror `γrm`
(`none`, or `some (M, v, d)` in removal mode; the run loop holds the other half, `swift.rmTok`)
and, in removal mode, a half of `γxe` (so a `deliver` with its `epochRd` share and `execLInv`'s
half sees `rm = false`: `swift.delivX_noRm`). The steps: Proof/swift/SyncEpoch.lean.

**The epoch reader** (`swift.epochRd`): a descriptor goroutine's share of the epoch's fields
(`ballot`, the embedded replica's `State`, `repchan`) and of its ghost variables: the node
invariant's epoch (`epochTok`, DescNode.lean) and the execution record's (`γxe`: the record's
epoch and `State` pointer, half in `execLInv`).

**The descriptor's fields** (`swift.descF`): those `deliver` (and `repchan.reply`) uses, owned
by the descriptor's owner; its value slice and dependency slice are read-only (`↦*□`: the
state machine keeps the value slice of a put; `execLog` keeps the dependency slice).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescNode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ShInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/


/-- The state machine after executing `X` from the empty store (`state.execS`). -/
def swift.applyX (X : List swift.ExE) : w64 → Option (List w8) :=
  X.foldl (fun σ e => (state.execS e.2.1.op e.2.1.key e.2.1.val σ).1) (fun _ => none)

theorem swift.applyX_snoc (X : List swift.ExE) (e : swift.ExE) :
    swift.applyX (X ++ [e]) = (state.execS e.2.1.op e.2.1.key e.2.1.val (swift.applyX X)).1 := by
  unfold swift.applyX; rw [List.foldl_append]; rfl

/-- Every command of `X` was executed after its dependencies. -/
def swift.depsBefore (X : List swift.ExE) : Prop :=
  ∀ i e, X[i]? = some e → ∀ d ∈ e.2.2, d ∈ (X.take i).map Prod.fst

theorem swift.depsBefore_snoc (X : List swift.ExE) (e : swift.ExE) (h : swift.depsBefore X)
    (he : ∀ d ∈ e.2.2, d ∈ X.map Prod.fst) : swift.depsBefore (X ++ [e]) := by
  intro i e' hi d hd
  by_cases hlt : i < X.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (by omega)]
    exact h i e' hi d hd
  · have hi' : i = X.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; simp at this; omega
    subst hi'
    rw [List.getElem?_concat_length] at hi; cases hi
    rw [List.take_left]; exact he d hd

/-- `COMMIT` (defs.go). -/
def swift.phCOMMIT : w64 := W64 3


section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]


/-- Why an executed command could be executed (persistent): committed here in `b`, or the
leader's own (`optExec`). -/
def swift.exOk (γ : sp.Names) (N r b : Nat) (e : swift.ExE) : IProp netDistGF :=
  iprop(sp.committed γ r b (toCmdId e.1) ∨ ⌜r = sp.leaderOf N b⌝)


/-- **An execution-log entry's facts** (persistent; table rev 4/5 §3.7, D32's per-entry fact
with G-ldr, D33's `execW`): the log entry `es` is the record's entry `e` (its id, its command with
its value slice read-only, its dependency slice read-only at `e`'s dependencies); why it was
executed (committed here in `b` at `COMMIT`, or, at `b`'s leader, its own optimistic execution
at `ACCEPT` with `accepted` or at `PRE_ACCEPT` with the pre-acceptance of the executed `dep`);
and (G-ldr) at `b`'s leader the executed `dep` is the one this leader pre-accepted, or the
command is a sync command of `b`. -/
def swift.exEntOk (γ : sp.Names) (N r b : Nat) (e : swift.ExE) (es : swift.commandStaticDesc) :
    IProp netDistGF :=
  iprop(⌜es.cmdId' = e.1⌝ ∗
    (∃ vs : GoSlice, ⌜es.cmd' = state.Command.mk e.2.1.op e.2.1.key vs⌝ ∗ vs ↦*□ e.2.1.val) ∗
    es.dep' ↦*□ e.2.2 ∗
    ((⌜es.phase' = W64 3⌝ ∗ sp.committed γ r b (toCmdId e.1)) ∨
     (⌜r = sp.leaderOf N b⌝ ∗
       ((⌜es.phase' = W64 2⌝ ∗ sp.accepted γ r b (toCmdId e.1)) ∨
        (⌜es.phase' = W64 1⌝ ∗ sp.preacc γ r b (toCmdId e.1) (e.2.2.map toCmdId))))) ∗
    (⌜r ≠ sp.leaderOf N b⌝ ∨ sp.preacc γ r b (toCmdId e.1) (e.2.2.map toCmdId) ∨
      (⌜es.phase' = W64 3⌝ ∗ swift.syncIn γ b (toCmdId e.1))))

instance swift.exEntOk_persistent (γ : sp.Names) (N r b : Nat) (e : swift.ExE)
    (es : swift.commandStaticDesc) : Persistent (swift.exEntOk γ N r b e es) := by
  unfold swift.exEntOk; infer_instance

/-- **Why `deliver` may execute** (persistent; `deliver.specE`'s premise; table rev 4/5 §3.7):
no proposal (it returns), or not `b`'s leader or `COMMIT` (then it executes only at `COMMIT`,
with its commit fact), or `b`'s leader's own optimistic execution at `ACCEPT` (accepted) or
`PRE_ACCEPT` (pre-accepted with `dep`); and `depWhy` (G-ldr). -/
def swift.execWhy (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop((⌜dv.propose = null ∨ r ≠ sp.leaderOf N b ∨ dv.phase = swift.phCOMMIT⌝ ∨
      (⌜dv.phase = W64 2⌝ ∗ sp.accepted γ r b (toCmdId x)) ∨
      (⌜dv.phase = W64 1⌝ ∗ sp.preacc γ r b (toCmdId x) (dv.D.map toCmdId))) ∗
    swift.depWhy γ γxm N r b x dv)

instance swift.execWhy_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.execWhy γ γxm N r b x dv) := by
  unfold swift.execWhy; infer_instance

/-- The pure part of `delivInv`: `delivered`'s keys are strings of the record's commands, every
command of the record is in `delivered` unless the map is being emptied (`rm`: handleSync's
removal mode), and the record's ghost map holds the record at its epoch and nothing later. -/
def swift.delivOk (str : swift.CommandId → GoString) (M : GMap GoString GoInterface) (bX : Nat)
    (X : List swift.ExE) (Mx : GMap (Nat × Nat) swift.ExE) (rm : Bool) : Prop :=
  (∀ k v, M.lookup k = some v → ∃ e ∈ X, k = str e.1) ∧
  (rm = false → ∀ e ∈ X, (M.lookup (str e.1)).isSome) ∧
  (∀ i, Mx.lookup (bX, i) = X[i]?) ∧ (∀ b' i, bX < b' → Mx.lookup (b', i) = none)

/-- The mirror's value (round 11): `none` outside removal mode, `some (M, v, d)` in it (the
view of `delivered`; the value `v = (bX, stp)` of the record's epoch variable `γxe`: the
record's epoch and the `State` pointer; `d`: the record was reset, it is empty). -/
abbrev swift.RmV : Type := Option (GMap GoString GoInterface × (Nat × Loc) × Bool)

/-- `delivX`'s removal-mode part (round 11; handleSync). The mirror `γrm` (`swift.RmV`): the
run loop always holds half (`swift.rmTok`); `delivRm` holds the other half, `none` outside
removal mode, `some (M, v, d)` in it, so the run loop's half gives the mode, the view (empty at
the reset), the record's epoch `v.1` and, once reset (`d`), that the record is empty. In
removal mode also half of the record's epoch variable `γxe` at `v` (the run loop's share,
deposited with the pins: a `deliver` holding an `epochRd` share of `γxe` and `execLInv`'s half
then sees `rm = false`). -/
def swift.delivRm (γxe γrm : GName) (bX : Nat) (X : List swift.ExE)
    (M : GMap GoString GoInterface) (rm : Bool) : IProp netDistGF :=
  if rm then iprop(∃ (v : Nat × Loc) (d : Bool),
    ghostVar γrm (1 : Qp).half (some (M, v, d) : swift.RmV) ∗
    ghostVar γxe (1 : Qp).half v ∗ ⌜v.1 = bX ∧ (d = true → X = [])⌝)
  else iprop(ghostVar γrm (1 : Qp).half (none : swift.RmV))

/-- The run loop's half of the mirror (see `swift.delivRm`). -/
def swift.rmTok (γrm : GName) (o : swift.RmV) : IProp netDistGF :=
  ghostVar γrm (1 : Qp).half o

instance swift.delivRm_timeless (γxe γrm : GName) (bX : Nat) (X : List swift.ExE)
    (M : GMap GoString GoInterface) (rm : Bool) : Timeless (swift.delivRm γxe γrm bX X M rm) := by
  unfold swift.delivRm; cases rm <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- `delivInv`'s round-8 part (`acceptL`'s link and the executed commands' facts): the
accepted-map's epoch variable `γa` at half (`acceptInv` holds the other half), equal to the
record's epoch outside removal mode, and each executed command's `exOk` (persistent copies:
a `delivered` hit at a follower gives `committed`, what `depsAccepted` needs for N2); (round 11)
the removal-mode part `delivRm` over the view `M`. -/
def swift.delivX (γ : sp.Names) (N r : Nat) (γa γxe γrm : GName) (bX : Nat) (X : List swift.ExE)
    (M : GMap GoString GoInterface) (rm : Bool) : IProp netDistGF :=
  iprop(∃ bA : Nat, ghostVar γa (1 : Qp).half bA ∗ ([∗list] e ∈ X, swift.exOk γ N r bX e) ∗
    ⌜rm = false → bA = bX⌝ ∗ swift.delivRm γxe γrm bX X M rm)

instance swift.delivX_timeless (γ : sp.Names) (N r : Nat) (γa γxe γrm : GName) (bX : Nat)
    (X : List swift.ExE) (M : GMap GoString GoInterface) (rm : Bool) :
    Timeless (swift.delivX γ N r γa γxe γrm bX X M rm) := by
  unfold swift.delivX swift.exOk sp.committed; infer_instance

/-- **The frozen mode** (round 52, D71 (1); lifecycle-table 11b.11 T20z/T23z): outside it,
`delivInv`'s second quarter of the record's variable `γx` and second half of the record's map
authority `γxm`; in it (`fillNewLeaderAckN` runs: `swift.fzX`, NewLeaderDesc.lean, holds those
two), the run loop's half of the pins' variable `γxp`, so `γxp` is whole in `delivInv` and a
`deliver` (its pin) refutes the mode. With `execL`'s half of `γx`, `delivInv`'s top quarter and
this one, an append to `X` (or a reset) needs `γx` whole, so it is impossible in the frozen mode:
`X` stays the frozen one. The map's half lets the thaw tell the modes apart (the frozen holder's
half refutes this branch's). Round 55 (53-3'): in both modes the record's persistent prefix
`exLb γxm bX X` (a `delivered` hit at the record's epoch gives `exIn`, `swift.delivFz_exIn`). -/
def swift.delivFz (γx γxp γxm : GName) (bX : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) : IProp netDistGF :=
  iprop(swift.exLb γxm bX X ∗
    ((ghostVar γx (1 : Qp).half.half (bX, X) ∗ ghostMapAuth γxm (1 : Qp).half Mx) ∨
      ghostVar γxp (1 : Qp).half bX))

instance swift.delivFz_timeless (γx γxp γxm : GName) (bX : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) : Timeless (swift.delivFz γx γxp γxm bX X Mx) := by
  unfold swift.delivFz swift.exLb swift.exAt; infer_instance

/-- `delivered`'s contents against the record (see the file header; SWB-5): its keys are the
record's commands (`delivOk`), the record's ghost map (`γxm`'s authority: an entry `exAt` of
the record's epoch is in `X`), and the **epoch pins**' variable `γxp` at the record's epoch:
half of it (the readers hold the other half as pins, `epochPin`), or all of it in removal mode
(`rm`: `handleSync` empties the map with every pin back; then no pin exists); and (round 8)
`delivX`: the accepted map's epoch (`γa`), the executed commands' `exOk`. Round 52 (D71 (1)):
a quarter of `γx` and half of `γxm`'s authority here, the other quarter and half in `delivFz`
outside the frozen mode (`swift.delivFz_get`/`swift.delivFz_put` give the old halves back). -/
def swift.delivInv (γ : sp.Names) (N r : Nat) (γdl : GName) (γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) : IProp netDistGF :=
  iprop(∃ (M : GMap GoString GoInterface) (bX : Nat) (X : List swift.ExE)
      (Mx : GMap (Nat × Nat) swift.ExE) (rm : Bool),
    github_com.orcaman.concurrent_map.cmapView γdl M ∗ ghostVar γx (1 : Qp).half.half (bX, X) ∗
    ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗ ghostMapAuth γxm (1 : Qp).half Mx ∗
    (swift.delivX γ N r γa γxe γrm bX X M rm ∗ swift.delivFz γx γxp γxm bX X Mx) ∗
    ⌜swift.delivOk str M bX X Mx rm⌝)

/-- N2-loop: `acceptL`'s list `rechecks` of the waiting commands whose dependency the run loop
accepted (the run loop rechecks them at the end of its step, `drainRechecks`): an owned slice of
command ids, with no fact about them (a recheck is `getCmdDesc(w, "recheck", nil)`, whose spec
holds of any id). -/
def swift.recheckOwn (rp : Loc) : IProp netDistGF :=
  iprop(∃ (rk : GoSlice) (ids : List swift.CommandId),
    swift.fld rp go!"rechecks" ↦ rk ∗ rk ↦* ids ∗ ownSliceCap swift.CommandId rk (DFrac.own 1))

/-- `acceptL`'s lock invariant (round 8; `depsAccepted`, `markAccepted`, `handleSync`'s reset):
the maps `accepted` (each key accepted here in the map's epoch `bA`) and `waiting` (owned
slices), and half of the map's epoch variable `γa` (the other half in `delivInv`, equal to the
record's epoch outside removal mode: a descriptor's pin gives `bA = b`); N2-loop: the list
`rechecks` (`swift.recheckOwn`, ids only). -/
def swift.acceptInv (γ : sp.Names) (r : Nat) (rp : Loc) (γa : GName) : IProp netDistGF :=
  iprop(∃ (am wm : Loc) (A : GMap swift.CommandId Unit) (W : GMap swift.CommandId GoSlice)
      (bA : Nat),
    swift.fld rp go!"accepted" ↦ am ∗ am ↦$ A ∗ swift.fld rp go!"waiting" ↦ wm ∗ wm ↦$ W ∗
    ([∗map] _w ↦ sl ∈ W, ∃ ids : List swift.CommandId, sl ↦* ids ∗
      ownSliceCap swift.CommandId sl (DFrac.own 1)) ∗
    ghostVar γa (1 : Qp).half bA ∗
    □ (∀ d : swift.CommandId, ⌜(A !! d).isSome⌝ -∗ sp.accepted γ r bA (toCmdId d)) ∗
    swift.recheckOwn rp)

/-- An epoch pin of epoch `b`: a share of the pins' variable (the run loop's own while it runs
a sequential descriptor, or a descriptor goroutine's, lent with its epoch share). With
`delivInv`, `x` executed in `b` (`exIn`) is in `delivered` (SWB-5). -/
def swift.epochPin (γxp : GName) (b : Nat) : IProp netDistGF :=
  iprop(∃ q : Qp, ghostVar γxp q b)

/-- **An epoch pin at its fraction** (round 42, D50; table §3R11a 11a-1): the loan's pin at the
loan's `q`. An owner's pin lives in its `shOwnR` at the `q` of its epoch share; a helper that takes
the pin out of `shOwnR` takes and returns it at that `q`, so it goes back at the same fraction. -/
def swift.epochPinQ (γxp : GName) (q : Qp) (b : Nat) : IProp netDistGF :=
  ghostVar γxp q b

def swift.delivN : Namespace := ndot nroot "swiftpaxos.delivered"

/-- `delivInv` opens inside cmap's atomic updates (outside the cmap's own invariants). -/
theorem swift.delivN_sub : ↑swift.delivN ⊆ (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
  have h : ↑swift.delivN ## (↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
    unfold swift.delivN github_com.orcaman.concurrent_map.cmapN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨he, h'⟩⟩

/-- A descriptor goroutine's share of the epoch `b` (see the file header). -/
def swift.epochRd (γe γxe : GName) (rp rr : Loc) (q : Qp) (b : Nat) (bw : w32) (stp rcp : Loc) :
    IProp netDistGF :=
  iprop(typedPointsto (swift.fld rp go!"ballot") bw (DFrac.own q) ∗
    typedPointsto (replica.fld rr go!"State") stp (DFrac.own q) ∗
    typedPointsto (swift.fld rp go!"repchan") rcp (DFrac.own q) ∗
    swift.epochTok γe q (b, b) ∗ ghostVar γxe q (b, stp) ∗
    ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝)

/-- The descriptor's fields `deliver` uses (see the file header), with its message channel
(messages with `MP`) and its successors' lock. `propose`: half (round 10; the other half is the
`afterPropagate` condition's state, `swift.proposeHalf`). `hs`: half (round 14; the other half
is the owner's, `swift.descRest`: only the owner's proposal handling writes it). `seq`: a
quarter, `msgs`: half (round 23, D18 G4/G5: only `newDesc`/the spawn write them; the
descriptors' invariant keeps the rest: `entS` half of `seq`, a running goroutine's `descGo`
a quarter of `seq` and the other half of `msgs` with its bag, so the run loop reads them under
the shard lock). -/
def swift.descF (d : Loc) (γm : ChanNames) (MP : GoInterface → IProp netDistGF)
    (dv : swift.DescV) : IProp netDistGF :=
  iprop(swift.dfld d go!"phase" ↦ dv.phase ∗
    swift.dfld d go!"cmd" ↦ state.Command.mk dv.c.op dv.c.key dv.vs ∗ dv.vs ↦*□ dv.c.val ∗
    swift.dfld d go!"dep" ↦ dv.dep ∗ dv.dep ↦*□ dv.D ∗
    typedPointsto (swift.dfld d go!"hs") dv.hs (DFrac.own (1 : Qp).half) ∗ dv.hs ↦*□ dv.Hs ∗
    typedPointsto (swift.dfld d go!"propose") dv.propose (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") dv.seq (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"msgs") dv.msgs (DFrac.own (1 : Qp).half) ∗
    isChanBag γm dv.msgs MP ∗
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d) ∗ ⌜dv.c.op ≠ W8 3⌝)

/-- **An owned reader bundle of `delivered`** (round 25, SW4 / D21; the same as RunCtx's
`swift.runReader`): the field read-only and a reader bundle at its value. A descriptor's owner
holds it in `shOwn` (a goroutine's from its `cntL` slot, the run loop's inline calls lend its
own); `deliver`/`depsAccepted` take it (no `readerBorrowV`). -/
def swift.ownRdr (rp : Loc) (γdl : GName) : IProp netDistGF :=
  iprop(∃ dm : GoSlice, swift.fld rp go!"delivered" ↦□ dm ∗
    github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR)

instance swift.exOk_persistent (γ : sp.Names) (N r b : Nat) (e : swift.ExE) :
    Persistent (swift.exOk γ N r b e) := by unfold swift.exOk; infer_instance

/-- An epoch pin against `delivInv`'s share: not in removal mode, and the record's epoch is the
pin's. -/

/-- The delivered-commands invariant inside a node prophecy's invariant and the node invariant. -/
theorem swift.delivN_pE : ↑swift.delivN ⊆ ((⊤ \ ↑client.nodeProphN) \ ↑swift.nodeN : CoPset) := by
  unfold swift.delivN swift.nodeN client.nodeProphN
  solve_ndisj

theorem swift.epochPin_agree (γxp : GName) (b bX : Nat) (rm : Bool) :
    swift.epochPin γxp b ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ⊢
      swift.epochPin γxp b ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗
      ⌜rm = false ∧ bX = b⌝ := by
  unfold swift.epochPin
  iintro ⟨⟨%q, Hp⟩, Hd⟩
  ihave %Hv := ghostVar_valid_2 γxp b q bX _ $$ Hp Hd
  isplitl [Hp]
  · iexists q; iexact Hp
  iframe Hd
  ipureintro
  obtain ⟨hq, hb⟩ := Hv
  refine ⟨?_, hb.symm⟩
  cases rm
  · rfl
  · exfalso
    simp only [↓reduceIte, Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := q.2
    grind

/-- `epochPin_agree` at the pin's fraction (round 42, D50). -/
theorem swift.epochPinQ_agree (γxp : GName) (q : Qp) (b bX : Nat) (rm : Bool) :
    swift.epochPinQ γxp q b ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ⊢
      swift.epochPinQ γxp q b ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗
      ⌜rm = false ∧ bX = b⌝ := by
  unfold swift.epochPinQ
  iintro ⟨Hp, Hd⟩
  ihave %Hv := ghostVar_valid_2 γxp b q bX _ $$ Hp Hd
  iframe Hp Hd
  ipureintro
  obtain ⟨hq, hb⟩ := Hv
  refine ⟨?_, hb.symm⟩
  cases rm
  · rfl
  · exfalso
    simp only [↓reduceIte, Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := q.2
    grind

omit [swift.Assumptions] in
/-- **Out of the frozen mode** (round 52): a share `q` of the pins' variable (a pin, or the run
loop's half), or removal mode (`γxp` whole in `delivInv`), refutes the frozen branch of
`delivFz`; then its quarter of `γx` and half of `γxm` join `delivInv`'s into the halves. -/
theorem swift.delivFz_get (γx γxp γxm : GName) (bX : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) (rm : Bool) (P : IProp netDistGF)
    (hP : P ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗ ghostVar γxp (1 : Qp).half bX ⊢
      False) :
    P ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗
      ghostVar γx (1 : Qp).half.half (bX, X) ∗ ghostMapAuth γxm (1 : Qp).half Mx ∗
      swift.delivFz γx γxp γxm bX X Mx ⊢
    P ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗
      ghostVar γx (1 : Qp).half (bX, X) ∗ ghostMapAuth γxm 1 Mx ∗ swift.exLb γxm bX X := by
  iintro ⟨HP, Hp, Hx, HM, Hf⟩
  iunfold swift.delivFz at Hf
  icases Hf with ⟨#Hlb, (⟨Hx2, HM2⟩ | Hp2)⟩
  · iframe HP Hp Hlb
    isplitl [Hx Hx2]
    · iapply (ghostVar_split_half γx (1 : Qp).half (bX, X)).2; iframe
    · iapply (ghostMapAuth_halves γxm Mx).2; iframe
  · iexfalso
    iapply hP
    iframe

omit [swift.Assumptions] in
/-- Back into `delivInv`'s shape, outside the frozen mode (round 52). -/
theorem swift.delivFz_put (γx γxp γxm : GName) (bX : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) :
    ghostVar γx (1 : Qp).half (bX, X) ∗ ghostMapAuth γxm 1 Mx ∗ swift.exLb γxm bX X ⊢
      ghostVar γx (1 : Qp).half.half (bX, X) ∗ ghostMapAuth γxm (1 : Qp).half Mx ∗
      swift.delivFz γx γxp γxm bX X Mx := by
  iintro ⟨Hx, HM, #Hlb⟩
  icases (ghostVar_split_half γx (1 : Qp).half (bX, X)).1 $$ Hx with ⟨Hx1, Hx2⟩
  icases (ghostMapAuth_halves γxm Mx).1 $$ HM with ⟨HM1, HM2⟩
  iframe Hx1 HM1
  iunfold swift.delivFz
  iframe Hlb
  ileft; iframe

omit [swift.Assumptions] in
/-- A pin (`epochPinQ` at `q`) refutes the frozen mode (round 52; `swift.delivFz_get`'s `hP`). -/
theorem swift.pin_noFz (γxp : GName) (q : Qp) (b bX : Nat) (rm : Bool) :
    swift.epochPinQ γxp q b ∗ ghostVar γxp (if rm then 1 else (1 : Qp).half) bX ∗
      ghostVar γxp (1 : Qp).half bX ⊢ (False : IProp netDistGF) := by
  unfold swift.epochPinQ
  iintro ⟨Hq, Hp, Hp2⟩
  ihave %Hv1 := ghostVar_valid_2 γxp bX (if rm then 1 else (1 : Qp).half) bX (1 : Qp).half $$ Hp Hp2
  cases rm with
  | true =>
    exfalso
    have hq := Hv1.1
    simp only [↓reduceIte, Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := ((1 : Qp).half).2
    grind
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave H1 : ghostVar γxp 1 bX $$ [Hp Hp2]
    · iapply (ghostVar_split_half γxp 1 bX).2; iframe
    ihave %Hv := ghostVar_valid_2 γxp b q bX 1 $$ Hq H1
    exfalso
    have hq := Hv.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := q.2
    grind

omit [swift.Assumptions] in
/-- Removal mode (`γxp` whole in `delivInv`) refutes the frozen mode (round 52;
`swift.delivFz_get`'s `hP` at `rm = true`). -/
theorem swift.rm_noFz (γxp : GName) (bX : Nat) :
    (True : IProp netDistGF) ∗ ghostVar γxp (if true then 1 else (1 : Qp).half) bX ∗
      ghostVar γxp (1 : Qp).half bX ⊢ False := by
  iintro ⟨-, Hp, Hp2⟩
  simp only [↓reduceIte]
  ihave %Hv := ghostVar_valid_2 γxp bX 1 bX (1 : Qp).half $$ Hp Hp2
  exfalso
  have hq := Hv.1
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
  have := ((1 : Qp).half).2
  grind

omit [swift.Assumptions] in
/-- The empty record's prefix (round 55). -/
theorem swift.exLb_nil (γxm : GName) (b : Nat) : ⊢ swift.exLb γxm b [] := by
  unfold swift.exLb
  exact BigSepL.bigSepL_nil_intro

omit [swift.Assumptions] in
/-- An entry of the record's prefix was executed in its epoch (round 55, 53-3'). -/
theorem swift.exLb_exIn (γxm : GName) (b : Nat) (X : List swift.ExE) (e : swift.ExE)
    (h : e ∈ X) : swift.exLb γxm b X ⊢ swift.exIn γxm b e.1 := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem h
  have hX : l1 ++ e :: l2 = (l1 ++ [e]) ++ l2 := by simp
  unfold swift.exIn
  unfold swift.exLb
  rw [hX]
  iintro H
  ihave ⟨H1, -⟩ := (BigSepL.bigSepL_append (PROP := IProp netDistGF)).1 $$ H
  iexists l1, e
  iframe H1
  ipureintro; rfl

omit [swift.Assumptions] in
/-- **A `delivered` hit at the record's epoch is an execution in it** (round 55, 53-3'): with
`delivInv`'s contents (`delivOk`) and `delivFz`'s record prefix, a key `str x` of the view gives
`exIn γxm bX x` (`str` injective). -/
theorem swift.delivFz_exIn (str : swift.CommandId → GoString) (hinj : Function.Injective str)
    (γx γxp γxm : GName) (M : GMap GoString GoInterface) (bX : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) (rm : Bool) (hok : swift.delivOk str M bX X Mx rm)
    (x : swift.CommandId) (hx : (M.lookup (str x)).isSome) :
    swift.delivFz γx γxp γxm bX X Mx ⊢ swift.delivFz γx γxp γxm bX X Mx ∗ swift.exIn γxm bX x := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨e, he, hk⟩ := hok.1 _ v hv
  have hxe : x = e.1 := hinj hk
  subst hxe
  iintro H
  iunfold swift.delivFz at H
  icases H with ⟨#Hlb, H⟩
  isplitl [H]
  · iunfold swift.delivFz; iframe Hlb; iexact H
  iapply (swift.exLb_exIn γxm bX X e he)
  iexact Hlb

/-- The log's per-entry facts with one more entry (`deliver`'s append). -/
theorem swift.exEnts_snoc (γ : sp.Names) (N r b : Nat) (X : List swift.ExE)
    (es : List swift.commandStaticDesc) (e : swift.ExE) (en : swift.commandStaticDesc)
    (hl : es.length = X.length) :
    ([∗list] i ↦ e' ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOk γ N r b e' esi) ∗ swift.exEntOk γ N r b e en ⊢
      [∗list] i ↦ e' ∈ X ++ [e], ∃ esi : swift.commandStaticDesc, ⌜(es ++ [en])[i]? = some esi⌝ ∗
        swift.exEntOk γ N r b e' esi := by
  refine (sep_mono (BigSepL.bigSepL_mono ?_) ?_).trans BigSepL.bigSepL_snoc.2
  · intro k e' hk
    have hk' : k < es.length := by
      rw [hl]; exact (List.getElem?_eq_some_iff.mp hk).1
    iintro ⟨%esi, %h, H⟩
    iexists esi; iframe H; ipureintro
    rw [List.getElem?_append_left hk']; exact h
  · iintro H
    iexists en; iframe H; ipureintro
    rw [← hl]; simp

/-- `delivX` with one more executed command (`deliver`'s `Set`; not in removal mode, the view
changes freely). -/
theorem swift.delivX_snoc (γ : sp.Names) (N r : Nat) (γa γxe γrm : GName) (b : Nat)
    (X : List swift.ExE) (e : swift.ExE) (M M' : GMap GoString GoInterface) :
    swift.delivX γ N r γa γxe γrm b X M false ∗ swift.exOk γ N r b e ⊢
      swift.delivX γ N r γa γxe γrm b (X ++ [e]) M' false := by
  unfold swift.delivX swift.delivRm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro ⟨⟨%bA, Ha, HX, %h, Hm⟩, He⟩
  iexists bA
  iframe Ha Hm
  isplitl [HX He]
  · iapply BigSepL.bigSepL_snoc.2; iframe HX He
  ipureintro; exact h

/-- Not in removal mode while a share `q` of `γxe` (an `epochRd`) and `execLInv`'s half are
held (round 11: in removal mode `delivX` holds the remaining half). -/
theorem swift.delivX_noRm (γ : sp.Names) (N r : Nat) (γa γxe γrm : GName) (bX : Nat)
    (X : List swift.ExE) (M : GMap GoString GoInterface) (rm : Bool) (q : Qp) (v1 v2 : Nat × Loc) :
    ghostVar γxe q v1 ∗ ghostVar γxe (1 : Qp).half v2 ∗ swift.delivX γ N r γa γxe γrm bX X M rm ⊢
      ghostVar γxe q v1 ∗ ghostVar γxe (1 : Qp).half v2 ∗ swift.delivX γ N r γa γxe γrm bX X M rm ∗
      ⌜rm = false⌝ := by
  cases rm with
  | false => iintro ⟨H1, H2, H3⟩; iframe; ipureintro; rfl
  | true =>
    unfold swift.delivX swift.delivRm
    simp only [↓reduceIte]
    iintro ⟨H1, H2, ⟨%bA, Ha, HX, %h, %v, %d, Hm, H3, %hv⟩⟩
    icases ghostVar_valid_2 γxe v2 (1 : Qp).half v (1 : Qp).half $$ H2 H3 with %Hv
    obtain ⟨-, rfl⟩ := Hv
    ihave H23 : ghostVar γxe 1 v2 $$ [H2 H3]
    · iapply (ghostVar_split_half γxe 1 v2).2; iframe
    icases ghostVar_valid_2 γxe v1 q v2 1 $$ H1 H23 with %Hv2
    exfalso
    have hq := Hv2.1
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at hq
    have := q.2
    grind

/-- **SWB-5's link**: `x` executed in epoch `b` (`exIn`), with the record's epoch `b` (from an
epoch pin against `delivInv`'s share) and `delivInv`'s ghost map: `x` is in `delivered`. -/
theorem swift.exIn_delivered (str : swift.CommandId → GoString) (γxm : GName) (b : Nat)
    (x : swift.CommandId) (M : GMap GoString GoInterface) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) (hok : swift.delivOk str M b X Mx false) {qa : Qp} :
    swift.exIn γxm b x ∗ ghostMapAuth γxm qa Mx ⊢ ⌜(M.lookup (str x)).isSome⌝ := by
  unfold swift.exIn swift.exLb
  iintro ⟨⟨%X0, %e, Hlb, %He⟩, Ha⟩
  ihave ⟨-, He'⟩ := (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).1 $$ Hlb
  iunfold swift.exAt at He'
  ihave %Hl := ghost_map_lookup $$ Ha He'
  ipureintro
  have h1 := hok.2.2.1 X0.length
  rw [Hl] at h1
  have hmem : e ∈ X := List.mem_of_getElem? h1.symm
  have := hok.2.1 rfl e hmem
  rw [He] at this; exact this

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `cmdId.String()` (through a pointer, any fraction: round 10) is `str cmdId` (round 16:
`isPkgInit swift`, for `fmt.Sprintf`'s package; proved for `swift.cmdStr`, CmdStr.lean). -/
abbrev swift.CommandId.String.specS (str : swift.CommandId → GoString) : Prop :=
  ∀ (p : Loc) (dq : DFrac) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (typedPointsto p x dq : IProp netDistGF) }}
    (App (Val #(methods (go.GoType.PointerType swift.CommandId.ty) go!"String" #p)) (Val #()))
  {{ RET #(str x); typedPointsto p x dq }}

/-- `m.Has(key)` reads the map's contents (its ghost view `γdl`, cmap's `cmapView`) atomically
(HOCAP form: the caller's update `Q` at the linearization point, at the masks outside the
cmap's invariants). An instance of cmap's `ConcurrentMap.HasV.spec`
(`swift.cmapHasV_of`, Proof/swift/CmapBridge.lean). -/
abbrev swift.cmapHasV.spec (dm : GoSlice) (γdl : GName) :
    Prop :=
  ∀ (key : GoString) (E : CoPset) (Q : Bool → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.orcaman.concurrent_map ∗
      github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
      (|={⊤ \ ↑github_com.orcaman.concurrent_map.cmapN, E}=> ∃ M,
        github_com.orcaman.concurrent_map.cmapView γdl M ∗
        (github_com.orcaman.concurrent_map.cmapView γdl M
          ={E, ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN}=∗ Q (M.lookup key).isSome)) }}
    (App (Val #(methods github_com.orcaman.concurrent_map.ConcurrentMap.ty go!"Has" #dm))
      (Val #key))
  {{ (ok : Bool), RET #ok; github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
      Q ok }}

/-- `m.Set(key, v)` updates the contents atomically (an instance of cmap's
`ConcurrentMap.SetV.spec`: `swift.cmapSetV_of`). -/
abbrev swift.cmapSetV.spec (dm : GoSlice) (γdl : GName) :
    Prop :=
  ∀ (key : GoString) (v : GoInterface) (E : CoPset) (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.orcaman.concurrent_map ∗
      github_com.orcaman.concurrent_map.isCMapV dm γdl swift.deliveredR ∗
      (|={⊤ \ ↑github_com.orcaman.concurrent_map.cmapN, E}=> ∃ M,
        github_com.orcaman.concurrent_map.cmapView γdl M ∗
        (github_com.orcaman.concurrent_map.cmapView γdl (M.insert key v)
          ={E, ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN}=∗ Q)) }}
    (App (App (Val #(methods github_com.orcaman.concurrent_map.ConcurrentMap.ty go!"Set" #dm))
      (Val #key)) (Val #v))
  {{ RET #(); Q }}

/-- **The slot builder of an incarnation** (round 37, table rev 8b §3.15 K1; request SWC-2's
builder part): every history slot `s` in the history's bounds, once `x` executed in `b`, is a
message of the descriptor's channel. An owner keeps it in `descSt` (made at its first step, T8/T7s,
from `mpOk` and the incarnation's commit witness); `deliver` turns it into the reply goroutine's
builder (`reply.specE`). -/
def swift.slotB (MP : GoInterface → IProp netDistGF) (γxm : GName) (b : Nat) (x : swift.CommandId) :
    IProp netDistGF :=
  iprop(∀ s : w64, ⌜swift.slotIn s⌝ -∗ swift.exIn γxm b x -∗ MP (interface.mkOk go.int #s))

/-- **What a sequential descriptor's history slot does** (table rev 4/5 T15/T16, D3; the
handler's capability `slotCapR` instantiated at `deliver`'s frame): from the slot, the
descriptor's fields, `x` executed in `b`, and the frame `Rs`, the slot case retires the
descriptor and gives `Ret`. -/
def swift.slotOk (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (γxm : GName) (rp d : Loc)
    (b : Nat) (x : swift.CommandId) (dv : swift.DescV) (Rs Ret : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∀ s : w64,
    {{ MP (interface.mkOk go.int #s) ∗ swift.descF d γd MP dv ∗ ⌜dv.seq = true ∧ dv.propose ≠ null⌝ ∗
        swift.exIn γxm b x ∗ Rs }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
        (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #x))
    {{ RET #true; Ret }})

end specs

section rdr
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- **`delivered`'s reader at the replica's value as an owned reader** (round 42, table §3R11 T8,
gap 11-2): the persistent points-to at `dm` and a reader bundle at `dm`. -/
theorem swift.ownRdr_of (rp : Loc) (γdl : GName) (dm : GoSlice) :
    swift.fld rp go!"delivered" ↦□ dm ∗
      github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ⊢ swift.ownRdr rp γdl := by
  iintro ⟨#Hdm, Hrd⟩
  iunfold swift.ownRdr
  iexists dm
  iframe Hdm Hrd

/-- The owned reader at a known value of `delivered` (round 25, SW4): in the shape of the old
`readerBorrowV` borrow (`|={⊤}=> readerV ∗ (readerV ={⊤}=∗ _)`), giving the owned reader back. -/
theorem swift.ownRdr_take (rp : Loc) (γdl : GName) (dm : GoSlice) :
    swift.fld rp go!"delivered" ↦□ dm ∗ swift.ownRdr rp γdl ⊢
      |={⊤}=> github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
        (github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ={⊤}=∗
          swift.ownRdr rp γdl) := by
  iintro ⟨#Hdm, Hr⟩
  iunfold swift.ownRdr at Hr
  icases Hr with ⟨%dm', #Hdm', Hrd⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hdm Hdm'
  subst Heq
  imodintro
  iframe Hrd
  iintro Hrd
  imodintro
  iunfold swift.ownRdr
  iexists dm
  iframe Hdm Hrd

end rdr

end Perennial.github_com.imdea_software.swiftpaxos
