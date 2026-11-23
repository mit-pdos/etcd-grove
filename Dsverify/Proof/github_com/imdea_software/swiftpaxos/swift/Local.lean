/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Local.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's **local invariant** (notes/prove-swift.md §1, §3, §9): what the run loop owns
(`swift.runSt`, class L of §1 and its share of class E), and how its Go values relate to its node's
protocol state `st : RState` (`swift.localOk`, pure). Internal to the swift group (not frozen).

The run loop's Go values are one record (`swift.RunV`); the model state is the replica's half of
`nodeSt γ k`. Between two run-loop steps (`run`'s `select` arms) the replica is in normal
operation (`handleNewLeader` returns only once an `MSync` was taken), so in the main loop
`ballot = cballot` and `status = NORMAL`; the recovery loop inside `handleNewLeader` keeps
`status = RECOVERING` and `ballot > cballot`.

`localOk`'s clauses, each with the step that needs it:
* `ballot`, `cballot`, `status` are the model's `ballot`, `cballot`, `normal` (every step);
* the model's sequence of `cballot` is the last `MSync`'s order, then `handled`
  (`handleProposal`: `upd_handle` appends to it; `fillNewLeaderAckN`: the report's order, F3);
* every command of that sequence is in `proposes` (`handleProposal`'s dedup gives
  `upd_handle`'s `x ∉ locAt`);
* the replica has no row of a ballot above `cballot` (`handleSync`: `upd_takeSync`'s
  "nothing in `b'`" for an `MSync` from a peer; the new leader's own row is passed by
  `handleNewLeaderAckNs` to `handleSync` directly). Round N3 (D65 (1)): no row at all, not only
  an empty sequence (`swift.LView.locAt_nil_of_rows`): `upd_computeSync` needs `b'`'s `MSync`
  unset, which `syncRows` gives from the absence of a row;
* its acceptances are of ballots up to `cballot` (`handleSync`: `upd_takeSync`'s `hacc`);
* the keys' `lightKeyInfo`s are `lkOf` along the sequence's commands (`getDepAndHashes`: the
  dependencies are the model's `lkDeps`, `upd_preaccept`'s `D = depsIn s y`);
* the sequence of `cballot` is duplicate-free (SWB-7: with its commands' registrations, it is
  shorter than `2^63 - 1`, `getDepAndHashes`'s premise; `handleProposal` appends a command not in
  it, `handleSync` takes `syncOrder M`, `sp.syncOrder_nodup`);
* the hash logs (`hlogOk`): nothing pending that was not handled, every handled command of the
  key pending or in the base; the leader's log is its own commands of the key, with no update
  (`getDepAndHashes`: `Append`'s path is `upd_preaccept`'s `P`);
* `ld`: `r` leads `cballot` (D56 N1-a: the hash logs follow `cballot`'s sequence, so
  `handleNewLeader` keeps `ld` when it moves `ballot` past `cballot`);
* `proposes` holds only commands of that sequence (round N3, D65 (2): with the clause above,
  exactly its commands; `fillNewLeaderAckN`'s report is then the sequence, the base first and
  the handled commands after it in their order, `upd_report`'s h7/h8).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeySpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: the Go values and their relation to the model -/

/-- `NORMAL` and `RECOVERING` (defs.go's `iota`) as the `status` field's values. -/
def swift.stNORMAL : w64 := 0
def swift.stRECOVERING : w64 := 1

/-- `lightKeyInfo` of key `k` along the commands `s` (each `add`ed in order): `(W, C)`. -/
def swift.lkOf (s : sp.Seq) (k : w64) : List swift.CommandId × List swift.CommandId :=
  s.foldl (fun (wc : List swift.CommandId × List swift.CommandId) p =>
    if p.2.key = k then swift.lki.addTo p.2.op (ofCmdId p.1) wc.1 wc.2 else wc) ([], [])

/-- The ids of key `k`'s commands in `s`, in order. -/
def swift.idsOfKey (s : sp.Seq) (k : w64) : List sp.CmdId :=
  (s.filter (fun p => p.2.key == k)).map Prod.fst

/-- A hash log of key `k` against the commands `hd` the replica handled since its last `MSync`
(see the file header). `ld`: the replica is its ballot's leader. Change log C22 (M3, round 19):
`K`, ids whose saved update is harmless (the proposals in `proposes`: never appended again);
`Λ k s P`: the ballot's leader numbered a command of key `k` with `s`, its path is `P`
(`swift.ldSound`): the log's synced prefix is such a path (or none). -/
def swift.hlogOk (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (k : w64) (σ : swift.hlog.HL) : Prop :=
  (∀ z ∈ σ.pending, z ∈ swift.idsOfKey hd k) ∧
  (∀ z ∈ swift.idsOfKey hd k, z ∈ σ.pending ∨ z ∈ σ.base) ∧
  (∀ x, (σ.upd x).isSome → x ∈ hd.map Prod.fst ∨ K x) ∧
  (ld = true → σ.base = [] ∧ σ.pending = swift.idsOfKey hd k ∧ ∀ x, σ.upd x = none) ∧
  ((sint.Z σ.synced < 0 ∧ σ.base = []) ∨ Λ k σ.synced σ.base)

/-- The ids in `proposes` (`hlogOk`'s `K`). -/
def swift.propsK (pM : GMap swift.CommandId Loc) (y : sp.CmdId) : Prop := (pM !! ofCmdId y).isSome

/-- The run loop's Go values. -/
structure swift.RunV where
  ballot : w32
  cballot : w32
  status : w64
  /-- `handled`: the slice and its contents -/
  hdSl : GoSlice
  handled : List swift.CommandId
  /-- `proposes`: the map and its contents -/
  props : Loc
  propsM : GMap swift.CommandId Loc
  /-- `keys` -/
  keys : Loc
  keysM : GMap w64 GoInterface
  /-- `hlog` -/
  hlog : Loc
  hlogM : GMap w64 Loc
  /-- `pendingHashUpds` -/
  pend : Loc
  pendM : GMap swift.CommandId Loc
  /-- `lastSync` -/
  lastSync : Loc

/-- What the run loop knows exactly of its node's protocol state (it alone changes these
fields): `ballot`, `cballot`, `normal` and the sequences `locR`. The descriptors' steps
(pre-accept, accept, commit) change the other rows (`nodeInv`). -/
abbrev swift.LView := Nat × Nat × Bool × List (Nat × List sp.CmdId)

def swift.viewOf (st : sp.RState) : swift.LView := (st.ballot, st.cballot, st.normal, st.locR)

/-- The view's sequence of ballot `b` (`RState.locAt`'s). -/
def swift.LView.locAt (w : swift.LView) (b : Nat) : List sp.CmdId :=
  ((w.2.2.2.find? (·.1 == b)).map Prod.snd).getD []

theorem swift.viewOf_locAt (st : sp.RState) (b : Nat) : (swift.viewOf st).locAt b = st.locAt b := rfl

/-- No row of `b` in the view: its sequence of `b` is empty (round N3). -/
theorem swift.LView.locAt_nil_of_rows {w : swift.LView} {b : Nat} (h : ∀ o, (b, o) ∉ w.2.2.2) :
    w.locAt b = [] := by
  unfold swift.LView.locAt
  rw [List.find?_eq_none.mpr (fun p hp => by
    intro e; apply h p.2; have := beq_iff_eq.mp e; rw [← this]; exact hp)]
  rfl

/-- The relation of the run loop's values `v` (its last `MSync` `M`, `none` before any) to the
replica `r`'s view `w` of its protocol state (see the file header); `ld`: `r` leads `w`'s
`cballot` (`w.2.1`, the ballot whose sequence the hash logs follow; in normal operation
`w.2.1 = w.1`; D56 N1-a). -/
def swift.localOk (N r : Nat) (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg)
    (w : swift.LView) : Prop :=
  0 ≤ sint.Z v.ballot ∧ 0 ≤ sint.Z v.cballot ∧
  w.1 = sp.bal v.ballot ∧ w.2.1 = sp.bal v.cballot ∧
  (w.2.2.1 = true ↔ v.status = swift.stNORMAL) ∧
  (w.2.2.1 = true → w.2.1 = w.1) ∧
  (M = none ↔ w.2.1 = 0) ∧
  w.locAt w.2.1 = (M.map sp.syncOrder).getD [] ++ v.handled.map toCmdId ∧
  (∀ y ∈ w.locAt w.2.1, (v.propsM !! ofCmdId y).isSome) ∧
  (∀ b o, w.2.1 < b → (b, o) ∉ w.2.2.2) ∧
  (ld = true ↔ sp.leaderOf N w.2.1 = r) ∧
  (w.locAt w.2.1).Nodup ∧
  (∀ y, (v.propsM !! ofCmdId y).isSome → y ∈ w.locAt w.2.1)

/-! ## Pure: the order of an `MSync` is duplicate-free (moved from SyncStepD.lean, SWB-7) -/

theorem sp.recOrderStep_nodup (k : sp.Kept) (ids P : List sp.CmdId) (h : P.Nodup) :
    (sp.recOrderStep k ids P).Nodup := by
  unfold sp.recOrderStep
  dsimp only
  split
  · rename_i c _ hc
    have := (List.mem_filter.mp (List.mem_of_find?_eq_some hc)).2
    simp only [decide_eq_true_eq] at this
    exact List.nodup_append.mpr ⟨h, by simp, fun a ha b hb => by
      simp at hb; subst hb; intro e; subst e; exact this ha⟩
  · rename_i c _ hc
    have := (List.mem_filter.mp (List.mem_of_mem_head? hc)).2
    simp only [decide_eq_true_eq] at this
    exact List.nodup_append.mpr ⟨h, by simp, fun a ha b hb => by
      simp at hb; subst hb; intro e; subst e; exact this ha⟩
  · exact h

theorem sp.recOrder_nodup (k : sp.Kept) (ids : List sp.CmdId) : (sp.recOrder k ids).Nodup := by
  rw [sp.recOrder_eq]
  generalize ids.length = n
  suffices ∀ n P, P.Nodup → (sp.iter (sp.recOrderStep k ids) n P).Nodup from this n [] List.nodup_nil
  intro n
  induction n with
  | zero => intro P h; exact h
  | succ n ih => intro P h; exact ih _ (sp.recOrderStep_nodup k ids P h)

theorem sp.syncOrder_nodup (M : sp.SyncMsg) : (sp.syncOrder M).Nodup := sp.recOrder_nodup _ _

/-! ## The run loop's resources -/

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- A proposal the run loop keeps in `proposes` (or sends to a descriptor): `proposeP`'s contents
(replica/Defs.lean), all read-only (D16: a `GPropose`/`Propose` is never written once sent, so
the run loop and the descriptors share it as a persistent fact; the value slice `↦*□`, SWB-1);
the `Propose`'s address is not null. -/
def swift.propIs (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c : sp.Cmd) : IProp netDistGF :=
  iprop(∃ (p w mu : Loc) (addr : GoString) (ts : w64) (vs : GoSlice),
    gp ↦□ replica.defs.GPropose.mk p w mu false addr ∗
    p ↦□ replica.defs.Propose.mk x.seq x.cl (state.Command.mk c.op c.key vs) ts ∗
    vs ↦*□ c.val ∗ sp.cmdIs γ x c ∗ ⌜c.wf ∧ p ≠ null⌝)

instance swift.propIs_persistent (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c : sp.Cmd) :
    Persistent (swift.propIs γ gp x c) := by
  unfold swift.propIs; infer_instance

/-- Key `k`'s entry `ki` of `keys` along `s`: a `*lightKeyInfo` with `lkOf s k`. -/
def swift.keyEnt (s : sp.Seq) (k : w64) (ki : GoInterface) : IProp netDistGF :=
  iprop(∃ kl : Loc, ⌜ki = interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩⌝ ∗
    swift.lki.lkiOwn kl (swift.lkOf s k).1 (swift.lkOf s k).2)

/-- Key `k`'s hash log at `l`, `hlogOk` against `hd` (`K`, `Λ`: change log C22). -/
def swift.hlogEnt (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (k : w64) (l : Loc) : IProp netDistGF :=
  iprop(∃ σ, swift.hlog.ownHashLog l σ ∗ ⌜swift.hlogOk ld hd K Λ k σ⌝)

/-- The keys' `lightKeyInfo`s along the sequence `s` (`keys ↦$ km`); a key without one has no
command in `s` (round 7: `getDepAndHashes` creates a fresh one for it; the same fact as
HandleSync.lean's `keysIn`). -/
def swift.keysOwn (km : Loc) (kM : GMap w64 GoInterface) (s : sp.Seq) : IProp netDistGF :=
  iprop(km ↦$ kM ∗ ([∗map] k ↦ ki ∈ kM, swift.keyEnt s k ki) ∗
    ⌜∀ k, kM !! k = none → swift.lkOf s k = ([], [])⌝)

/-- The hash logs (`hlog ↦$ hm`), each `hlogOk` against `hd`; a key without one has no command
in `hd` (round 7, as `keysOwn`). -/
def swift.hlogOwn (hm : Loc) (hM : GMap w64 Loc) (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) : IProp netDistGF :=
  iprop(hm ↦$ hM ∗ ([∗map] k ↦ l ∈ hM, swift.hlogEnt ld hd K Λ k l) ∗
    ⌜∀ k, hM !! k = none → swift.idsOfKey hd k = []⌝)

/-- What `hlogOk`'s `Λ` says (change log C22, M3): each entry is ballot `b`'s leader `L`'s
number and path of a command of the key. -/
def swift.ldSound (γ : sp.Names) (L b : Nat) (Λ : w64 → w64 → List sp.CmdId → Prop) :
    IProp netDistGF :=
  iprop(□ ∀ (k s : w64) (P : List sp.CmdId), ⌜Λ k s P⌝ -∗ ∃ (y : sp.CmdId) (c : sp.Cmd),
    sp.numIs γ L b y s ∗ sp.pathIs γ L b y P ∗ sp.cmdIs γ y c ∗ ⌜c.key = k⌝)

/-- `pendingHashUpds`: the leader's acknowledgements of commands not yet proposed here
(read-only entries; round 18/19, change log C22: each with its hash slice, the hash's path and
the leader's number and path of the command in ballot `b`). -/
def swift.pendOwnH (γ : sp.Names) (L b : Nat) (pm : Loc) (pM : GMap swift.CommandId Loc) :
    IProp netDistGF :=
  iprop(pm ↦$ pM ∗ [∗map] x ↦ u ∈ pM, ∃ (sl : GoSlice) (sq : w64) (H : swift.SHash)
    (P : List sp.CmdId), u ↦□ swift.UpdateEntry.mk sl sq ∗ sl ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
    sp.numIs γ L b (toCmdId x) sq ∗ sp.pathIs γ L b (toCmdId x) P)

/-- `proposes`: each entry its proposal (read-only, D16). -/
def swift.propsOwn (γ : sp.Names) (pm : Loc) (pM : GMap swift.CommandId Loc) : IProp netDistGF :=
  iprop(pm ↦$ pM ∗ [∗map] x ↦ gp ∈ pM, ∃ c, swift.propIs γ gp (toCmdId x) c)

/-- The last `MSync` `M` (persistent: the run loop and the descriptors only read it). Round N5
(D72 (3)): with its maps (`swift.syncMaps`, RecDefs.lean, what `handleSync` had when it stored
`lastSync`), which `fillNewLeaderAckN` reads. Round N7 (D78, `I1: base locLb`): with the
ballot's leader's `locLb` of the `MSync`'s sequence (`msgOk (.sync)`'s, or the leader's own from
`computeSync_stepD`; `handleSync`'s pre carries it), the base entries' witness in
`fillNewLeaderAckN`. -/
def swift.syncObj (γ : sp.Names) (N : Nat) (ls : Loc) (b : Nat) (M : Option sp.SyncMsg) :
    IProp netDistGF :=
  match M with
  | none => iprop(⌜ls = null⌝)
  | some M => iprop(∃ (ph cm dp : Loc) (rep bl : w32), ls ↦□ swift.MSync.mk rep bl ph cm dp ∗
      ⌜sp.bal bl = b⌝ ∗ sp.syncIs γ b M ∗ swift.syncMaps ls b M ∗
      sp.locLb γ (sp.leaderOf N b) b (sp.syncSeq M))

/-- The replica's node state, shared by its run loop and its descriptors' goroutines (each
step opens it, with one `upd_*` of Steps.lean): the replica's half of `nodeSt`, the half of the
run loop's view `γv` (the run loop holds the other half), and what the run loop's steps need of
the descriptors' rows: acceptances only up to `cballot` (`upd_takeSync`'s `hacc`). -/
def swift.nodeInv (γ : sp.Names) (γv : GName) (k : Nat) : IProp netDistGF :=
  iprop(∃ st : sp.RState, sp.nodeSt γ k (1 : Qp).half st ∗
    ghostVar γv (1 : Qp).half (swift.viewOf st) ∗
    ⌜∀ b x, (b, x) ∈ st.accR → b ≤ st.cballot⌝)

/-- **The run loop's state** of replica `r` (node `k`) at `rp` (see the file header): its
class-L fields, its share of class E (`ballot` at a quarter: `ballotL` holds a quarter, the
readers the half; `status` at a half), its half of the view `w` of its node state, and
`localOk`, and its sequence of `cballot` as a `locLb`: the base `bs` (the last `MSync`'s
order with its commands), then the handled commands `hd` (`v.handled` with their commands). -/
def swift.runSt (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool) (v : swift.RunV)
    (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) : IProp netDistGF :=
  iprop(typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
    swift.fld rp go!"cballot" ↦ v.cballot ∗
    typedPointsto (swift.fld rp go!"status") v.status (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"handled" ↦ v.hdSl ∗ v.hdSl ↦* v.handled ∗
      ownSliceCap swift.CommandId v.hdSl (DFrac.own 1) ∗
    swift.fld rp go!"proposes" ↦ v.props ∗ swift.propsOwn γ v.props v.propsM ∗
    swift.fld rp go!"keys" ↦ v.keys ∗
      swift.keysOwn v.keys v.keysM (bs ++ hd) ∗
    swift.fld rp go!"hlog" ↦ v.hlog ∗
      (∃ Λ, swift.hlogOwn v.hlog v.hlogM ld hd (swift.propsK v.propsM) Λ ∗
        swift.ldSound γ (sp.leaderOf N w.2.1) w.2.1 Λ) ∗
    swift.fld rp go!"pendingHashUpds" ↦ v.pend ∗
      swift.pendOwnH γ (sp.leaderOf N w.2.1) w.2.1 v.pend v.pendM ∗
    swift.fld rp go!"lastSync" ↦ v.lastSync ∗ swift.syncObj γ N v.lastSync w.2.1 M ∗
    ghostVar γv (1 : Qp).half w ∗ sp.locLb γ r w.2.1 (bs ++ hd) ∗
    ⌜swift.localOk N r ld v M w ∧ hd.map Prod.fst = v.handled.map toCmdId ∧
      bs.map Prod.fst = (M.map sp.syncOrder).getD []⌝)

end defs

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The replica's node invariant's namespace (disjoint from `spN`). -/
def swift.nodeN : Namespace := ndot nroot "swiftpaxos.node"

theorem swift.nodeN_spN : ↑swift.nodeN ## (↑sp.spN : CoPset) := by
  unfold swift.nodeN sp.spN
  exact ndot_ne_disjoint nroot (by decide)

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- **A run-loop step on the node state**: the run loop, with its half of the view `w`, runs
a step `f` (one `upd_*`, given as `Hstep` over the node's half) that takes every state of view
`w` to view `w'` and keeps the acceptances' bound; its view becomes `w'`. -/
theorem swift.run_upd (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (γ : sp.Names) (γv : GName) (k : Nat)
    (w w' : swift.LView) (f : sp.RState → sp.RState) (Q : IProp netDistGF)
    (hw : ∀ st, swift.viewOf st = w → swift.viewOf (f st) = w')
    (hacc : ∀ st, swift.viewOf st = w → (∀ b x, (b, x) ∈ st.accR → b ≤ st.cballot) →
      ∀ b x, (b, x) ∈ (f st).accR → b ≤ (f st).cballot) :
    inv swift.nodeN (swift.nodeInv γ γv k) ∗ ghostVar γv (1 : Qp).half w ∗
      (∀ st, ⌜swift.viewOf st = w⌝ -∗ sp.nodeSt γ k (1 : Qp).half st ={E \ ↑swift.nodeN}=∗
        sp.nodeSt γ k (1 : Qp).half (f st) ∗ Q) ⊢
    |={E}=> ghostVar γv (1 : Qp).half w' ∗ Q := by
  iintro ⟨#Hinv, Hw, Hstep⟩
  iinv Hinv with Hi Hclose
  iunfold swift.nodeInv at Hi
  imod Hi
  icases Hi with ⟨%st, Hst, Hw2, %Hacc⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  imod Hstep $$ %st %Heq.symm Hst with ⟨Hst, HQ⟩
  imod ghostVar_update_halves w' γv w (swift.viewOf st) $$ Hw Hw2 with ⟨Hw, Hw2⟩
  imod Hclose $$ [Hst Hw2] with -
  · inext
    iunfold swift.nodeInv
    iexists f st
    iframe Hst
    isplitl [Hw2]
    · rw [hw st Heq.symm]; iexact Hw2
    · ipureintro; exact hacc st Heq.symm Hacc
  imodintro
  iframe

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section inst
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

-- (moved from SyncSpecs.lean, round N5: `syncObj` carries `syncMaps`)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.syncMaps_persistent (ls : Loc) (b : Nat) (M : sp.SyncMsg) :
    Persistent (swift.syncMaps ls b M) := by
  unfold swift.syncMaps; infer_instance

instance swift.syncObj_persistent (γ : sp.Names) (N : Nat) (ls : Loc) (b : Nat)
    (M : Option sp.SyncMsg) : Persistent (swift.syncObj γ N ls b M) := by
  cases M <;> unfold swift.syncObj <;> infer_instance

end inst

end Perennial.github_com.imdea_software.swiftpaxos
