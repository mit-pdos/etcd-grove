/-
Lean-first (no Rocq counterpart). #33 parity B2, statements (round 1: nothing proves these statements yet;
`notes/antithesis-parity-design.md` §3.5, §4; the vocabulary is `HarnessDur.lean`'s).
**Staging: the B2 statements of the functions whose B1 spec changes** (round 1). Each `<F>.specB2` is
the future `<F>.spec` (its own file's), stated here beside the B1 spec, which keeps its B1 proof until
B2's replaces it; this module goes then.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **`RunCluster(cfg, mode)` under B2's mask** (`RunCluster.spec`'s text at `b2Scope`). -/
abbrev RunCluster.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], antRunFits GF →
  ∀ (cfg : H.Config) (mode : H.Mode), CfgOk cfg → InScope b2Scope mode →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      threadTok }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster)) (Val #cfg)) (Val #mode))
  {{ (c : Loc), RET #c; runOver c b2Scope ∗ threadTok }}

/-- **`(*Cluster).spawn(f)` with a resource back** (`Cluster.spawn.spec`'s, the goroutine's `Q`
given back through `behWg.Done`: the restarter returns its `restarterOwn`). -/
abbrev Cluster.spawn.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (f : GoFunc) (k : w32) (P Q : IProp GF), sint.Z k < 2 ^ 31 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) k P ∗ threadTok ∗
      (threadTok -∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ threadTok ∗ Q }}) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"spawn")) (Val #f))
  {{ RET #(); sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) (k + W32 1) iprop(P ∗ Q) ∗ threadTok }}

/-- **`(*Cluster).run(n)` under B2**: node `j`'s goroutine from `down` (fresh, or killed: a restart);
it ends at the stop, or dead: then its `RawNode` vacated (raft's vacate law), its state deposited in
the `mu` lock (`down[j] = true`, `downInvB2`); either way `nodesWg.Done()` with its shares
(`nodeDoneB2`). -/
abbrev Cluster.run.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (ns : List Loc)
    (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ clusterRO c ns γ.mode ∗ ⌜ns[j.val]? = some n⌝ ∗ nodeOwnB2 c γ j n v .down ∗
      netAdder c γ.toAntNames q ∗ runLive γ q ∗ threadTok ∗ nodeDoneB2 c γ q ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"run")) (Val #n))
  {{ RET #(); threadTok }}

/-- **`(*Cluster).handle(n, inp)` under B2**: B1's kinds, and `inFlush` (`flush`), `inWork` (`work`),
`inKill` (dead now, or a fuse of 1 to 6 reports). -/
abbrev Cluster.handle.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (inp : H.input) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ inputOkB2 γ j inp ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"handle")) (Val #n)) (Val #inp))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .idle ∗ nodeExitB2 c γ q ∗ threadTok }}

/-- **`(*node).start()` under B2**: from `down`, fresh (B1's) or killed: its storage from its disk
(`memoryOf`), the `boot` report of the disk (term, vote, commit, last index and term; applied `0`;
the initial voters), `NewRawNode` (a restart: `restartAtApiSpec` at the disk's `StorageHolds`,
`Applied = 0`), the boot drain, `alone`. Ends drained. -/
abbrev node.start.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .down ∗ nodeExitB2 c γ q ∗ threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"start")) (Val #()))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok }}

/-- **`(*node).emit(p)` under B2**: dead, nothing recorded; a fuse that burns out kills, nothing
recorded; otherwise recorded (`emitStep`). -/
abbrev node.emit.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (p : Loc) (ev : AntCheck.Event) (Q : IProp GF)
    (dead : Bool) (fuse : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n dead fuse ∗ eventOwn p ev ∗
      reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j)) ev] Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"emit")) (Val #p))
  {{ (b : Bool), RET #b; killOwn n (emitStep dead fuse).2.1 (emitStep dead fuse).2.2 ∗
      ⌜b = (emitStep dead fuse).1⌝ ∗
      if b then Q else reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j)) ev] Q }}

/-- **`(*node).announce(p)` under B2**: `emit`'s, and, recorded with a fuse of `1` left, a kill
between the announcement and the write (`below(2) == 0`): recorded and dead. -/
abbrev node.announce.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (p : Loc) (ev : AntCheck.Event) (Q : IProp GF)
    (dead : Bool) (fuse : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n dead fuse ∗ eventOwn p ev ∗
      reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j)) ev] Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"announce")) (Val #p))
  {{ (b : Bool) (dead' : Bool) (fuse' : w64), RET #b; killOwn n dead' fuse' ∗
      ⌜(b = true → dead' = false) ∧
        (((emitStep dead fuse).1 = false ∧ dead' = (emitStep dead fuse).2.1 ∧ fuse' = (emitStep dead fuse).2.2) ∨
         ((emitStep dead fuse).1 = true ∧ ((dead' = false ∧ fuse' = (emitStep dead fuse).2.2) ∨
           ((emitStep dead fuse).2.2 = W64 1 ∧ dead' = true ∧ fuse' = W64 0))))⌝ ∗
      if (emitStep dead fuse).1 then Q else reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j)) ev] Q }}

/-- **`(*node).saveDisk(hs, ents)` under B2**: the write when alive; nothing when dead. -/
abbrev node.saveDisk.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (d : Loc) (w : AntSim.DurW) (hp : Loc)
    (oh : Option HardStateM) (sl : GoSlice) (els : List Loc) (es : List EntryM) (dead : Bool) (fuse : w64),
    SaveOk w es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ n.[H.node, go!"disk"] ↦□ d ∗ killOwn n dead fuse ∗ diskOwn d w ∗ hsOptRO hp oh ∗
      sl ↦*□ els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"saveDisk")) (Val #hp)) (Val #sl))
  {{ RET #(); killOwn n dead fuse ∗ diskOwn d (if dead then w else saveW w oh es) }}

/-- **`(*node).sendMsg(m)` under B2**: to the network when alive (B1's); nothing when dead. -/
abbrev node.sendMsg.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (ml : Loc)
    (cap : Bool) (st : MsgSt) (q : Qp) (dead : Bool) (fuse : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n dead fuse ∗ netAdder c γ.toAntNames q ∗ threadTok ∗
      msgPtsC ml DFrac.discard DFrac.discard cap st ∗ (⌜dead = true⌝ ∨ sendFacts γ.toAntNames st) ∗
      ⌜γ.mode.SnapStatus' = false⌝ ∗ ⌜st.resps = []⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"sendMsg")) (Val #ml))
  {{ RET #(); killOwn n dead fuse ∗ netAdder c γ.toAntNames q ∗ threadTok ∗
      msgPtsC ml DFrac.discard DFrac.discard cap st }}

/-- **`(*node).stateEv(e, hs, ents)` under B2** (`node.stateEv.spec`'s text over the B2 vocabulary). -/
abbrev node.stateEv.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (e : GoString) (hp : Loc) (hs : HardStateM)
    (sl : GoSlice) (dq : DFrac) (els : List Loc) (es : List EntryM), AllNormal es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ hsRO hp hs ∗ sl ↦*{dq} els ∗ [∗list] p;e ∈ els;es, entRO p e }}
    (App (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"stateEv")) (Val #e)) (Val #hp)) (Val #sl))
  {{ (p : Loc), RET #p; sl ↦*{dq} els ∗ ([∗list] p;e ∈ els;es, entRO p e) ∗ eventOwn p (stateEvM e hs es) ∗
      ⧗ es.length }}

/-- **`(*node).sendEv(by, m)` under B2** (`node.sendEv.spec`'s text over the B2 vocabulary). -/
abbrev node.sendEv.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (by_ : GoString) (ml : Loc) (dq dqe : DFrac)
    (cap : Bool) (st : MsgSt), st.msg.Type' ≠ MsgSnap → AllNormal st.ents →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ msgPtsC ml dq dqe cap st }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"sendEv")) (Val #by_)) (Val #ml))
  {{ (p : Loc), RET #p; msgPtsC ml dq dqe cap st ∗ eventOwn p (sendEvM by_ st) ∗ ⧗ st.ents.length }}

/-- **`(*node).reportCause()` under B2**: the cause cell cleared; its report, if any, through `emit`
(`causeStep`: dead or killed now, not recorded, the reports kept). -/
abbrev node.reportCause.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (cl : Loc) (o : Option AntCheck.Event) (Q : IProp GF)
    (dead : Bool) (fuse : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ killOwn n dead fuse ∗ n.[H.node, go!"cause"] ↦ cl ∗
      pendingCause cl o ∗ reports γ.strm (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"reportCause")) (Val #()))
  {{ RET #(); killOwn n (causeStep o dead fuse).2.1 (causeStep o dead fuse).2.2 ∗ n.[H.node, go!"cause"] ↦ null ∗
      if (causeStep o dead fuse).1 then Q
      else reports γ.strm (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}

/-- **`(*node).parts(hs, ents)` under B2**: one write (`Split = 0`, B1's), or `splitTermEntriesCommit`'s
up to three: the term and vote with the old commit, the entries, the commit (each part's `after` the
hard state on disk after it). -/
abbrev node.parts.specB2 : Prop :=
  ∀ (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (hp hp0 : Loc) (sl : GoSlice) (h h0 : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ n.[H.node, go!"hs"] ↦ hp0 ∗ hsRO hp h ∗ hsRO hp0 h0 ∗
      ⌜γ.mode.Split' = W64 0 ∨ γ.mode.Split' = W64 1⌝ }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"parts")) (Val #hp)) (Val #sl))
  {{ (out : GoSlice) (ps : List H.part), RET #out; n.[H.node, go!"hs"] ↦ hp0 ∗ out ↦* ps ∗
      ⌜γ.mode.Split' = W64 0 → ps = [({ hs' := if hp = hp0 then null else hp, ents' := sl, after' := hp } : H.part)]⌝ ∗
      ⌜γ.mode.Split' = W64 1 → ps.length ≤ 3 ∧ ∀ p ∈ ps, p.ents' = sl ∨ p.ents' = slice.nil⌝ ∗
      [∗list] p ∈ ps, ∃ (ha : HardStateM) (oh : Option HardStateM),
        hsRO p.after' ha ∗ hsOptRO p.hs' oh ∗
        ⌜ha = h ∨ ha = h0 ∨ (ha.Term' = h.Term' ∧ ha.Vote' = h.Vote' ∧ ha.Commit' = h0.Commit')⌝ ∗
        ⌜∀ h', oh = some h' → h' = ha⌝ }}

/-- **`(*node).input(by, ents)` under B2**: the drain (sync or async), or, batching, `note`. -/
abbrev node.input.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp)
    (sl : GoSlice) (es : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ entsRO sl es ∗ nodeExitB2 c γ q ∗
      threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"input")) (Val #v.byE)) (Val #sl))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

/-- **`(*node).drain(by)` under B2**: async → `drainAsync`; sync: per `Ready` B1's, a leader's in
`Parallel` through `parallel`, the write in `parts`. -/
abbrev node.drain.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"drain")) (Val #v.byE))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

/-- **`(*node).tick()` under B2** (the shape of every input call's, `campaign`, `propose`,
`readIndex`, `unreachable`, `transferLeader`, `step`: B1's text over the B2 vocabulary, `DrainB2` for
`DrainB1`; the others' below are stated with their B1 premises the same way). -/
abbrev node.tick.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"tick")) (Val #()))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"tick"⌝ }}

/-- **`(*node).campaign` under B2** (`node.campaign.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.campaign.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"campaign")) (Val #()))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"campaign"⌝ }}

/-- **`(*node).propose` under B2** (`node.propose.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.propose.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (sl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ ∗ sl ↦*□ data ∗ propOk γ.toAntNames data }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"propose")) (Val #sl))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"propose"⌝ }}

/-- **`(*node).readIndex` under B2** (`node.readIndex.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.readIndex.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (ctx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ ∗ readOk γ.toAntNames ctx ∗ ⌜γ.mode.Reads' = true⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"readIndex")) (Val #ctx))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"read"⌝ }}

/-- **`(*node).unreachable` under B2** (`node.unreachable.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.unreachable.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"unreachable")) (Val #id))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"tick"⌝ }}

/-- **`(*node).transferLeader` under B2** (`node.transferLeader.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.transferLeader.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ ∗ ⌜γ.mode.Transfer' = true ∧ ∃ i : Fin γ.R.N, to = AntSim.nodeId i⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"transferLeader")) (Val #to))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = go!"transfer"⌝ }}

/-- **`(*node).step` under B2** (`node.step.spec`'s text over the B2 vocabulary, `DrainB2` for `DrainB1`). -/
abbrev node.step.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (q : Qp) (ml : Loc) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .idle ∗ nodeExitB2 c γ q ∗ threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      ((∃ m : Msg, netMsg γ.toAntNames ml st m ∗ ⌜m.dst = AntSim.nodeId j⌝) ∨
       (∃ x : XMsg, netXMsg γ.toAntNames ml st x ∗ ⌜x.dst = AntSim.nodeId j⌝)) }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"step")) (Val #ml))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .idle ∗ nodeExitB2 c γ q ∗ threadTok }}

/-- **`(*node).alone()` under B2**: after the boot drain of a batching node, `note("write")`; nothing
otherwise (B1's spec: batching off). -/
abbrev node.alone.specB2 : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) (v : AntSim.NodeView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗ ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"alone")) (Val #()))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok }}

end spec

end AntHarness
end EtcdGrove
end Perennial
