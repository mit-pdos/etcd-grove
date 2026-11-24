/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the per-report statements (#33 S3c step 5 / S4)

One statement per report kind, plus the reportless steps (`quiet`) and `GC`
(`notes/antithesis-rawnode-design.md` §3.3, in the shape of `notes/antithesis-s4-design.md` §3):

    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G → <raft's facts> →
      ∃ S', Prefix cfg3 (evs ++ [ev]) S' ∧ AntSim S' V' net' ∧ GlobalOk S' net' G

with `ev` the harness's report as a function of the raft data (`Abs.lean`) and `V'`, `net'` as the
report moves them. The `GC` steps the checker takes before each event are inside `Prefix`'s step
(`Checker.next`); `antSim_gc` is the statement each proof uses for them. Raft's facts are pure
relations over `PState`: the per-input end relations (`Protocol/InputEnd.lean`: `RecvEnd`,
`TickEnd`, `ProposeEnd`, `AdvanceEnd`), the `Ready`'s data as a function of the node's state
(`ReadyOutP`, the protocol reading of `ReadyOut`, §2.2), and the global facts already in `G`
(`ReadyFacts`, `MsgFacts`). The S4 harness proof applies them, one per report, inside the recorder's
atomic update (§3.4). Statements only (phase 1 of the spec-first plan): `abbrev <name>.stmt : Prop`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Rel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section stmts
variable [GooseExts]

/-! ## Raft's side of a report -/

/-- The cluster's configuration (`γ.reCfg`): voters `1, 2, 3`, no learners, not joint. -/
def cfgM3 : CfgM := CfgM.simple voters3 ∅

/-- One input of a node's goroutine (`Cluster.run`): a message (`RawNode.Step`), a tick
(`RawNode.Tick`), a proposal's data (`RawNode.Propose`). -/
inductive Input where
  | recv (m : Msg)
  | tick
  | propose (data : List w8)

/-- The `by` of the input's drain (`drain(n, "recv")`, ...). -/
def Input.byE : Input → AntCheck.Str
  | .recv _ => go!"recv"
  | .tick => go!"tick"
  | .propose _ => go!"propose"

/-- The message the input's drain handles (`n.cause`). -/
def Input.cause : Input → Option Msg
  | .recv m => some m
  | _ => none

/-- `RawNode.Propose(data)`'s message (`rawnode.go`: `MsgProp` from the node, one entry of the data,
term and index 0). -/
def propMsg (id : w64) (data : List w8) : Msg :=
  Msg.mk .propose id (W64 0) (W64 0) false (W64 0) (W64 0) (W64 0) (W64 0)
    [EntryM.mk (W64 0) (W64 0) (W32 0) data]

/-- What one input does to the node's protocol state (`RecvEnd`, `TickEnd`, `ProposeEnd`). -/
def InputStep (id : w64) (ps : PState) : Input → PState → Prop
  | .recv m, ps' => RecvEnd cfgM3 id ps m ps'
  | .tick, ps' => TickEnd cfgM3 id ps ps'
  | .propose d, ps' => ProposeEnd id ps (propMsg id d) ps'

/-- The view once the node has taken an input (before any report): the drain's `by` and cause; its
`recv` not reported yet (`Cluster.run` sets `n.cause`). -/
def NodeView.noteInput (v : NodeView) (inp : Input) : NodeView :=
  { v with byE := inp.byE, cause := inp.cause, told := false }

/-- **How the node reached the state `ps₁` a `Ready` (or `HasReady`) is taken at**, from its view
`v`: no input taken (`RunCluster`'s `drain(n, "boot")` right after the `boot` report, at the
view's own state), an input taken between inputs (`v` noted it, `NodeView.noteInput`; a message
received was sent to it), or `Advance` at the end of a `Ready` whose reports are all made
(`AdvanceEnd` stepping the `Ready`'s self-addressed messages; the drain's `by` one of the
harness's). -/
inductive Reach (id : w64) (net : List Msg) : NodeView → PState → Prop
  | stay (v : NodeView) : v.Idle → Reach id net v v.ps
  | input (v : NodeView) (inp : Input) (ps₁ : PState) :
      v.Idle → v.byE = inp.byE → v.cause = inp.cause →
      (∀ m, inp = .recv m → m ∈ net ∧ m.dst = id) →
      InputStep id v.ps inp ps₁ → Reach id net v ps₁
  | advance (v : NodeView) (ps₁ : PState) :
      v.pend = [] → v.ce = [] →
      (v.byE = go!"boot" ∨ v.byE = go!"recv" ∨ v.byE = go!"tick" ∨ v.byE = go!"propose") →
      AdvanceEnd cfgM3 id v.ps v.qs ps₁ → Reach id net v ps₁

/-- A `Ready`'s data, as the harness reads it: the role and hard state after it (`SoftState` or the
last reported role; `HardState` or the last written one), its entries to write (`Entries`), its
messages to other nodes in its order (`Messages`), the self-addressed ones `Advance` steps
(`stepsOnAdvance`), its committed entries (`CommittedEntries`). -/
structure ReadyD where
  role : Role
  term : w64
  vote : w64
  commit : w64
  ents : List EntryM
  msgs : List Msg
  qs : List Msg
  ce : List EntryM

/-- **The `Ready` binding at the protocol level** (`ReadyOut`, §2.2, over `PState`): a `Ready` taken
at `ps` from a node whose view (its durable state) is `v` reports `ps`'s role and hard state; its
entries are what the write appends (the log after it is `ps.log`, from the first entry's index,
which starts at a conflict with the durable log or past its end: raft's unstable entries); its
messages are `ps`'s outbox, those to the node itself queued for `Advance` (in some order: raft's
invariants relate `msgsAfterAppend` to the outbox up to permutation), the others to voters;
its committed entries follow what was handed out, within the commit index; no snapshot, the log's
indices its positions. -/
def ReadyOutP (id : w64) (v : NodeView) (ps : PState) (rd : ReadyD) : Prop :=
  rd.role = ps.role ∧ rd.term = ps.term ∧ rd.vote = ps.vote ∧ rd.commit = ps.commit ∧
  (rd.ents = [] → ps.log = v.ps.log) ∧
  (∀ e0 ∈ rd.ents.head?, ps.log = v.ps.log.take (uint.nat e0.Index' - 1) ++ rd.ents ∧
    ∀ e ∈ v.ps.log[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') ∧
  rd.qs.Perm (ps.outbox.filter (fun q => decide (q.dst = id))) ∧
  rd.msgs.Perm (ps.outbox.filter (fun q => decide (q.dst ≠ id))) ∧
  v.delivered ++ rd.ce <+: ps.log ∧ (v.delivered ++ rd.ce).length ≤ uint.nat ps.commit ∧
  ps.base = base0 ∧ LogIdx ps.log

/-- The harness reports the `Ready` (`drain`'s `write || role != n.role`): its hard state, its
entries or its role differ from the last reported (the view's, C1). -/
def Reported (v : NodeView) (rd : ReadyD) : Prop :=
  rd.term ≠ v.ps.term ∨ rd.vote ≠ v.ps.vote ∨ rd.commit ≠ v.ps.commit ∨ rd.ents ≠ [] ∨
    rd.role ≠ v.ps.role

/-- The view after a `Ready` taken at `ps` (the drain phase): `ps` with the outbox emptied, the
`Ready`'s messages and committed entries to report, its self-addressed messages for `Advance`. -/
def NodeView.afterReady (v : NodeView) (ps : PState) (rd : ReadyD) : NodeView :=
  { v with ps := { ps with outbox := [] }, qs := rd.qs, pend := rd.msgs, ce := rd.ce }

/-- **The steps of a node that report nothing** (§3.3's `antSim_quiet`): taking an input (noted in
the view); reaching a state with no `Ready` (`HasReady` false: `PIdle`, nothing to write, send or
apply; after an input, or after `Advance`, ending the drain); a `Ready` whose write and role the
harness does not report (only messages or committed entries, reported by `antSim_send`,
`antSim_apply`). -/
inductive Quiet (id : w64) (net : List Msg) : NodeView → NodeView → Prop
  | input (v : NodeView) (inp : Input) :
      v.Idle → (∀ m, inp = .recv m → m ∈ net ∧ m.dst = id) → Quiet id net v (v.noteInput inp)
  | noReady (v : NodeView) (ps₁ : PState) :
      Reach id net v ps₁ → ps₁.outbox = [] → ps₁.term = v.ps.term → ps₁.vote = v.ps.vote →
      ps₁.commit = v.ps.commit → ps₁.role = v.ps.role → ps₁.log = v.ps.log →
      Quiet id net v { v with ps := ps₁, qs := [] }
  | silentReady (v : NodeView) (ps₁ : PState) (rd : ReadyD) :
      Reach id net v ps₁ → ReadyOutP id v ps₁ rd → ¬ Reported v rd →
      Quiet id net v (v.afterReady ps₁ rd)

/-- `V` with node `n`'s view replaced. -/
def setV (V : Fin 3 → NodeView) (n : Fin 3) (v : NodeView) : Fin 3 → NodeView :=
  fun j => if j = n then v else V j

/-! ## The statements -/

/-- **The initial state** (`Init0`, B 755, `Bootstrapped = FALSE`): before any report, at three
fresh nodes (`pInit`), the checker is at a state related to them, with no message sent; its facts
are certified by any `G` that has the empty log. -/
abbrev antSim_init.stmt : Prop :=
  ∀ V : Fin 3 → NodeView,
    (∀ n, PInit (V n).ps ∧ (V n).delivered = [] ∧ (V n).Idle ∧ (V n).told = false) →
    ∃ S, Prefix cfg3 [] S ∧ AntSim S V [] ∧ ∀ G : RaftFacts, [] ∈ G.logs → GlobalOk S [] G

/-- **`boot`** (`RunCluster`, B 162-194): a fresh node's `boot` report is taken (`Recovered` with term
0, vote `""`, commit 0, no entry; voters `names(3)`, none outgoing). -/
abbrev antSim_boot.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List AntCheck.Event)
    (G : RaftFacts) (n : Fin 3),
    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G →
    PInit (V n).ps → (V n).delivered = [] → (V n).Idle → (V n).told = false →
    ∃ S', Prefix cfg3 (evs ++ [evBoot (nodeId n)]) S' ∧ AntSim S' V net ∧ GlobalOk S' net G

/-- **`recv`** (`reportCause`, B 199-204): the message a node handles, sent to it, is reported (at
its drain's first report); the binding's `pending[n]` is then it. -/
abbrev antSim_recv.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List AntCheck.Event)
    (G : RaftFacts) (n : Fin 3) (m : Msg),
    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G →
    m ∈ net → m.dst = nodeId n → (V n).cause = some m →
    ∃ S', Prefix cfg3 (evs ++ [evRecv (nodeId n) m]) S' ∧
      AntSim S' (setV V n { V n with told := true }) net ∧ GlobalOk S' net G

/-- **The steps that report nothing** (`Quiet`): the relation holds of the new view, `S` unchanged. -/
abbrev antSim_quiet.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (G : RaftFacts) (n : Fin 3)
    (v' : NodeView),
    AntSim S V net → RaftLaws G → GlobalOk S net G → Quiet (nodeId n) net (V n) v' →
    AntSim S (setV V n v') net

/-- **`ready`** (`drain`, B 439-447: `InMemory` then `OnDisk`): a `Ready` taken after an input or an
`Advance`, whose write or role the harness reports (after the drain's `recv`, for `by = recv`), is
taken; the node's view becomes the `Ready`'s (the drain phase). -/
abbrev antSim_ready.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List AntCheck.Event)
    (G : RaftFacts) (n : Fin 3) (ps₁ : PState) (rd : ReadyD),
    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G →
    Reach (nodeId n) net (V n) ps₁ → ReadyOutP (nodeId n) (V n) ps₁ rd → Reported (V n) rd →
    ((V n).byE = go!"recv" → (V n).told = true) → ReadyFacts G (nodeId n) ps₁ →
    ∃ S', Prefix cfg3
        (evs ++ [evReady (nodeId n) (V n).byE rd.role rd.term rd.vote rd.commit rd.ents]) S' ∧
      AntSim S' (setV V n ((V n).afterReady ps₁ rd)) net ∧ GlobalOk S' net G

/-- **`send`** (`drain`, B 510-593): the next message of the node's `Ready` is reported, then it is on
the network. The message the drain handles was sent (the harness took it from the network). -/
abbrev antSim_send.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List AntCheck.Event)
    (G : RaftFacts) (n : Fin 3) (q : Msg) (rest : List Msg),
    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G →
    (V n).pend = q :: rest → ((V n).byE = go!"recv" → (V n).told = true) →
    (∀ m, (V n).cause = some m → m ∈ net) → MsgFacts G q →
    ∃ S', Prefix cfg3 (evs ++ [evSend (nodeId n) (V n).byE q]) S' ∧
      AntSim S' (setV V n { V n with pend := rest }) (net ++ [q]) ∧ GlobalOk S' (net ++ [q]) G

/-- **`apply`** (`drain`, B 598-609): the `Ready`'s committed entries are reported, then handed out. -/
abbrev antSim_apply.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (evs : List AntCheck.Event)
    (G : RaftFacts) (n : Fin 3),
    Prefix cfg3 evs S → AntSim S V net → RaftLaws G → GlobalOk S net G →
    (V n).ce ≠ [] → ((V n).byE = go!"recv" → (V n).told = true) →
    ∃ S', Prefix cfg3 (evs ++ [evApply (nodeId n) (V n).byE (V n).ce]) S' ∧
      AntSim S' (setV V n { V n with delivered := (V n).delivered ++ (V n).ce, ce := [] }) net ∧
      GlobalOk S' net G

/-- **`GC`** (B 713-723, taken while due before each event, `Checker.next`'s `gcLoop`): the steps
end within `gcFuel` with no violation, and the relation holds after them (C2-C4 name no garbage). -/
abbrev antSim_gc.stmt : Prop :=
  ∀ (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg) (G : RaftFacts),
    AntSim S V net → RaftLaws G → GlobalOk S net G →
    ∃ S', AntCheck.gcLoop (AntCheck.gcFuel S) S = .ok (S', none) ∧ AntSim S' V net ∧ GlobalOk S' net G

end stmts

end AntSim
end EtcdGrove
end Perennial
