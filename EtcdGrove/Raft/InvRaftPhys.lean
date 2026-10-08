/-
Port of `election_proof/inv_raft_phys.v` (at 857d09190): physical ownership of the raft
struct.

## Physical ownership of the raft struct

`ownRaftPhys cfg r id s` is full ownership of the `raft` struct at `r` and of
everything hanging off it, in a state described by the physical abstract state
`s : NState` (`Defs.lean`).

**This is the only ownership predicate for the raft struct, and every Go-level spec is
stated on it.** If a function cannot be specified this way, the fix is to make `NState`
more precise and this predicate with it -- not to add a variant. See `NState` for the
three variants this replaced on 2026-09-22 and notes/decisions.md, "Three layers", for
why.

There is no `γ`: this predicate says nothing about ghost state. The connection to the
protocol is `NStateRel` (`Defs.lean`), and `Step`'s spec is the only one that mentions
both.

Lean notes:
* Rocq's `Context (cfg : gset w64)` is an explicit section variable, so `ownRaftPhys`
  and every lemma about it take `cfg` as their first explicit argument (as in Rocq
  once the section is closed): `ownRaftPhys cfg r id s`. The reconfiguration section
  has no such variable and takes `cfg0 cfg` explicitly, as in Rocq.
* The seal (Rocq `seal`/`unseal`) is Perennial's Lean pattern
  (`Perennial/Golang/Defn/PostLang.lean`): `ownRaftPhysDef`, an `@[irreducible] def
  ownRaftPhys` equal to it, and an unseal lemma. The unseal lemma is `private`, as
  Rocq's is `Local`, and so is `ownRaftPhysDef` itself: an `@[irreducible]` def can
  still be `unfold`ed by its equation lemma, but outside this file what comes out is a
  private name that cannot be unfolded further. Rocq's `iNamed_phys` is a local macro
  (`ownRaftPhys_open`, `iunfold`, `icases`, `iNamed`).
* The Rocq `Local Ltac`s: `reseal` is a local macro that takes the target state
  explicitly (Rocq reads it off the goal) and closes the pure premises of
  `ownRaftPhys_intro` with `assumption`/`rfl`; `load_proof`/`store_proof` are written
  out in each proof (`wp_apply wp_load_access`/`wp_store_access`, the Rocq local
  lemmas, then `reseal`); `split_field_proof` is a local macro taking the `icases`
  pattern that names the field `Hx` and the remaining fields `Hrest`.
* Field-access lemmas are named `raft.wp_load_<field>` / `raft.wp_store_<field>` (Rocq
  `wp_raft_load_<field>` / `wp_raft_store_<field>`), and the accessors
  `ownRaftPhys_<x>` (Rocq `own_raft_phys_<x>`). They are stated at exactly the
  expressions `wp_auto` leaves in front of a raft field access in Perennial's Lean
  port: `App (Val (GoInstruction (GoLoad t))) (Val #(r.[raft, go!"f"]))` and
  `App (Val (GoInstruction (GoStore t))) (Val (PairV #(r.[raft, go!"f"]) #v))` (Rocq
  `![t] #(r.[raft.raft.t, "f"])` and `GoStore t (#(r.[raft.raft.t, "f"]), #v)%V`).
  Go types are the Lean descriptors: `raft.StateType` is `StateType.ty`,
  `go.PointerType raft.raftLog` is `go.GoType.PointerType raftLog.ty`, etc.
* `msg_abs`, `abs_list`, `outbox_rel`, `send_no_snap` are `msgAbs`, `absList`,
  `outboxRel`, `send_no_snap`; Rocq `omap (λ a, a) as_` is `as_.filterMap id`.
  `state_w64`, `send_msgs`, `own_tracker`, `own_raftLog`, `own_Progress`, `is_Logger`,
  `own_ReadOnly`, `own_raft_misc` are `stateW64`, `sendMsgs`, `ownTracker`,
  `ownRaftLog`, `ownProgress`, `isLogger`, `ownReadOnly`, `ownRaftMisc`; `trk.mk v p q`
  is `⟨v, p, q⟩ : Trk`.
* Rocq's local `wp_load_access`/`wp_store_access` are kept (private), stated as
  Hoare triples so that `wp_apply` uses them; the field `AccessStrict` instances are
  the generated ones. `split_field_proof` unseals only the struct points-to, with
  `typedPointsto_unseal_eq`.
* `ownRaftPhys_reconfig`'s and `ownRaftPhys_retrack`'s new states are written
  `{ s with progress := prs', prvals := pvs' }` etc., Rocq's chains of setters (the
  same value).
* The Rocq `wp_raft_log` tactic is the macro `wp_raft_log` at the end of this file
  (checked on a copy of `becomeCandidate`'s `Infof` call; not used anywhere yet).
-/
import EtcdGrove.Raft.InvRaftlog
import EtcdGrove.Raft.InvTracker
import EtcdGrove.Raft.InvLogger
import EtcdGrove.Raft.InvMisc

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The abstract outbox of the two queues

`msgAbs m a`: the queued physical message `m` contributes `a` to the abstract outbox --
`none` for a type the model does not describe (`mtypeOf = none`: `MsgHup`,
`MsgCheckQuorum`, ...), else `absMsg ty m ents` where `ents` is what `m.Entries` points
to, held read-only. The points-to is what makes the abstraction a function of the heap
rather than of `m` alone: `m.Entries` is a slice (notes/raft-replication-model.md,
"Abstract messages").

A `MsgSnap` is abstracted by `absSnap m sv voters` instead (since 2026-10-02), the
snapshot's metadata and voters -- **read through the heap** (since 2026-10-03), like
`App`'s entries: `sv` is what `m.Snapshot` points to and `voters` what `sv`'s
`ConfState.Voters` slice holds, both read-only. `send` takes these points-tos for a
`MsgSnap` (its `Hsnap`); `maybeSendSnapshot` persists the local `snapshot` variable
whose address it queues (nobody writes it again) and has the voters from
`raftLog.snapshot` (`isStorage`'s `HSnapshot`, or `ownSnap` for a pending snapshot).
The receiving side, `Step`'s `Hsnap`, holds the same points-tos.

`outboxRel o msgs msgsAA`: the abstract outbox `o` is, up to permutation, what the two
queues contribute. Persistent. -/
def msgAbs (m : raftpb.Message) (a : Option Msg) : IProp GF :=
  iprop(⌜mtypeOf m.Type' = none ∧ a = none⌝ ∨
    (∃ ty ents, ⌜mtypeOf m.Type' = some ty ∧ ty ≠ .snap ∧ a = some (absMsg ty m ents)⌝ ∗
                m.Entries' ↦*□ ents) ∨
    (∃ (sv : raftpb.Snapshot) (voters : List w64),
       ⌜mtypeOf m.Type' = some .snap ∧ a = some (absSnap m sv voters)⌝ ∗
       m.Snapshot' ↦□ sv ∗
       sv.Metadata'.ConfState'.Voters' ↦*□ voters))

/-- `send`'s `Hsnap` precondition for a message that is not a `MsgSnap`: vacuous. -/
theorem send_no_snap (m : raftpb.Message) (P : IProp GF) (Hne : m.Type' ≠ MsgSnap) :
    ⊢ □ (⌜m.Type' = MsgSnap⌝ -∗ P) := by
  imodintro
  iintro %H
  exact absurd H Hne

def absList (as_ : List (Option Msg)) : List Msg := as_.filterMap id

def outboxRel (o : List Msg) (msgs msgsAA : List raftpb.Message) : IProp GF :=
  iprop(∃ (as1 as2 : List (Option Msg)),
    ⌜o ≡ₚ absList as1 ++ absList as2⌝ ∗
    ([∗list] _k ↦ m;a ∈ msgs;as1, msgAbs m a) ∗
    ([∗list] _k ↦ m;a ∈ msgsAA;as2, msgAbs m a))

instance msgAbs_pers (m : raftpb.Message) (a : Option Msg) :
    Persistent (msgAbs (GF := GF) m a) := by
  unfold msgAbs; infer_instance

instance outboxRel_pers (o : List Msg) (msgs msgsAA : List raftpb.Message) :
    Persistent (outboxRel (GF := GF) o msgs msgsAA) := by
  unfold outboxRel; infer_instance

theorem outboxRel_nil : ⊢ outboxRel (GF := GF) [] [] [] := by
  unfold outboxRel
  iexists [], []
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m a => msgAbs (GF := GF) m a)).2; iempintro
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m a => msgAbs (GF := GF) m a)).2; iempintro

theorem outboxRel_perm (o o' : List Msg) (msgs msgsAA : List raftpb.Message) (Hp : o' ≡ₚ o) :
    ⊢ outboxRel (GF := GF) o msgs msgsAA -∗ outboxRel o' msgs msgsAA := by
  unfold outboxRel
  iintro ⟨%as1, %as2, %Ho, H1, H2⟩
  iexists as1, as2
  iframe H1 H2
  ipureintro; exact Hp.trans Ho

-- The (fixed) set of voters. `ownRaftPhys` mentions it because `ownTracker` does: now
-- that the tracker is a real definition rather than an opaque axiom, it pins the
-- progress map's domain and the configuration's voter set to `cfg`.
variable (cfg : GSet w64)

/-- Rocq `own_raft_phys_def`: the body of `ownRaftPhys` (see the file header). -/
private def ownRaftPhysDef (r : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(∃ (rv : raft) (msgs msgsAA : List raftpb.Message) (lok : GoInterfaceOk),
  "Hr" ∷ r ↦ rv ∗

  -- the abstraction relation
  "%Hid" ∷ ⌜rv.id' = id⌝ ∗
  "%Hterm" ∷ ⌜rv.Term' = s.term⌝ ∗
  "%Hvote" ∷ ⌜rv.Vote' = s.vote⌝ ∗
  "%Hlead" ∷ ⌜rv.lead' = s.lead⌝ ∗
  "%Hstate" ∷ ⌜rv.state' = stateW64 s.role⌝ ∗
  -- `r.step`. Not a function of the role: `becomeFollower` assigns it before `reset`
  -- runs, and `newRaft` starts with it nil. That the two agree is `NStateWf`, which
  -- `Step` carries.
  "%Hstepfn" ∷ ⌜rv.step' = s.stepfn⌝ ∗

  -- the vote tally, the progress map and the rest of the heap the tracker points at.
  -- The tracker's own bytes are covered by `Hr` above, since `trk` is embedded by
  -- value; this is only what hangs off it. Indexed by `s.progress` and `s.prvals`:
  -- that is what lets a proof know *which* `Progress` a peer has, and what it holds,
  -- after a call it made with the struct sealed. (Until 2026-09-29 the values were
  -- existential, and a proof that needed one across a call took the tracker out of
  -- the predicate on loan, `nstate.lent`.) (From 2026-09-22 to 2026-09-23 a second,
  -- persistent copy of the progress map's points-to sat here, beside the one inside
  -- `ownTracker`; indexing `ownTracker` by the map made it redundant.)
  "Htrk" ∷ ownTracker cfg rv.trk' ⟨s.votes, s.progress, s.prvals⟩ ∗

  -- the log, at the state `s` records (`NState.logst`). Never on loan: what
  -- `raftLog.slice` returns is read-only and the caller's for good. (Until 2026-09-28
  -- the log's state was quantified here, and the log went on loan with the tracker;
  -- until 2026-09-29 a slice `raftLog.slice` lent out was recorded in `logst.page`.)
  "%Hlogp" ∷ ⌜rv.raftLog' = s.log⌝ ∗
  "Hlog" ∷ ownRaftLog rv.raftLog' s.logst ∗

  -- outgoing messages. `send` routes vote/append *responses* to `msgsAfterAppend`
  -- and everything else to `msgs`; the model has a single outbox, so the
  -- abstraction is of the two together.
  --
  -- Two deliberate choices here. `filterMap` (Rocq `omap`): a message type the model
  -- does not describe (notably the `MsgAppResp` that `appendEntry` queues) simply
  -- drops out, rather than making the abstract outbox undefined. `≡ₚ`: appending to
  -- `msgs` does not append to the concatenation when `msgsAA` is non-empty, so
  -- equality would not survive a `send`; permutation is also all the model needs,
  -- since it cares which messages are out and not in what order.
  "Hmsgs" ∷ rv.msgs' ↦* msgs ∗
  "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rv.msgs' (DFrac.own 1) ∗
  "HmsgsAA" ∷ rv.msgsAfterAppend' ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message rv.msgsAfterAppend' (DFrac.own 1) ∗
  "#Houtbox" ∷ outboxRel s.outbox msgs msgsAA ∗

  -- `r.preVote`, recorded (since 2026-10-04; until then a scope conjunct pinned it to
  -- `false`). Never written after `newRaft`.
  "%Hprevote" ∷ ⌜rv.preVote' = s.prevote⌝ ∗

  -- scope assumptions
  -- `Config.DisableProposalForwarding` is `false` (`newRaft`'s premise): a follower
  -- forwards a proposal to the leader it knows. Never written after `newRaft`. Added
  -- 2026-10-02.
  "%HpropForward" ∷ ⌜rv.disableProposalForwarding' = false⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜rv.checkQuorum' = false⌝ ∗
  "%HnoLearner" ∷ ⌜rv.isLearner' = false⌝ ∗
  "%HnoTransfer" ∷ ⌜rv.leadTransferee' = W64 0⌝ ∗
  "%Hid_nz" ∷ ⌜id ≠ W64 0⌝ ∗
  -- `Config.validate` requires `ElectionTick > HeartbeatTick > 0` and `newRaft`
  -- copies it, so this is an invariant of every struct raft builds. It is needed
  -- because `resetRandomizedElectionTimeout` passes the field to `crypto/rand.Int`,
  -- which panics on a non-positive bound -- see
  -- `spec_raft__resetRandomizedElectionTimeout.v`. Never written on the election path.
  -- Added 2026-09-20.
  "%HelectionTimeout" ∷ ⌜0 < sint.Z rv.electionTimeout'⌝ ∗

  -- logging, tracing, and everything else
  "%Hlok" ∷ ⌜rv.logger' = interface.ok lok⌝ ∗
  "#Hlogger" ∷ isLogger lok ∗
  "Hmisc" ∷ ownRaftMisc rv.readStates' rv.readOnly' rv.pendingReadIndexMessages')

/-- Physical ownership of the raft struct (see the file header).

Sealed: outside this file `ownRaftPhys` cannot be unfolded, so a program proof that
reaches into the representation does not compile. Every access goes through the
interface below. -/
@[irreducible] def ownRaftPhys (r : Loc) (id : w64) (s : NState) : IProp GF :=
  ownRaftPhysDef cfg r id s

private theorem ownRaftPhys_unseal (r : Loc) (id : w64) (s : NState) :
    ownRaftPhys (GF := GF) cfg r id s = ownRaftPhysDef cfg r id s := by
  with_unfolding_all rfl

/-- Open the predicate, in this file only. -/
private theorem ownRaftPhys_open (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhysDef cfg r id s := by
  rw [ownRaftPhys_unseal]; iintro H; iexact H

/-- Re-sealing `ownRaftPhys` after a proof has taken it apart.

In Rocq, `iFrame "∗#%"` against the unfolded predicate costs ~17s per use (2026-09-17
measurement): `iFrame "%"` alone tries every pure fact in the Coq context against
every one of the conjuncts. This lemma makes a re-seal a single `iapply` with named
hypotheses and pure side goals:

    iapply ownRaftPhys_intro … $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

The pure premises are in the order the conjuncts appear in the predicate. `r ↦ rv` is
the first spatial argument **on purpose**: it is what fixes `rv`, at the struct value
the heap holds *now*. If another argument came first, `rv` would be fixed from it --
at whatever struct value that hypothesis was stated -- and after any field write the
heap's `r ↦ { rv with … }` would then fail to match. -/
theorem ownRaftPhys_intro (r : Loc) (id : w64) (s : NState) (rv : raft)
    (msgs msgsAA : List raftpb.Message) (lok : GoInterfaceOk) :
    rv.id' = id →
    rv.Term' = s.term →
    rv.Vote' = s.vote →
    rv.lead' = s.lead →
    rv.state' = stateW64 s.role →
    rv.step' = s.stepfn →
    rv.preVote' = s.prevote →
    rv.disableProposalForwarding' = false →
    rv.checkQuorum' = false →
    rv.isLearner' = false →
    rv.leadTransferee' = W64 0 →
    id ≠ W64 0 →
    0 < sint.Z rv.electionTimeout' →
    rv.logger' = interface.ok lok →
    rv.raftLog' = s.log →
    ⊢ (r ↦ rv : IProp GF) -∗
      isLogger lok -∗
      ownTracker cfg rv.trk' ⟨s.votes, s.progress, s.prvals⟩ -∗
      ownRaftLog rv.raftLog' s.logst -∗
      rv.msgs' ↦* msgs -∗
      ownSliceCap raftpb.Message rv.msgs' (DFrac.own 1) -∗
      rv.msgsAfterAppend' ↦* msgsAA -∗
      ownSliceCap raftpb.Message rv.msgsAfterAppend' (DFrac.own 1) -∗
      ownRaftMisc rv.readStates' rv.readOnly' rv.pendingReadIndexMessages' -∗
      outboxRel s.outbox msgs msgsAA -∗
      ownRaftPhys cfg r id s := by
  intro Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum
    HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
  iintro Hr #Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc #Houtbox
  rw [ownRaftPhys_unseal]; unfold ownRaftPhysDef
  iexists rv, msgs, msgsAA, lok
  simp only [named]
  iframe Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox
  ipureintro
  exact ⟨Hid, Hterm, Hvote, Hlead, Hstate, Hstepfn, Hlogp, Hprevote, HpropForward,
    HnoCheckQuorum, HnoLearner, HnoTransfer, Hid_nz, HelectionTimeout, Hlok⟩

end proof

set_option hygiene false in
/-- Rocq `iNamed_phys`: open `ownRaftPhys` in the hypothesis `H` and name its
conjuncts (`rv`, `msgs`, `msgsAA`, `lok`, `Hr`, `Hid`, ...). In this file only. -/
local macro "iNamed_phys " H:ident : tactic =>
  `(tactic| (ihave $H:ident := ownRaftPhys_open _ _ _ _ $$ $H:ident;
             iunfold ownRaftPhysDef at $H:ident;
             icases $H:ident with ⟨%rv, %msgs, %msgsAA, %lok, $H:ident⟩;
             iNamed $H:ident))

/-- The pure premises of `ownRaftPhys_intro` after a field access: each is a
hypothesis of the opened predicate up to computation, or holds by computation. -/
local macro "phys_pure" : tactic => `(tactic| first | assumption | rfl)

set_option hygiene false in
/-- Rocq `reseal`: re-seal at the state `s'` the goal names, given explicitly because
otherwise `ownRaftPhys_intro`'s `s` is fixed by `Htrk` -- at the state *before* the
access -- and the conclusion no longer matches. -/
local macro "reseal " s:term:max : tactic =>
  `(tactic| (iapply ownRaftPhys_intro _ _ _ $s _ msgs msgsAA lok
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- The progress map in `s` is the tracker's, and so has domain `cfg`. Read out
without consuming anything. -/
theorem ownRaftPhys_progress_dom (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜domSet s.progress = cfg⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  icases ownTracker_progress_map cfg _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  isplitr
  · ipureintro; exact Hdom
  reseal s

/-- Changing only the outbox, up to permutation. -/
theorem ownRaftPhys_outbox (r : Loc) (id : w64) (s : NState) (o : List Msg) :
    o ≡ₚ s.outbox →
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhys cfg r id { s with outbox := o } := by
  intro Ho
  iintro H
  iNamed_phys H
  ihave #Houtbox' := outboxRel_perm _ o _ _ Ho $$ Houtbox
  iapply ownRaftPhys_intro _ _ _ { s with outbox := o } _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'

/-- Sending nothing, in both directions: an exit that sends nothing proves a
postcondition stated at `sendMsgs s ms` with `ms = []`, and a `send` of a message the
model does not see comes back at `sendMsgs s []`. -/
theorem ownRaftPhys_send_nil (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhys cfg r id (sendMsgs s []) := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

theorem ownRaftPhys_unsend (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id (sendMsgs s []) -∗ ownRaftPhys cfg r id s := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

/-! ## The interface: field lemmas and accessors

**Program proofs do not unfold `ownRaftPhys`.** Every access to the raft struct goes
through one of the lemmas below, so that the struct's representation -- `r ↦ rv`, the
abstraction relation, the scope assumptions -- is written down, and relied on, in this
file alone. Changing the representation then means re-proving this section, not the
program proofs. (Decided 2026-09-24; notes/decisions.md, "Program proofs do not unfold
`own_raft_phys`".)

`wp_auto` is *not* used for these accesses. Its field automation builds on full
ownership of the struct, `r ↦ rv`, which is exactly the representation this predicate
hides: with `ownRaftPhys` sealed, `wp_auto` stops in front of a load or store of a raft
field, and the proof continues with the lemma for that field, named explicitly:
`wp_apply raft.wp_load_Term $$ Hphys as Hphys`. There is deliberately no tactic that
searches the lemmas for the one that applies: each failed `wp_apply` walks the whole
program, and a proof that names its lemma says which field it touches.

There are three kinds.

- **Scalar fields**, one Hoare triple per load and per store, stated at the expression
  `wp_auto` leaves behind: `App (Val (GoInstruction (GoLoad t))) (Val #(r.[raft, f]))`
  and `App (Val (GoInstruction (GoStore t))) (Val (PairV #(r.[raft, f]) #v))`. A field
  `NState` tracks is loaded at its abstract value and a store updates `s`; a field
  pinned by a scope assumption is loaded at the pinned value and has no store (or only
  a store of that value); a field the abstraction does not track is loaded at an
  unknown value and stored freely. If a proof needs to know more about one of the
  latter -- that two loads agree, say -- the rule is the usual one: add it to `NState`.
- **Heap hanging off a field**: the tracker, the log, the two message queues, the
  `readOnly` object. An *accessor* hands out the field's points-to and the object's own
  predicate, together with a wand that takes them back -- possibly changed -- and gives
  `ownRaftPhys` at the correspondingly changed state. What the object is then used for
  (a map lookup in `trk.Progress`, `raftLog` methods, `append` on a queue) is the
  object's business, specified by its own predicate, so no operation on it is
  duplicated here.

Nothing is ever lent out of the predicate: an accessor's wand is the only way to hold
part of the struct across a step, and a call on the struct needs the predicate whole.
(Until 2026-09-29 there were loans, `own_raft_phys_lend` / `own_raft_phys_unlend`,
which moved the tracker's heap out of the predicate for the length of a function body;
`nstate.lent`.) -/

private theorem wp_load_access {V : Type} {t : go.GoType} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t]
    (l : Loc) (v : V) (P : IProp GF) [AccessStrict (l ↦ v) (l ↦ v) P P] :
    {{ P }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) {{ RET #v; P }} := by
  iintro %Φ HP HΦ
  icases (access_strict (A := l ↦ v) (A' := l ↦ v) (P := P) (P' := P)) $$ HP with ⟨Hl, Hback⟩
  iapply IntoValTyped.wp_load (t := t) l (DFrac.own 1) v $$ Hl
  inext
  iintro Hl
  iapply HΦ
  iapply Hback $$ Hl

private theorem wp_store_access {V : Type} {t : go.GoType} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t]
    (l : Loc) (v w : V) (P P' : IProp GF) [AccessStrict (l ↦ v) (l ↦ w) P P'] :
    {{ P }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) {{ RET #(); P' }} := by
  iintro %Φ HP HΦ
  icases (access_strict (A := l ↦ v) (A' := l ↦ w) (P := P) (P' := P')) $$ HP with ⟨Hl, Hback⟩
  iapply IntoValTyped.wp_store (t := t) l v w $$ Hl
  inext
  iintro Hl
  iapply HΦ
  iapply Hback $$ Hl

/-! ### Loads of fields `NState` tracks, and of the pinned ones -/

theorem raft.wp_load_id (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"id"])))
    {{ RET #id; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.id' $$ Hr as Hr
  rw [Hid]; iapply HΦ; reseal s

theorem raft.wp_load_Term (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Term"])))
    {{ RET #s.term; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.Term' $$ Hr as Hr
  rw [Hterm]; iapply HΦ; reseal s

theorem raft.wp_load_Vote (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Vote"])))
    {{ RET #s.vote; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.Vote' $$ Hr as Hr
  rw [Hvote]; iapply HΦ; reseal s

theorem raft.wp_load_lead (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"lead"])))
    {{ RET #s.lead; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.lead' $$ Hr as Hr
  rw [Hlead]; iapply HΦ; reseal s

theorem raft.wp_load_state (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad StateType.ty))) (Val #(r.[raft, go!"state"])))
    {{ RET #(stateW64 s.role); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.state' $$ Hr as Hr
  rw [Hstate]; iapply HΦ; reseal s

theorem raft.wp_load_step (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad stepFunc.ty))) (Val #(r.[raft, go!"step"])))
    {{ RET #s.stepfn; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.step' $$ Hr as Hr
  rw [Hstepfn]; iapply HΦ; reseal s

/-- The log's *location*. Its contents are `ownRaftPhys_log_at`'s. -/
theorem raft.wp_load_raftLog (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty))))
        (Val #(r.[raft, go!"raftLog"])))
    {{ RET #s.log; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.raftLog' $$ Hr as Hr
  rw [show (#rv.raftLog' : val) = #s.log by rw [Hlogp]]; iapply HΦ; reseal s

theorem raft.wp_load_logger (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad Logger.ty))) (Val #(r.[raft, go!"logger"])))
    {{ (lok : GoInterfaceOk), RET #(interface.ok lok);
        ownRaftPhys cfg r id s ∗ isLogger lok }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.logger' $$ Hr as Hr
  rw [Hlok]; iapply HΦ
  isplitl
  · reseal s
  · iexact Hlogger

theorem raft.wp_load_checkQuorum (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"checkQuorum"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.checkQuorum' $$ Hr as Hr
  rw [HnoCheckQuorum]; iapply HΦ; reseal s

theorem raft.wp_load_preVote (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"preVote"])))
    {{ RET #s.prevote; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.preVote' $$ Hr as Hr
  rw [Hprevote]; iapply HΦ; reseal s

theorem raft.wp_load_disableProposalForwarding (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool)))
        (Val #(r.[raft, go!"disableProposalForwarding"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.disableProposalForwarding' $$ Hr as Hr
  rw [HpropForward]; iapply HΦ; reseal s

/-- `r.pendingReadIndexMessages`, at a slice of length `0` (`ownRaftMisc` holds it at
the empty list). Moved here from `proof_releasePendingReadIndexMessages.v` on
2026-10-02. -/
theorem raft.wp_load_pendingReadIndexMessages (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType raftpb.Message.ty))))
        (Val #(r.[raft, go!"pendingReadIndexMessages"])))
    {{ (sl : GoSlice), RET #sl; ownRaftPhys cfg r id s ∗ ⌜sl.len = W64 0⌝ }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  icases Hmisc with ⟨%rr, Hmisc⟩
  iNamed Hmisc
  ihave %Hl := ownSlice_len _ _ _ $$ Hpri
  wp_apply wp_load_access _ rv.pendingReadIndexMessages' $$ Hr as Hr
  iapply HΦ
  isplitl
  · ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' rv.readOnly'
        rv.pendingReadIndexMessages' $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
    · unfold ownRaftMisc
      iexists rr
      simp only [named]
      iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap
      ipureintro; exact Hro_pending
    reseal s
  · ipureintro
    obtain ⟨Hl1, Hl2⟩ := Hl
    simp only [List.length_nil] at Hl1
    apply BitVec.eq_of_toInt_eq
    simp only [sint.nat] at Hl1
    simp only [sint.Z] at Hl2
    rw [show (W64 0).toInt = 0 by rfl]
    omega

theorem raft.wp_load_isLearner (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"isLearner"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.isLearner' $$ Hr as Hr
  rw [HnoLearner]; iapply HΦ; reseal s

theorem raft.wp_load_leadTransferee (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"leadTransferee"])))
    {{ RET #(W64 0); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.leadTransferee' $$ Hr as Hr
  rw [HnoTransfer]; iapply HΦ; reseal s

/-! ### Loads of fields the abstraction does not track -/

theorem raft.wp_load_electionTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s ∗ ⌜0 < sint.Z v⌝ }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.electionTimeout' $$ Hr as Hr
  iapply HΦ
  isplitl
  · reseal s
  · ipureintro; exact HelectionTimeout

theorem raft.wp_load_electionElapsed (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionElapsed"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.electionElapsed' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_heartbeatTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"heartbeatTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.heartbeatTimeout' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_randomizedElectionTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int)))
        (Val #(r.[raft, go!"randomizedElectionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.randomizedElectionTimeout' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_pendingConfIndex (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"pendingConfIndex"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.pendingConfIndex' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_uncommittedSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"uncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.uncommittedSize' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_maxUncommittedSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"maxUncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.maxUncommittedSize' $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_maxMsgSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryEncodingSize.ty)))
        (Val #(r.[raft, go!"maxMsgSize"])))
    {{ (v : entryEncodingSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.maxMsgSize' $$ Hr as Hr
  iapply HΦ; reseal s

/-! ### Stores to fields `NState` tracks -/

theorem raft.wp_store_Term (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Term"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with term := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.Term' v $$ Hr as Hr
  iapply HΦ; reseal { s with term := v }

theorem raft.wp_store_Vote (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Vote"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with vote := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.Vote' v $$ Hr as Hr
  iapply HΦ; reseal { s with vote := v }

theorem raft.wp_store_lead (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"lead"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with lead := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.lead' v $$ Hr as Hr
  iapply HΦ; reseal { s with lead := v }

/-- Stated at `stateW64 ro`, so the caller names the role; the Go code stores the
constant (`StateFollower` = `W64 0`), which unifies with `stateW64 .follower` by
computation. -/
theorem raft.wp_store_state (r : Loc) (id : w64) (s : NState) (ro : PRole) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) #(stateW64 ro))))
    {{ RET #(); ownRaftPhys cfg r id { s with role := ro } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.state' (stateW64 ro) $$ Hr as Hr
  iapply HΦ; reseal { s with role := ro }

theorem raft.wp_store_step (r : Loc) (id : w64) (s : NState) (f : GoFunc) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore stepFunc.ty))) (Val (PairV #(r.[raft, go!"step"]) #f)))
    {{ RET #(); ownRaftPhys cfg r id { s with stepfn := f } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.step' f $$ Hr as Hr
  iapply HΦ; reseal { s with stepfn := f }

/-! ### Stores to fields the abstraction does not track, and the pinned one -/

theorem raft.wp_store_tick (r : Loc) (id : w64) (s : NState) (f : GoFunc) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore (go.GoType.FunctionType (go.signature.Signature [] false [])))))
        (Val (PairV #(r.[raft, go!"tick"]) #f)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.tick' f $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_electionElapsed (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"electionElapsed"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.electionElapsed' v $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_heartbeatElapsed (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"heartbeatElapsed"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.heartbeatElapsed' v $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_randomizedElectionTimeout (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"randomizedElectionTimeout"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.randomizedElectionTimeout' v $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_pendingConfIndex (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"pendingConfIndex"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.pendingConfIndex' v $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_uncommittedSize (r : Loc) (id : w64) (s : NState) (v : entryPayloadSize) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore entryPayloadSize.ty)))
        (Val (PairV #(r.[raft, go!"uncommittedSize"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.uncommittedSize' v $$ Hr as Hr
  iapply HΦ; reseal s

/-- Only `false`: no learners are in scope. `switchToConfig` stores
`ok && pr.IsLearner`, which is `false` for every voter's `Progress`. -/
theorem raft.wp_store_isLearner (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.bool)))
        (Val (PairV #(r.[raft, go!"isLearner"]) #false)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.isLearner' false $$ Hr as Hr
  iapply HΦ; reseal s

/-- Only `None` (`W64 0`): no leader transfer is in scope. -/
theorem raft.wp_store_leadTransferee (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"leadTransferee"]) #(W64 0))))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.leadTransferee' (W64 0) $$ Hr as Hr
  iapply HΦ; reseal s

/-- Two states that are equal: for a state reached by a run of field stores and the
name a spec gives it (`becomeFollower s t l`, say). Proving the `=` with `rfl` is
cheap; leaving it to unification inside `iframe` can run for minutes (in Rocq;
notes/gotchas.md). -/
theorem ownRaftPhys_eq (r : Loc) (id : w64) (s1 s2 : NState) :
    s1 = s2 → ⊢ ownRaftPhys (GF := GF) cfg r id s1 -∗ ownRaftPhys cfg r id s2 := by
  intro H; subst H; iintro H; iexact H

end proof

/-! ### Accessors -/

set_option hygiene false in
/-- Rocq `split_field_proof`: one field of the struct points-to, with a wand taking
back *any* value. The generated `AccessStrict` store instance fixes the new value when
it is applied, which is too early for a value a later call produces (see
notes/gotchas.md); these unseal `l ↦ rv` instead. The pattern names the field `Hx` by
position and keeps every later field in one hypothesis `Hrest` (in Rocq, framing the 33
field points-tos one by one cost ~40s per lemma, this ~6s; 2026-09-24). -/
local macro "split_field_proof " pat:icasesPat : tactic =>
  `(tactic| (rw [typedPointsto_unseal_eq l rv]
             iintro ⟨Hf, %Hnn⟩
             simp only [TypedPointsto.typedPointstoDef]
             icases Hf with $pat
             iframe Hx
             iintro %x Hx
             rw [typedPointsto_unseal_eq (V := raft) l]
             simp only [TypedPointsto.typedPointstoDef]
             iframe
             ipureintro; exact Hnn))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem raft_split_trk (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗
      (∀ x, l.[raft, go!"trk"] ↦ x -∗ l ↦ { rv with trk' := x }) := by
  split_field_proof ⟨_, _, _, _, _, _, _, Hx, Hrest⟩

private theorem raft_split_msgs (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"msgs"] ↦ rv.msgs' ∗
      (∀ x, l.[raft, go!"msgs"] ↦ x -∗ l ↦ { rv with msgs' := x }) := by
  split_field_proof ⟨_, _, _, _, _, _, _, _, _, _, Hx, Hrest⟩

private theorem raft_split_msgsAA (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"msgsAfterAppend"] ↦ rv.msgsAfterAppend' ∗
      (∀ x, l.[raft, go!"msgsAfterAppend"] ↦ x -∗ l ↦ { rv with msgsAfterAppend' := x }) := by
  split_field_proof ⟨_, _, _, _, _, _, _, _, _, _, _, Hx, Hrest⟩

/-- The fields `RawNode.Ready`/`HasReady` touch, out of the struct at once (2026-10-05).
`readyWithoutAccept` sets `rd.Messages := r.msgs` and appends `r.msgsAfterAppend`'s
outgoing messages to it -- *in place*, into `r.msgs`' spare capacity -- and only
`acceptReady` then sets both queues to `nil`; in between it reads `r.id`, `r.Term`,
`r.raftLog` and the log. The struct is not `ownRaftPhys` in between (the queue's slack
belongs to `rd.Messages`, and a `send` would overwrite it), so the whole of `Ready` is
proved with the struct open through this accessor: the scalar fields it reads, the two
queues with their contents and capacity, the log, and a wand that takes them back with
any queues, any abstract outbox they relate to, and the log at any state. `readStates`
comes with its length, `0` in scope (`ownRaftMisc`). -/
private theorem raft_split_view (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"id"] ↦ rv.id' ∗
      l.[raft, go!"Term"] ↦ rv.Term' ∗
      l.[raft, go!"Vote"] ↦ rv.Vote' ∗
      l.[raft, go!"readStates"] ↦ rv.readStates' ∗
      l.[raft, go!"raftLog"] ↦ rv.raftLog' ∗
      l.[raft, go!"state"] ↦ rv.state' ∗
      l.[raft, go!"msgs"] ↦ rv.msgs' ∗
      l.[raft, go!"msgsAfterAppend"] ↦ rv.msgsAfterAppend' ∗
      l.[raft, go!"lead"] ↦ rv.lead' ∗
      (∀ x y, l.[raft, go!"id"] ↦ rv.id' -∗
              l.[raft, go!"Term"] ↦ rv.Term' -∗
              l.[raft, go!"Vote"] ↦ rv.Vote' -∗
              l.[raft, go!"readStates"] ↦ rv.readStates' -∗
              l.[raft, go!"raftLog"] ↦ rv.raftLog' -∗
              l.[raft, go!"state"] ↦ rv.state' -∗
              l.[raft, go!"msgs"] ↦ x -∗
              l.[raft, go!"msgsAfterAppend"] ↦ y -∗
              l.[raft, go!"lead"] ↦ rv.lead' -∗
              l ↦ { rv with msgs' := x, msgsAfterAppend' := y }) := by
  rw [typedPointsto_unseal_eq l rv]
  iintro ⟨Hf, %Hnn⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases Hf with ⟨Hid, HTerm, HVote, Hrs, Hlog, _, _, _, Hst, _, Hm, Hma, Hld, Hrest⟩
  iframe Hid HTerm HVote Hrs Hlog Hst Hm Hma Hld
  iintro %x %y Hid HTerm HVote Hrs Hlog Hst Hm Hma Hld
  rw [typedPointsto_unseal_eq (V := raft) l]
  simp only [TypedPointsto.typedPointstoDef]
  iframe
  ipureintro; exact Hnn

private theorem raft_split_readOnly (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"readOnly"] ↦ rv.readOnly' ∗
      (∀ x, l.[raft, go!"readOnly"] ↦ x -∗ l ↦ { rv with readOnly' := x }) := by
  split_field_proof ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, Hx, Hrest⟩

/-- Two fields at once, `raftLog` (read-only here) and `trk`: for
`ownRaftPhys_retrack`. -/
private theorem raft_split_raftLog_trk (l : Loc) (rv : raft) :
    ⊢ (l ↦ rv : IProp GF) -∗
      l.[raft, go!"raftLog"] ↦ rv.raftLog' ∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗
      (∀ x, l.[raft, go!"raftLog"] ↦ rv.raftLog' -∗
            l.[raft, go!"trk"] ↦ x -∗ l ↦ { rv with trk' := x }) := by
  rw [typedPointsto_unseal_eq l rv]
  iintro ⟨Hf, %Hnn⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases Hf with ⟨_, _, _, _, Hy, _, _, Hx, Hrest⟩
  iframe Hx Hy
  iintro %x Hy Hx
  rw [typedPointsto_unseal_eq (V := raft) l]
  simp only [TypedPointsto.typedPointstoDef]
  iframe
  ipureintro; exact Hnn

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- The tracker, as the tracker's own specs take it: the embedded struct's points-to
and `ownTracker`. The wand takes it back at any tracker value and vote tally, and at
the same progress map and `Progress` values (`NState.progress` is stable: nothing on
the election path inserts into the map). A map lookup `r.trk.Progress[i]` is done on
what this hands out, with `ownTracker_progress_map` / `wp_tracker_progress_lookup`; a
function that changes a `Progress` uses `ownRaftPhys_tracker_prvals`. -/
theorem ownRaftPhys_tracker (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' votes', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨votes', s.progress, s.prvals⟩ -∗
           ownRaftPhys cfg r id { s with votes := votes' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %votes' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  reseal { s with votes := votes' }

/-- The same, put back at the same tally: the wand gives `ownRaftPhys` at `s` itself
rather than at `{ s with votes := s.votes }`, so a read-only use (a map lookup,
`JointConfig.IDs`), or a split and re-seal repeated inside a `Visit` closure, does not
pile up setters. -/
theorem ownRaftPhys_tracker_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tvx, r.[raft, go!"trk"] ↦ tvx -∗
           ownTracker cfg tvx ⟨s.votes, s.progress, s.prvals⟩ -∗
           ownRaftPhys cfg r id s) := by
  iintro Hphys
  icases ownRaftPhys_tracker cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  iexists tv
  iframe Htrkf Htrk
  iintro %tvx Htrkf Htrk
  ihave Hphys := Hback $$ %tvx %s.votes Htrkf Htrk
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ Hphys

/-- The tracker, put back with new `Progress` values (at the same tally): for a
function that writes a `Progress` -- `reset`'s `Visit` closure, `becomeLeader`'s
`RecentActive` and `BecomeReplicate`, `SentEntries`. -/
theorem ownRaftPhys_tracker_prvals (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, s.progress, pvs'⟩ -∗
           ownRaftPhys cfg r id { s with prvals := pvs' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  reseal { s with prvals := pvs' }

/-- One peer's `Progress`, borrowed out of the struct by its key at the value
`NState.prvals` records, and given back at that value -- for a read (`IsPaused`, field
loads, `Inflights.Full`). The lookup of `r.trk.Progress[to]` itself goes through
`ownRaftPhys_tracker_same`: it reads the tracker field. The two lookups are premises
inside the logic, so that `s` is fixed by the struct hypothesis the lemma is applied
to, not by the lookups' types: `icases ownRaftPhys_pr … $$ Hphys %Hlk %Hv with …`. -/
theorem ownRaftPhys_pr (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗ (ownProgress pr p -∗ ownRaftPhys cfg r id s) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup_same cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro Hp
  ihave Htrk := Hpb $$ Hp
  iapply Hback $$ Htrkf Htrk

/-- The same, given back at new values, which the state then records -- for a write
(`SentEntries`). -/
theorem ownRaftPhys_pr_upd (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗
         ownRaftPhys cfg r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhys_tracker_prvals cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro %p'' Hp
  ihave Htrk := Hpb $$ %p'' Hp
  iapply Hback $$ Htrkf Htrk

/-- A write that does not need to know the value it overwrites (`SentCommit`). -/
theorem ownRaftPhys_pr_any (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ∃ p, ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗
         ownRaftPhys cfg r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk
  icases ownRaftPhys_tracker_prvals cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  iexists p'
  iframe Hp
  iintro %p'' Hp
  ihave Htrk := Hpb $$ %p'' Hp
  iapply Hback $$ Htrkf Htrk

/-- The log, at the state `s` records, put back at any state. This is the accessor for
a function that changes the log (`appendEntry`'s `append`, `loadState`'s `committed`,
`newRaft`'s `appliedTo`). -/
theorem ownRaftPhys_log_at (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftLog s.log s.logst ∗
      (∀ ls', ownRaftLog s.log ls' -∗ ownRaftPhys cfg r id { s with logst := ls' }) := by
  iintro H
  iNamed_phys H
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlog
  iintro %ls' Hlog
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  reseal { s with logst := ls' }

/-- The log at the state `s` records, put back at that same state: for a read through
`ownRaftLog` (a `raftLog` method that keeps its state, a field load through
`ownRaftLog_struct`). The wand gives `ownRaftPhys` at `s` itself, so no
`ownRaftPhys_eq` is needed afterwards. -/
theorem ownRaftPhys_log_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftLog s.log s.logst ∗
      (ownRaftLog s.log s.logst -∗ ownRaftPhys cfg r id s) := by
  iintro H
  icases ownRaftPhys_log_at cfg r id s $$ H with ⟨Hlog, Hback⟩
  iframe Hlog
  iintro Hlog
  ihave H := Hback $$ %s.logst Hlog
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ H

/-- `r.msgs`, append-only: a message `m'` appended joins the abstract outbox (at the
end, up to permutation -- see `Houtbox`) as whatever `msgAbs` says it contributes:
nothing for a type the model does not describe, else its abstraction, given
`m'.Entries ↦*□ ents`. -/
theorem ownRaftPhys_msgs (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ sl ms, r.[raft, go!"msgs"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgs"] ↦ sl' -∗ sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ownRaftPhys cfg r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_phys H
  icases raft_split_msgs r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgs', msgs
  iframe Hf Hmsgs Hmsgs_cap
  iintro %sl' %m' %a Hf Hmsgs Hmsgs_cap #Ha
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) (msgs ++ [m']) msgsAA $$ []
  · unfold outboxRel
    iexists as1 ++ [a], as2
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      refine (Ho.append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    isplitr
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H1 Ha
    · iexact H2
  iapply ownRaftPhys_intro _ _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgs' := sl' } (msgs ++ [m']) msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- `r.msgsAfterAppend`, likewise. -/
theorem ownRaftPhys_msgsAA (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ sl ms, r.[raft, go!"msgsAfterAppend"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgsAfterAppend"] ↦ sl' -∗
           sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ownRaftPhys cfg r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_phys H
  icases raft_split_msgsAA r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgsAfterAppend', msgsAA
  iframe Hf HmsgsAA HmsgsAA_cap
  iintro %sl' %m' %a Hf HmsgsAA HmsgsAA_cap #Ha
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) msgs (msgsAA ++ [m']) $$ []
  · unfold outboxRel
    iexists as1, as2 ++ [a]
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      simpa [List.append_assoc] using Ho.append_right (List.filterMap _root_.id [a])
    isplitr
    · iexact H1
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H2 Ha
  iapply ownRaftPhys_intro _ _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgsAfterAppend' := sl' } msgs (msgsAA ++ [m']) lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The `readOnly` object. Election never reads it; `reset` replaces it. The object
comes out at a record with no pending requests (phase-1 scope, `ownRaftMisc`) and goes
back at any record with none: `reset` puts in a fresh one. -/
theorem ownRaftPhys_readOnly (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ (ro : Loc) (rr : ReadOnly),
        ⌜rr.pending = []⌝ ∗
        r.[raft, go!"readOnly"] ↦ ro ∗ ownReadOnly ro rr ∗
        (∀ (ro' : Loc) (rr' : ReadOnly), ⌜rr'.pending = []⌝ -∗
           r.[raft, go!"readOnly"] ↦ ro' -∗ ownReadOnly ro' rr' -∗
           ownRaftPhys cfg r id s) := by
  iintro H
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  icases Hmisc with ⟨%rr, Hmisc⟩
  iNamed Hmisc
  icases raft_split_readOnly r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.readOnly', rr
  isplitr
  · ipureintro; exact Hro_pending
  iframe Hf Hro_obj
  iintro %ro' %rr' %Hpend' Hf Hro_obj
  ihave Hr := Hback $$ %ro' Hf
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' ro' rv.pendingReadIndexMessages'
      $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    iexists rr'
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap
    ipureintro; exact Hpend'
  reseal s

/-- Rocq `own_raft_phys_view`: the struct open for `RawNode.Ready` (see
`raft_split_view`). -/
theorem ownRaftPhys_view (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      iprop(∃ (rs sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
        "Hf_id" ∷ r.[raft, go!"id"] ↦ id ∗
        "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
        "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
        "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rs ∗
        "%Hrs" ∷ ⌜rs.len = W64 0⌝ ∗
        "Hf_raftLog" ∷ r.[raft, go!"raftLog"] ↦ s.log ∗
        "Hf_state" ∷ r.[raft, go!"state"] ↦ stateW64 s.role ∗
        "Hf_lead" ∷ r.[raft, go!"lead"] ↦ s.lead ∗
        "Hf_msgs" ∷ r.[raft, go!"msgs"] ↦ sl1 ∗ "Hmsgs" ∷ sl1 ↦* ms1 ∗
        "Hmsgs_cap" ∷ ownSliceCap raftpb.Message sl1 (DFrac.own 1) ∗
        "Hf_msgsAA" ∷ r.[raft, go!"msgsAfterAppend"] ↦ sl2 ∗ "HmsgsAA" ∷ sl2 ↦* ms2 ∗
        "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message sl2 (DFrac.own 1) ∗
        "#Houtbox" ∷ outboxRel s.outbox ms1 ms2 ∗
        "Hlog" ∷ ownRaftLog s.log s.logst ∗
        "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                      (ls' : LogState),
            r.[raft, go!"id"] ↦ id -∗
            r.[raft, go!"Term"] ↦ s.term -∗
            r.[raft, go!"Vote"] ↦ s.vote -∗
            r.[raft, go!"readStates"] ↦ rs -∗
            r.[raft, go!"raftLog"] ↦ s.log -∗
            r.[raft, go!"state"] ↦ stateW64 s.role -∗
            r.[raft, go!"lead"] ↦ s.lead -∗
            r.[raft, go!"msgs"] ↦ sl1' -∗ sl1' ↦* ms1' -∗
            ownSliceCap raftpb.Message sl1' (DFrac.own 1) -∗
            r.[raft, go!"msgsAfterAppend"] ↦ sl2' -∗ sl2' ↦* ms2' -∗
            ownSliceCap raftpb.Message sl2' (DFrac.own 1) -∗
            outboxRel o ms1' ms2' -∗
            ownRaftLog s.log ls' -∗
            ownRaftPhys cfg r id { s with outbox := o, logst := ls' })) := by
  iintro H
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  icases Hmisc with ⟨%rr, Hmisc⟩
  iNamed Hmisc
  ihave %Hrl := ownSlice_len _ _ _ $$ HreadStates
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' rv.readOnly'
      rv.pendingReadIndexMessages' $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    iexists rr
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap
    ipureintro; exact Hro_pending
  icases raft_split_view r rv $$ Hr with
    ⟨Hfid, HfTerm, HfVote, Hfrs, Hflog, Hfst, Hfm, Hfma, Hfld, Hback⟩
  ihave Hfid : r.[raft, go!"id"] ↦ id $$ [Hfid]
  · rw [← Hid]; iexact Hfid
  ihave HfTerm : r.[raft, go!"Term"] ↦ s.term $$ [HfTerm]
  · rw [← Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ s.vote $$ [HfVote]
  · rw [← Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ s.log $$ [Hflog]
  · rw [← Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ stateW64 s.role $$ [Hfst]
  · rw [← Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ s.lead $$ [Hfld]
  · rw [← Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iexists rv.readStates', rv.msgs', rv.msgsAfterAppend', msgs, msgsAA
  simp only [named]
  iframe Hfid HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm Hfma Hmsgs Hmsgs_cap HmsgsAA
    HmsgsAA_cap Houtbox Hlog
  isplitr
  · ipureintro
    obtain ⟨Hl1, Hl2⟩ := Hrl
    simp only [List.length_nil] at Hl1
    apply BitVec.eq_of_toInt_eq
    simp only [sint.nat] at Hl1
    simp only [sint.Z] at Hl2
    rw [show (W64 0).toInt = 0 by rfl]
    omega
  iintro %sl1' %sl2' %ms1' %ms2' %o %ls' Hfid HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm Hmsgs
    Hmsgs_cap Hfma HmsgsAA HmsgsAA_cap #Houtbox' Hlog
  ihave Hfid : r.[raft, go!"id"] ↦ rv.id' $$ [Hfid]
  · rw [Hid]; iexact Hfid
  ihave HfTerm : r.[raft, go!"Term"] ↦ rv.Term' $$ [HfTerm]
  · rw [Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ rv.Vote' $$ [HfVote]
  · rw [Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hflog]
  · rw [Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ rv.state' $$ [Hfst]
  · rw [Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ rv.lead' $$ [Hfld]
  · rw [Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %sl1' %sl2' Hfid HfTerm HfVote Hfrs Hflog Hfst Hfm Hfma Hfld
  iapply ownRaftPhys_intro _ _ _ { s with outbox := o, logst := ls' }
      { rv with msgs' := sl1', msgsAfterAppend' := sl2' } ms1' ms2' lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'

end proof

/-! ### Reconfiguration

The one accessor that changes `ownRaftPhys`'s `cfg` index: the tracker comes out at
the old configuration and goes back at a new one, with a new progress map
(`NState.progress`). Only `ownTracker` mentions `cfg`, so nothing else is
re-established. `switchToConfig` is the one user (for `newRaft`'s move from the empty
configuration to the persisted one). -/
section reconfig
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem ownRaftPhys_reconfig (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, prs', pvs'⟩ -∗
           ownRaftPhys cfg r id { s with progress := prs', prvals := pvs' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %prs' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  iapply ownRaftPhys_intro cfg r id { s with progress := prs', prvals := pvs' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The tracker replaced while the log is in use (2026-10-02): `restore` stores a fresh
tracker into `r.trk`, loads it back, calls `r.raftLog.lastIndex()` and only then hands
the new tracker's (empty) voter map to `confchange.Restore` -- so between the store and
that call the struct cannot be re-sealed without losing which tracker value it holds.
This accessor hands out the tracker field and the `raftLog` field (read-only: its value
is `s.log`) together with the log, and takes them back at any tracker -- a new
configuration `cfg`, tally, progress map and values -- and any log state. -/
theorem ownRaftPhys_retrack (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        r.[raft, go!"raftLog"] ↦ s.log ∗
        ownRaftLog s.log s.logst ∗
        (∀ tv' votes' prs' pvs' ls',
           r.[raft, go!"raftLog"] ↦ s.log -∗
           r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨votes', prs', pvs'⟩ -∗
           ownRaftLog s.log ls' -∗
           ownRaftPhys cfg r id
             { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_raftLog_trk r rv $$ Hr with ⟨Hlf, Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  ihave Hlf : r.[raft, go!"raftLog"] ↦ s.log $$ [Hlf]
  · rw [← Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlf Hlog
  iintro %tv' %votes' %prs' %pvs' %ls' Hlf Hf Htrk Hlog
  ihave Hlf : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hlf]
  · rw [Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %tv' Hlf Hf
  iapply ownRaftPhys_intro cfg r id
      { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCheckQuorum HnoLearner
    HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

end reconfig

set_option hygiene false in
/-- A logging call through `r.logger`, once the raft fields its arguments read have
been loaded (each with its own lemma, by the caller): the variadic argument slice, the
load of `r.logger`, and the logger spec. Works on `Hphys`. A fixed sequence of steps,
no search: it applies the same lemmas in the same order every time.

The argument slice is kept (anonymously) and its capacity dropped, as in Rocq. The
loaded logger is named `lok` and its `isLogger` (`Hlg`) is cleared after the call. The
method side condition `meth ∈ logMethods` is Rocq's `solve_log_method`, here `decide`.
Depending on the arguments, `wp_slice_literal`'s equation may already be discharged,
hence the `try`s (as in Rocq). -/
macro "wp_raft_log" : tactic => `(tactic| (
  wp_apply Perennial.wp_slice_literal
  wp_pures
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  wp_pures; wp_load; wp_pures
  wp_apply Perennial.EtcdGrove.raft.wp_load_logger $$ Hphys as %lok ⟨Hphys, #Hlg⟩
  wp_pures
  wp_apply Perennial.EtcdGrove.Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  iclear Hlg))

end EtcdGrove
end Perennial
