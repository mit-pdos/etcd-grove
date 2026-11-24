/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/Concrete.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: the agreement invariant over the model's configurations (`notes/unit-A1.md`).

A configuration `c` reachable by `kahn.GRun` from `Cfg.init gNet` comes with a ghost history
`G : GG` (one `Gh Val` per instance, `Abstract.lean`), monotone along the run. `CInv c G` is the
inductive invariant:
* per instance `(q, i)` (leader `L = rowOf q`, ghost `g = G q i`, ballots `bal = balOf c q i`):
  - `AInv g bal L` (one proposal per ballot, A3's `SafeAt` for every proposal and restart, the fast
    path's facts);
  - every copy (`CopyOk`): its ballot/vbal shape, its votes as the ghost records them (no votes while
    NONE/PREACCEPTED*, the latest vote while ACCEPTED), committed copies chosen, pre-accepted copies
    at a nonzero vbal come from a restart, unchanged ballot-0 copies carry the creation value, the
    leader's untouched ballot-0 copy (no Accept at 0, no fast commit yet), a recoverer's own fresh
    ballot (no proposal yet), a preparing recoverer's candidate (`RIOk`, `Decide.lean`), the
    unchanged pre-accepts' fate (`eqTrack`);
  - every message about the instance (`MsgOk`): what its sender's state was (`RepOk` for a prepare
    reply), proposals for Accepts, chosen values for Commits, ...;
* the replicas' ids.

`committed_chosen`: committed values are chosen. With `chosen_unique` (`Abstract.lean`) and the
run's monotonicity (`inv_run`) this gives `agree_run` (`Pure/Agree.lean`).

`inv_step` (preservation by one step, `Inv.lean`) is the bulk of the proof: see `notes/unit-A1.md`
for its status. (Hub request H-A1-1, `notes/hub-requests2.md`, found agreement false once `seq` wrapped;
fixed in the model since, G41: PREACCEPTED_EQ iff the attributes are unchanged.)
-/
module

public import Dsverify.Proof.gryff.PureA.PrepareReply

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-- The leader of row `q` as an acceptor (rows outside `0..2` have no instances: `0`). -/
def rowOf (q : w32) : Fin 3 :=
  if h : 0 ≤ sint.Z q ∧ sint.Z q < 3 then ⟨(sint.Z q).toNat, by omega⟩ else 0

/-- Replica `a`'s copy of instance `(q, i)`. -/
def cpOf (c : Cfg gNet) (a : Fin 3) (q i : w32) : Option Copy := (c.st a).inst q i

/-- The acceptors' ballots for instance `(q, i)`. -/
def balOf (c : Cfg gNet) (q i : w32) : Fin 3 → Option Int :=
  fun a => (cpOf c a q i).map (fun cp => sint.Z cp.ballot)

/-- The ghost history: one `Gh` per instance. -/
abbrev GG := w32 → w32 → Gh Val

/-- The empty history. -/
def Gh.empty : Gh Val := ⟨fun _ _ _ => False, fun _ _ => False, fun _ => False, fun _ => False,
  fun _ => False, fun _ => False⟩

/-- Ballot `b` belongs to recoverer `R` (`makeUniqueBallot R _` with a round `≥ 1`). -/
def Own (b : Int) (R : Fin 3) : Prop := ∃ k : Int, 1 ≤ k ∧ b = 16 * k + R.val

def isCommitted (st : w8) : Prop := st = St.COMMITTED ∨ st = St.EXECUTED
def isPre (st : w8) : Prop := st = St.PREACCEPTED ∨ st = St.PREACCEPTED_EQ

/-- A value's attributes are the creation's. -/
def CreAttrs (g : Gh Val) (seq : w32) (deps : Deps) (base : ValTag) : Prop :=
  ∃ v, g.cre v ∧ v.2 = (seq, deps, base)

section defs
variable (c : Cfg gNet) (G : GG)

/-- Facts about replica `a`'s copy `cp` of instance `(q, i)`. -/
structure CopyOk (q i : w32) (a : Fin 3) (cp : Copy) : Prop where
  nonneg : 0 ≤ sint.Z cp.ballot
  ballotForm : cp.ballot = 0 ∨ ∃ R, Own (sint.Z cp.ballot) R
  vbalLe : sint.Z cp.vbal ≤ sint.Z cp.ballot
  stOk : cp.status = St.NONE ∨ isPre cp.status ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status
  noVotes : (cp.status = St.NONE ∨ isPre cp.status) → ∀ b u, ¬ (G q i).acc a b u
  accVote : cp.status = St.ACCEPTED →
    (G q i).acc a (sint.Z cp.vbal) cp.valA ∧ ∀ b u, (G q i).acc a b u → b ≤ sint.Z cp.vbal
  committed : isCommitted cp.status → Chosen (G q i) cp.valA
  rstVbal : isPre cp.status → cp.vbal ≠ 0 → 0 < sint.Z cp.vbal ∧ (G q i).rst (sint.Z cp.vbal)
  eqCre : cp.status = St.PREACCEPTED_EQ → cp.vbal = 0 → a ≠ rowOf q → (G q i).cre cp.valA
  leader0 : a = rowOf q → cp.ballot = 0 → cp.status = St.PREACCEPTED →
    (G q i).cre cp.valA ∧ (∀ u, ¬ (G q i).prop 0 u) ∧ (∀ v, ¬ (G q i).fast v) ∧
      ∀ lb, cp.lb = some lb → lb.preAcceptOKs = 0
  ownFresh : (cp.status = St.NONE ∨ isPre cp.status) → Own (sint.Z cp.ballot) a →
    ∀ u, ¬ (G q i).prop (sint.Z cp.ballot) u
  preparing : ∀ lb, cp.lb = some lb → lb.preparing = true → ¬ isCommitted cp.status →
    Own (sint.Z cp.ballot) a →
    RIOk (G q i) (balOf c q i) (rowOf q) (sint.Z cp.ballot) a lb.recoveryInst ∧
      ¬ (G q i).rst (sint.Z cp.ballot) ∧ (∀ u, ¬ (G q i).prop (sint.Z cp.ballot) u) ∧
      0 ≤ sint.Z lb.prepareOKs ∧ sint.Z lb.prepareOKs ≤ 1
  eqTrack : a ≠ rowOf q → (G q i).eq a →
    cp.status = St.ACCEPTED ∨ isCommitted cp.status ∨
      (cp.status = St.PREACCEPTED_EQ ∧ cp.vbal = 0) ∨ RstBelow (G q i) (sint.Z cp.ballot)

/-- Facts about a message `m` in flight to replica `d`. -/
def MsgOk (d : Fin 3) : Msg → Prop
  | .preAccept m =>
    (m.ballot = 0 → d ≠ rowOf m.replica ∧ m.leaderId = rid32 (rowOf m.replica) ∧
      (G m.replica m.inst).cre (m.cmds, m.seq, m.deps, m.base) ∧
      (∀ cp, cpOf c d m.replica m.inst = some cp →
        0 < sint.Z cp.ballot ∨ cp.status = St.ACCEPTED ∨ isCommitted cp.status) ∧
      (c.inflight d).count (.preAccept m) = 1) ∧
    (m.ballot ≠ 0 → 0 < sint.Z m.ballot ∧ (G m.replica m.inst).rst (sint.Z m.ballot) ∧
      ∃ R, Own (sint.Z m.ballot) R ∧ m.leaderId = rid32 R ∧ R ≠ d)
  | .preAcceptReply m =>
    (m.ballot = 0 → d = rowOf m.replica ∧
      (m.ok ≠ FALSE → CreAttrs (G m.replica m.inst) m.seq m.deps m.base →
        ∃ X, X ≠ rowOf m.replica ∧ (G m.replica m.inst).eq X) ∧
      (m.ok ≠ FALSE → ∃ v, (G m.replica m.inst).cre v ∧ m.deps.length = v.2.2.1.length ∧
        (∀ k, (k = (rowOf m.replica).val ∨ 3 ≤ k) → m.deps.at k = v.2.2.1.at k) ∧
        (m.base.t.gt v.2.2.2.t = false → m.base = v.2.2.2))) ∧
    (m.ballot ≠ 0 → m.ok ≠ FALSE → Own (sint.Z m.ballot) d ∧ (G m.replica m.inst).rst (sint.Z m.ballot))
  | .preAcceptOK m => ∃ X, X ≠ d ∧ (G (rid32 d) m.inst).eq X
  | .accept m =>
    (G m.replica m.inst).prop (sint.Z m.ballot) (m.cmds, m.seq, m.deps, m.base) ∧
      (∃ R, m.leaderId = rid32 R ∧ R ≠ d ∧
        ((m.ballot = 0 ∧ R = rowOf m.replica) ∨ Own (sint.Z m.ballot) R) ∧
        (G m.replica m.inst).acc R (sint.Z m.ballot) (m.cmds, m.seq, m.deps, m.base))
  | .acceptReply m =>
    (m.ok ≠ FALSE → ∃ Y, Y ≠ d ∧ ∃ v, (G m.replica m.inst).acc Y (sint.Z m.ballot) v ∧
        (G m.replica m.inst).acc d (sint.Z m.ballot) v) ∧
      (m.ok ≠ FALSE → (m.ballot = 0 ∧ d = rowOf m.replica) ∨ Own (sint.Z m.ballot) d)
  | .commit m => Chosen (G m.replica m.inst) m.valA
  | .prepare m =>
    0 < sint.Z m.ballot ∧ ∃ R, Own (sint.Z m.ballot) R ∧ m.leaderId = rid32 R ∧ R ≠ d ∧
      ∃ B, balOf c m.replica m.inst R = some B ∧ sint.Z m.ballot ≤ B
  | .prepareReply m =>
    (isCommitted m.status → Chosen (G m.replica m.inst) m.valA) ∧
    (m.ok = TRUE → (∃ B, balOf c m.replica m.inst d = some B ∧ sint.Z m.ballot ≤ B) ∧
      ∃ Y, m.acceptorId = rid32 Y ∧ Y ≠ d ∧ Own (sint.Z m.ballot) d ∧
      -- `RepOk` only while nothing was proposed at the ballot (A1b): a Prepare still in flight
      -- after the recoverer's decision may meet a copy that accepted at the ballot itself
      (¬ isCommitted m.status → (∀ u, ¬ (G m.replica m.inst).prop (sint.Z m.ballot) u) →
        RepOk (G m.replica m.inst) (balOf c m.replica m.inst) (rowOf m.replica) (sint.Z m.ballot) Y m)) ∧
    -- replies are OK or NACK (A1b: `handlePrepareReply` tests `ok = FALSE`)
    (m.ok = TRUE ∨ m.ok = FALSE)
  | _ => True

/-- A Prepare for instance `(q, i)` at ballot `b`. -/
def isPrepareAt (q i b : w32) : Msg → Bool
  | .prepare m => m.replica == q && m.inst == i && m.ballot == b
  | _ => false

/-- An OK PrepareReply for instance `(q, i)` at ballot `b` from replica `Y`. -/
def isOKReplyAt (q i b : w32) (Y : Fin 3) : Msg → Bool
  | .prepareReply m => m.replica == q && m.inst == i && m.ballot == b && m.ok == TRUE &&
      m.acceptorId == rid32 Y
  | _ => false

/-- The instance a message names (`none`: not an EPaxos message about an instance;
`PreAcceptOK` names `(its receiver, inst)`, handled by `MsgOk`). -/
def msgInst : Msg → Option (w32 × w32)
  | .preAccept m => some (m.replica, m.inst)
  | .preAcceptReply m => some (m.replica, m.inst)
  | .accept m => some (m.replica, m.inst)
  | .acceptReply m => some (m.replica, m.inst)
  | .commit m => some (m.replica, m.inst)
  | .prepare m => some (m.replica, m.inst)
  | .prepareReply m => some (m.replica, m.inst)
  | _ => none

/-- Facts about instance `(q, i)`. -/
structure InstOk (q i : w32) : Prop where
  ainv : AInv (G q i) (balOf c q i) (rowOf q)
  copies : ∀ a cp, cpOf c a q i = some cp → CopyOk c G q i a cp
  noCopy : ∀ a, cpOf c a q i = none → (∀ b u, ¬ (G q i).acc a b u) ∧ ¬ (G q i).eq a
  fastL : ∀ v, (G q i).fast v → ∃ cp, cpOf c (rowOf q) q i = some cp ∧ isCommitted cp.status
  leaderCopy : (∃ a cp, cpOf c a q i = some cp) →
    ∃ cp, cpOf c (rowOf q) q i = some cp ∧ cp.status ≠ St.NONE
  ownMono : ∀ b R, Own b R → ((G q i).rst b ∨ ∃ u, (G q i).prop b u) →
    ∃ B, balOf c q i R = some B ∧ b ≤ B
  /-- An instance without copies has no creation and no proposal (A1a). -/
  fresh : (∀ a, cpOf c a q i = none) → (∀ v, ¬ (G q i).cre v) ∧ ∀ b u, ¬ (G q i).prop b u

/-- **The agreement invariant.** -/
structure CInv : Prop where
  ids : ∀ a, (c.st a).id = rid32 a
  inst : ∀ q i, InstOk c G q i
  msgs : ∀ d m, m ∈ c.inflight d → MsgOk c G d m
  /-- Rows are created by their owner: a replica's `crt[q]` is at most `q`'s own. -/
  crtOwn : ∀ a q : Fin 3, sint.Z ((c.st a).crt (rid32 q)) ≤ sint.Z ((c.st q).crt (rid32 q))
  /-- ... every copy of row `q` is below `q`'s `crt[q]` (and rows outside `0..2` have no copies) -/
  copyBelow : ∀ a q j cp, cpOf c a q j = some cp →
    rowOk q = true ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((c.st (rowOf q)).crt q)
  /-- ... and so is every instance a message names. -/
  msgBelow : ∀ d m q j, m ∈ c.inflight d → msgInst m = some (q, j) →
    rowOk q = true ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ((c.st (rowOf q)).crt q)
  /-- `crtInstance` has its three entries (A1a). -/
  crtLen : ∀ a, (c.st a).crtInstance.length = 3
  /-- The leader has a copy, not NONE, of each instance of its row below its `crt` (A1a). -/
  leaderHas : ∀ (q : Fin 3) j, 0 ≤ sint.Z j → sint.Z j < sint.Z ((c.st q).crt (rid32 q)) →
    ∃ cp, cpOf c q (rid32 q) j = some cp ∧ cp.status ≠ St.NONE
  /-- Message multiplicities while recovering (`prepareOKs ≤ 1` between replies): per peer `Y` at
  most one Prepare or OK reply in flight at a preparing ballot `b`; once one OK was counted
  (`prepareOKs = 1` while still preparing: only the leader's PREACCEPTED reply returns early), the
  leader's is gone. -/
  prepMult : ∀ R q i cp lb, cpOf c R q i = some cp → cp.lb = some lb → lb.preparing = true →
    ¬ isCommitted cp.status → Own (sint.Z cp.ballot) R →
    (∀ Y : Fin 3, (c.inflight Y).countP (isPrepareAt q i cp.ballot) +
      (c.inflight R).countP (isOKReplyAt q i cp.ballot Y) ≤ 1) ∧
    (sint.Z lb.prepareOKs = 1 → R ≠ rowOf q ∧
      (c.inflight (rowOf q)).countP (isPrepareAt q i cp.ballot) = 0 ∧
      (c.inflight R).countP (isOKReplyAt q i cp.ballot (rowOf q)) = 0)

end defs

/-- `leader0` for a copy whose bookkeeping changed but not its PreAccept-OK count (A1c). -/
theorem leader0_lb {c : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy} {lb lb' : LB}
    (h : CopyOk c G q i a cp) (hl : cp.lb = some lb) (e : lb'.preAcceptOKs = lb.preAcceptOKs) :
    a = rowOf q → cp.ballot = 0 → cp.status = St.PREACCEPTED →
      (G q i).cre cp.valA ∧ (∀ u, ¬ (G q i).prop 0 u) ∧ (∀ v, ¬ (G q i).fast v) ∧
        ∀ lb2, ({ cp with lb := some lb' } : Copy).lb = some lb2 → lb2.preAcceptOKs = 0 :=
  fun h1 h2 h3 =>
    let k := h.leader0 h1 h2 h3
    ⟨k.1, k.2.1, k.2.2.1, fun lb2 hl2 => by cases hl2; rw [e]; exact k.2.2.2 lb hl⟩

/-! ## Committed values are chosen -/

theorem committed_copy_chosen {c : Cfg gNet} {G : GG} (I : CInv c G) {a : Fin 3} {q i : w32}
    {cp : Copy} (h : (c.st a).inst q i = some cp) (hs : isCommitted cp.status) :
    Chosen (G q i) cp.valA :=
  ((I.inst q i).copies a cp h).committed hs

theorem committed_commit_chosen {c : Cfg gNet} {G : GG} (I : CInv c G) {d : Fin 3}
    {m : ECommitM} (h : Msg.commit m ∈ c.inflight d) : Chosen (G m.replica m.inst) m.valA :=
  I.msgs d _ h

theorem committed_reply_chosen {c : Cfg gNet} {G : GG} (I : CInv c G) {d : Fin 3}
    {m : PrepareReplyM} (h : Msg.prepareReply m ∈ c.inflight d)
    (hs : isCommitted m.status) : Chosen (G m.replica m.inst) m.valA :=
  (I.msgs d _ h).1 hs

/-! ## Along a run -/

/-- `Chosen` only grows with the history. -/
theorem chosen_mono {g g' : Gh Val} (h : g.Le g') {v : Val} (hv : Chosen g v) : Chosen g' v := by
  rcases hv with hv | ⟨b, a1, a2, ha, h1, h2⟩
  · exact Or.inl (h.fast v hv)
  · exact Or.inr ⟨b, a1, a2, ha, h.acc _ _ _ h1, h.acc _ _ _ h2⟩

/-- The initial configuration, with the empty history. -/
theorem inv_init : CInv (Cfg.init gNet) (fun _ _ => Gh.empty) where
  ids _ := rfl
  inst q i :=
    { ainv := { prop_uniq := fun _ _ _ h => h.elim, acc_prop := fun _ _ _ h => h.elim,
                prop_nonneg := fun _ _ h => h.elim, prop_safe := fun _ _ h => h.elim,
                rst_safe := fun _ h => h.elim, cre_uniq := fun _ _ h => h.elim,
                fast_cre := fun _ h => h.elim, fast_eq := fun _ h => h.elim,
                fast_noprop := fun _ h => h.elim }
      copies := fun _ _ h => by cases h
      noCopy := fun _ _ => ⟨fun _ _ h => h, fun h => h⟩
      fastL := fun _ h => h.elim
      leaderCopy := fun ⟨_, _, h⟩ => by cases h
      ownMono := fun _ _ _ h => by rcases h with h | ⟨_, h⟩ <;> exact h.elim
      fresh := fun _ => ⟨fun _ h => h, fun _ _ h => h⟩ }
  msgs _ _ h := by cases h
  crtOwn _ _ := Int.le_refl _
  copyBelow _ _ _ _ h := by cases h
  msgBelow _ _ _ _ h := by cases h
  crtLen _ := rfl
  leaderHas q j h0 h1 := by
    exfalso
    have : ((Cfg.init gNet).st q).crt (rid32 q) = 0 := by
      show (RState.init q.val).crtInstance.getD _ 0 = 0
      simp only [RState.init]
      have := q.isLt
      rcases (rid32 q).toNat with _ | _ | _ | n <;> rfl
    rw [this] at h1; simp at h1; omega
  prepMult _ _ _ _ _ h := by cases h

end Perennial.gryff.pureA
