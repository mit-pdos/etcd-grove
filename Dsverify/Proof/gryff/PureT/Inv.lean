/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Inv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the invariant of reachable configurations.

* `SI P r s`: replica `r`'s state `s` (its id, the budget, the instance space's bounds and copies'
  shapes, the leader's own copies, the conflict table, `CommittedUpTo`, the coordinator's records),
  where `P q` bounds the instance numbers of row `q` (in a configuration, `Pf st q`: the number of
  instances replica `q` created, `crtInstance[q]` at `q`).
* `MInv P st r m`: a message `m` in flight to `r` (its fields' shape; for a reply or a request, the
  proposer's copy, which exists and keeps its bookkeeping until committed; for the coordinator's
  messages, its records).
* `Mono r s s'`: what a step of replica `r` keeps (the facts messages rely on).
-/
module

public import Dsverify.Proof.gryff.PureT.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-- The number of instances replica `q` created (`crtInstance[q]` at `q`). -/
def Pf (st : Fin 3 → RState) (q : Fin 3) : Nat := ((st q).crt (rid32 q)).toNat

/-- `(q, i)` is an instance some replica created: `q` a row, `i` below its count. -/
def InstB (P : Fin 3 → Nat) (q i : w32) : Prop := ∃ q' : Fin 3, q = rid32 q' ∧ i.toNat < P q'

/-- A status the code uses. -/
def stOk (x : w8) : Prop :=
  x = St.NONE ∨ x = St.PREACCEPTED ∨ x = St.PREACCEPTED_EQ ∨ x = St.ACCEPTED ∨
    x = St.COMMITTED ∨ x = St.EXECUTED

/-- A recovery candidate's shape. -/
def RIok (ir : RecoveryInstance) : Prop :=
  (ir.status = St.PREACCEPTED ∨ ir.status = St.PREACCEPTED_EQ ∨ ir.status = St.ACCEPTED) ∧
  cmdsOk ir.cmds = true ∧ (ir.status ≠ St.ACCEPTED → ir.cmds ≠ []) ∧
  (ir.preAcceptCount ≠ 0 → ir.status = St.PREACCEPTED_EQ)

/-- Bookkeeping's shape. -/
def LBok (lb : LB) : Prop :=
  (∀ p ∈ lb.clientProposals, p.cmd.ok = true) ∧ ∀ ir, lb.recoveryInst = some ir → RIok ir

/-- A copy of instance `(q, i)`. -/
def CopyOK (q i : w32) (c : Copy) : Prop :=
  cmdsOk c.cmds = true ∧ ((c.status = St.PREACCEPTED ∨ c.status = St.PREACCEPTED_EQ) → c.cmds ≠ []) ∧
  c.leader = q ∧ c.slot = i ∧ stOk c.status ∧ ∀ lb, c.lb = some lb → LBok lb

/-- The leader's own copy of its instance. -/
def OwnOK (c : Copy) : Prop :=
  c.status ≠ St.NONE ∧ (c.lb = none → committedSt c.status) ∧
  ∀ lb, c.lb = some lb → lb.clientProposals ≠ []

/-- A read record (every read completes at its first `Read1Reply`). -/
def FreshR (rop : ReadOp) : Prop :=
  rop.maxValTag = none ∧ rop.numRead1Replies = 1 ∧ rop.readsWithMaxTag = 0 ∧
    rop.determinedReadVal = false

/-- The coordinator's records (`maxN`, `OngoingReqs`, `wops`, `rops`; the keys used): reads' and
writes' entries are distinct, every write has its entry, every read record is fresh. -/
structure CoordOK (mx : w32) (oq : AMap 32 OngoingOp) (ws : AMap 64 WriteOp) (rs : AMap 64 ReadOp)
    (used : List (w32 × w32)) : Prop where
  oreq : ∀ k o, oq.get? k = some o → k.toNat ≤ mx.toNat ∧
    ∀ k' ∈ o.shortReads, k'.toNat ≤ mx.toNat ∧ ∀ o', oq.get? k' = some o' → o'.isRead = true
  wops : ∀ e ∈ ws, e.2.n.toNat ≤ mx.toNat ∧ (∃ o, oq.get? e.2.n = some o ∧ o.isRead = false) ∧
    e.2.maxValTag.v = -1 ∧ e.2.numWrite1Applies = 0 ∧ e.1 = shiftInts e.2.requestId e.2.clientId ∧
    (e.2.clientId, e.2.requestId) ∈ used
  wopsN : ∀ e1 ∈ ws, ∀ e2 ∈ ws, e1.2.n = e2.2.n → e1.1 = e2.1
  rops : ∀ id rop, rs.get? id = some rop → FreshR rop ∧ rop.n.toNat ≤ mx.toNat ∧
    ∀ o, oq.get? rop.n = some o → o.isRead = true

/-- Replica `r`'s state. -/
structure SI (P : Fin 3 → Nat) (r : Fin 3) (s : RState) : Prop where
  id : s.id = rid32 r
  lcrt : s.crtInstance.length = 3
  lcut : s.committedUpTo.length = 5
  lconf : s.conf.length = 3
  nreq : s.nReqs ≤ 24
  budget : s.maxN.toNat + (s.crt (rid32 r)).toNat ≤ s.nReqs
  crt : ∀ q : Fin 3, (s.crt (rid32 q)).toNat ≤ P q
  inst : ∀ q i c, s.inst q i = some c → InstB P q i ∧ CopyOK q i c
  own : ∀ i : w32, i.toNat < (s.crt (rid32 r)).toNat → (s.inst (rid32 r) i).isSome
  ownOK : ∀ i c, s.inst (rid32 r) i = some c → OwnOK c
  cut : ∀ q : Fin 3, s.cut (rid32 q) = -1 ∨ (s.cut (rid32 q)).toNat < 24
  conf : ∀ q : Fin 3, ∀ hi, s.confAt q.val = some hi → (s.inst (rid32 q) hi).isSome
  propQ : ∀ p ∈ s.proposeQ, p.cmd.ok = true
  usedPos : ∀ p ∈ s.used, 0 ≤ p.1.toInt
  coord : CoordOK s.maxN s.ongoingReqs s.wops s.rops s.used

/-- Replica `L`'s copy of `(q, i)` exists and keeps its bookkeeping until committed (`L` sent a
request for it, or gets a reply to one). -/
def PropC (st : Fin 3 → RState) (L : Fin 3) (q i : w32) : Prop :=
  ∃ c, (st L).inst q i = some c ∧ (c.lb ≠ none ∨ committedSt c.status)

/-- Replica `x` executed `(q, i)` with a command. -/
def ExecC (st : Fin 3 → RState) (x : Fin 3) (q i : w32) : Prop :=
  ∃ c, (st x).inst q i = some c ∧ c.status = St.EXECUTED ∧ c.cmds ≠ []

/-- The coordinator `q`'s write with key `(cid, rid)`: the key is used, and its record (if any)
has its tag. -/
def WK (st : Fin 3 → RState) (q : Fin 3) (rid cid : w32) : Prop :=
  0 ≤ cid.toInt ∧ (cid, rid) ∈ (st q).used ∧
    ∀ w, (st q).wops.get? (shiftInts rid cid) = some w → w.writeTag ≠ none

/-- A request of `L ≠ r` for `(q, i)`. -/
def FromL (st : Fin 3 → RState) (r : Fin 3) (leaderId q i : w32) : Prop :=
  ∃ L, L ≠ r ∧ leaderId = rid32 L ∧ PropC st L q i

/-- A message in flight to `r`. -/
def MInv (P : Fin 3 → Nat) (st : Fin 3 → RState) (r : Fin 3) : Msg → Prop
  | .read1 m => m.k = 0 ∧ m.d = dep0 ∧ ∃ q : Fin 3, m.replicaId = rid32 q
  | .read2 _ => False
  | .read1Reply _ => True
  | .read2Reply _ => False
  | .write1 m => m.k = 0 ∧ slt m.d.key 0 = true ∧ m.forceWrite = 1 ∧ ∃ q : Fin 3, m.replicaId = rid32 q
  | .write2 m => m.k = 0 ∧ ∃ q : Fin 3, m.replicaId = rid32 q ∧ WK st q m.requestId m.clientId
  | .write1Reply m => m.vt.v = -1
  | .write2Reply m => WK st r m.requestId m.clientId
  | .preAccept m => FromL st r m.leaderId m.replica m.inst ∧ InstB P m.replica m.inst ∧
      cmdsOk m.cmds = true ∧ m.cmds ≠ []
  | .preAcceptReply m => InstB P m.replica m.inst ∧ PropC st r m.replica m.inst
  | .preAcceptOK m => InstB P (rid32 r) m.inst ∧ PropC st r (rid32 r) m.inst
  | .accept m => FromL st r m.leaderId m.replica m.inst ∧ InstB P m.replica m.inst ∧
      cmdsOk m.cmds = true
  | .acceptReply m => InstB P m.replica m.inst ∧ PropC st r m.replica m.inst
  | .commit m => InstB P m.replica m.inst ∧ cmdsOk m.cmds = true
  | .prepare m => FromL st r m.leaderId m.replica m.inst ∧ InstB P m.replica m.inst
  | .prepareReply m => InstB P m.replica m.inst ∧ PropC st r m.replica m.inst ∧
      cmdsOk m.cmds = true ∧ ((m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) → m.cmds ≠ [])
  | .executed m => m.replica = rid32 r ∧ InstB P m.replica m.inst ∧ ∃ x, ExecC st x m.replica m.inst
  | .executeOverwrite m => InstB P m.leader m.slot ∧ ExecC st r m.leader m.slot

/-- The invariant of a configuration. -/
def InvC (c : Cfg gNet) : Prop :=
  (∀ r, SI (Pf c.st) r (c.st r)) ∧ ∀ r m, m ∈ c.inflight r → MInv (Pf c.st) c.st r m

/-- What a step of replica `r` from `s` to `s'` keeps. -/
structure Mono (r : Fin 3) (s s' : RState) : Prop where
  id : s'.id = s.id
  used : ∀ p ∈ s.used, p ∈ s'.used
  crt : (s.crt (rid32 r)).toNat ≤ (s'.crt (rid32 r)).toNat
  inst : ∀ q i c, s.inst q i = some c → ∃ c', s'.inst q i = some c' ∧
    ((c.lb ≠ none ∨ committedSt c.status) → (c'.lb ≠ none ∨ committedSt c'.status)) ∧
    (c.status = St.EXECUTED → c'.status = St.EXECUTED ∧ c'.cmds = c.cmds)
  wt : ∀ rid cid, (cid, rid) ∈ s.used →
    (∀ w, s.wops.get? (shiftInts rid cid) = some w → w.writeTag ≠ none) →
    (∀ w, s'.wops.get? (shiftInts rid cid) = some w → w.writeTag ≠ none)

/-- The configuration's states after replica `r` steps to `s'`. -/
def upd (st : Fin 3 → RState) (r : Fin 3) (s' : RState) : Fin 3 → RState :=
  fun j => if j = r then s' else st j

/-- An output's obligation. -/
def OutOk (P : Fin 3 → Nat) (st : Fin 3 → RState) : Out → Prop
  | .send d m => MInv P st d m
  | .ext _ => True

/-- The postcondition of a step of replica `r` (states `st`) with result `(s', o)`. -/
def Post (st : Fin 3 → RState) (r : Fin 3) (res : RState × List Out) : Prop :=
  Mono r (st r) res.1 ∧ SI (Pf (upd st r res.1)) r res.1 ∧
    ∀ x ∈ res.2, OutOk (Pf (upd st r res.1)) (upd st r res.1) x

end Perennial.gryff.pure.tot
