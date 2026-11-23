/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Defs.lean`, run `rabia-r1wake-1`.)

`rabia/internal/tcp`'s internal definitions (prover T): the bodies of the representation
predicates `Spec.lean` leaves to the prover are stated over these.

* **Wait groups** (`wgCtr`, `wgTok`): each endpoint's `Wg` only counts its routines (nobody
  waits on it in the verified run): an invariant holds the counter with one token per routine
  added and not done (`wgTok`, the right to call `Done` once), and the adder's remaining budget
  (`wgCtr wg b`: `b` more may be added; the counter stays below `2^31`).
* **The proxy's client table** (`tableInv`): `Conns`, `SendChan`, `Readers`, `Writers` under
  `ConnsLock`: a connected client's entry is its accepted connection (`connIface`, persistent) and
  its reply channel (`repP`).
* **The proxy's request receipts** (`rcptInv`): per client `c`, its receipts are unclaimed, or
  claimed by the receive routine of its established connection `cid` (which holds them; the
  invariant keeps that routine's fresh token `connFresh cid true`, so no other routine claims).
-/
module

public import Dsverify.Proof.rabia.Core.Chans
public import Dsverify.GeneratedProof.rabia.internal.tcp
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.rabia.Core.PkgState
public import Perennial.Proof.sync
public import Perennial.Proof.TokSet
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia sync

/-- The wait groups' namespaces: the `WaitGroup`'s own and its counting invariant's. -/
abbrev wgN : Namespace := rabiaR.@"tcp_wg"

/-- The bound on a wait group's routines (`2 * nC` for a proxy, `2 * n` for a network endpoint,
`2` for a client). -/
def wgMax : Nat := 64

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-! ## Wait groups -/

/-- The counting invariant of a wait group: its counter is the number `n` of `Done` tokens out,
no waiters, and the adder's budget `b`, with `n + b ≤ wgMax`. -/
def wgBody (γw : WaitGroupNames) (γt γb : GName) : IProp GF :=
  iprop(∃ (ctr : w32) (n b : Nat), ownWaitGroup γw ctr ∗ ownWaitGroupWaiters γw 0 ∗
    ownTokAuth γt n ∗ ghostVar γb (1 : Qp).half b ∗ ⌜sint.Z ctr = n ∧ n + b ≤ wgMax⌝)

/-- The wait group `wg` with its counting invariant (persistent). -/
def isWg (wg : Loc) (γw : WaitGroupNames) (γt γb : GName) : IProp GF :=
  iprop(isWaitGroup wg γw (wgN.@"wg") ∗ inv (wgN.@"inv") (wgBody γw γt γb))

/-- The adder of `wg` may add `b` more routines. -/
def wgCtr (wg : Loc) (b : Nat) : IProp GF :=
  iprop(∃ γw γt γb, isWg wg γw γt γb ∗ ghostVar γb (1 : Qp).half b)

/-- One routine's right to call `wg.Done()`. -/
def wgTok (wg : Loc) : IProp GF :=
  iprop(∃ γw γt γb, isWg wg γw γt γb ∗ ownToks γt 1)

instance isWg_persistent (wg : Loc) (γw : WaitGroupNames) (γt γb : GName) :
    Persistent (isWg (GF := GF) wg γw γt γb) := by unfold isWg; infer_instance

/-! ## Channels nobody sends on -/

/-- A `Done` channel of an endpoint: a bag nothing is sent on (and never closed: `Close` is not
called in the verified run). -/
def doneChan (done : GoChan) : IProp GF :=
  iprop(∃ γd : ChanNames, isChanBag (V := Unit) γd done doneP)

instance doneChan_persistent (done : GoChan) : Persistent (doneChan (GF := GF) done) := by
  unfold doneChan; infer_instance

/-! ## The proxy's client table -/

/-- Client `c`'s entry: none, or its accepted connection (the `*net.Conn` cell `cl` holds the
acceptor's end of a connection) and its reply channel `ch` (`repP`). -/
def tableEntry (γ : Names) (c : Nat) (cl : Loc) (ch : GoChan) : IProp GF :=
  iprop(⌜cl = null⌝ ∨ ((∃ (cv : GoInterface) (cid : Nat) (a : GoString), cl ↦□ cv ∗ net.isConn cv cid true a) ∗
    ∃ γch : ChanNames, isChanBag γch ch (repP γ c)))

instance tableEntry_persistent (γ : Names) (c : Nat) (cl : Loc) (ch : GoChan) :
    Persistent (tableEntry (GF := GF) γ c cl ch) := by unfold tableEntry; infer_instance

/-- The client table under `ConnsLock`. -/
def tableInv (γ : Names) (scs cns rds wrs : GoSlice) : IProp GF :=
  iprop(∃ (chs : List GoChan) (cs rs ws : List Loc), scs ↦* chs ∗ cns ↦* cs ∗ rds ↦* rs ∗
    wrs ↦* ws ∗ ⌜chs.length = nC ∧ cs.length = nC ∧ rs.length = nC ∧ ws.length = nC⌝ ∗
    [∗list] c ↦ cl ∈ cs, ∃ ch, ⌜chs[c]? = some ch⌝ ∗ tableEntry γ c cl ch)

/-! ## The proxy's request receipts -/

/-- Client `c`'s receipts at proxy `k`: unclaimed, or claimed by the receive routine of its
established connection `cid` (the invariant keeps that routine's fresh token). -/
def rcptBody (γ : Names) (k : Nat) (γl : SrvNames) (c : Nat) : IProp GF :=
  iprop(([∗list] n ∈ List.range opBudget, pRcpt γl c n) ∨
    ∃ cid : Nat, estab γ c k cid ∗ connFresh cid true)

def rcptN (k : Nat) (c : Nat) : Namespace := ndot (ndot (ndot rabiaR "tcp_rcpt") (toString k)) (toString c)

/-- The receipts' invariants of proxy `k` (persistent). -/
def rcptInvs (γ : Names) (k : Nat) (γl : SrvNames) : IProp GF :=
  iprop([∗list] c ∈ List.range nC, inv (rcptN k c) (rcptBody γ k γl c))

instance rcptInvs_persistent (γ : Names) (k : Nat) (γl : SrvNames) :
    Persistent (rcptInvs (GF := GF) γ k γl) := by unfold rcptInvs; infer_instance

end defs

end Perennial.rabia.internal.tcp
