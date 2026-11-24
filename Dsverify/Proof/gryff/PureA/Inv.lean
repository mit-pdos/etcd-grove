/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/Inv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: **preservation of the agreement invariant** (`inv_step`), by the step's kind, and
the invariant along runs (`inv_run`, `inv_reach`, used by `agree_run`). The common part
(transport, `inv_quiet`, `StepInv`) is in `StepBase.lean`; the step cases are in `Step<Event>.lean`
(those still open are stubs here, see `notes/unit-A1.md` §3).
-/
module

public import Dsverify.Proof.gryff.PureA.StepBase
public import Dsverify.Proof.gryff.PureA.StepExec
public import Dsverify.Proof.gryff.PureA.StepExecuted
public import Dsverify.Proof.gryff.PureA.StepExecuteOverwrite
public import Dsverify.Proof.gryff.PureA.StepRecover
public import Dsverify.Proof.gryff.PureA.StepRmw
public import Dsverify.Proof.gryff.PureA.StepPrepare
public import Dsverify.Proof.gryff.PureA.StepPrepareReply
public import Dsverify.Proof.gryff.PureA.StepAccept
public import Dsverify.Proof.gryff.PureA.StepCommit
public import Dsverify.Proof.gryff.PureA.StepAcceptReply
public import Dsverify.Proof.gryff.PureA.StepPreAccept
public import Dsverify.Proof.gryff.PureA.StepPreAcceptReply

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

theorem inv_prepare {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.prepare m)) s' o c1)
    (hm : Msg.prepare m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.prepare m)) = .ok (s', o)) :
    StepInv c c1 G :=
  A1b.prepare_inv I hp.1 hp.2 hm h -- `PureA/StepPrepare.lean`

theorem inv_preAccept {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.preAccept m)) s' o c1)
    (hm : Msg.preAccept m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.preAccept m)) = .ok (s', o)) :
    StepInv c c1 G :=
  SPA.inv_preAccept_core I hp.1 hp.2 hm h

theorem inv_accept {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : EAcceptM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.accept m)) s' o c1)
    (hm : Msg.accept m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.accept m)) = .ok (s', o)) :
    StepInv c c1 G :=
  A1d.inv_accept_core I hp.1 hp.2 hm h

theorem inv_commit {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : ECommitM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.commit m)) s' o c1)
    (hm : Msg.commit m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.commit m)) = .ok (s', o)) :
    StepInv c c1 G :=
  A1d.inv_commit_core I hp.1 hp.2 hm h

theorem inv_prepareReply {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PrepareReplyM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.prepareReply m)) s' o c1)
    (hm : Msg.prepareReply m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.prepareReply m)) = .ok (s', o)) :
    StepInv c c1 G :=
  A1b.prepareReply_inv I hp.1 hp.2 hm h -- `PureA/StepPrepareReply.lean`

theorem inv_preAcceptReply {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptReplyM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.preAcceptReply m)) s' o c1)
    (hm : Msg.preAcceptReply m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.preAcceptReply m)) = .ok (s', o)) :
    StepInv c c1 G :=
  SPA.inv_preAcceptReply_core I hp.1 hp.2 hm h

theorem inv_preAcceptOK {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : PreAcceptOKM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.preAcceptOK m)) s' o c1)
    (hm : Msg.preAcceptOK m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.preAcceptOK m)) = .ok (s', o)) :
    StepInv c c1 G :=
  SPA.inv_preAcceptOK_core I hp.1 hp.2 hm h

theorem inv_acceptReply {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {m : AcceptReplyM} {s' : RState}
    {o : List Out} (I : CInv c G) (hp : Post c a (.msg (.acceptReply m)) s' o c1)
    (hm : Msg.acceptReply m ∈ c.inflight a) (h : stepR a (c.st a) (.msg (.acceptReply m)) = .ok (s', o)) :
    StepInv c c1 G :=
  A1d.inv_acceptReply_core I hp.1 hp.2 hm h

/-- **Preservation by one step** (with the history extended): the Gryff handlers and `forceWrite`
by `inv_quiet`; the EPaxos steps by `inv_<event>` (`Step<Event>.lean`; some open). -/
theorem inv_step {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {x : List Ext}
    (I : CInv c G) (h : GStep c a e c1 x) :
    ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i) := by
  obtain ⟨s', o, hs, hrecv, -, hst, hinf⟩ := h
  have hp : Post c a e s' o c1 := ⟨hst, hinf⟩
  have hok := gstep_ok hs
  have hm : ∀ m, e = .msg m → m ∈ c.inflight a := fun m he => hrecv m (by subst he; rfl)
  cases e with
  | read => exact inv_quiet' I hp (stepClientRead_frame hok) (stepClientRead_quiet hok)
  | write => exact inv_quiet' I hp (stepClientWrite_frame hok) (stepClientWrite_quiet hok)
  | rmw => exact inv_rmw I hp hok
  | forceWrite => cases hok; exact inv_quiet' I hp ⟨rfl, rfl, rfl⟩ quietO_nil
  | recover => exact inv_recover I hp hok
  | exec => exact inv_exec I hp hok
  | msg m =>
    have hm := hm m rfl
    cases m with
    | read1 => exact inv_quiet' I hp (stepRead1_frame hok) (stepRead1_quiet hok)
    | read2 => exact inv_quiet' I hp (stepRead2_frame hok) (stepRead2_quiet hok)
    | write1 => exact inv_quiet' I hp (stepWrite1_frame hok) (stepWrite1_quiet hok)
    | write2 => exact inv_quiet' I hp (stepWrite2_frame hok) (stepWrite2_quiet hok)
    | read1Reply => exact inv_quiet' I hp (stepRead1Reply_frame hok) (stepRead1Reply_quiet hok)
    | read2Reply => exact inv_quiet' I hp (stepRead2Reply_frame hok) (stepRead2Reply_quiet hok)
    | write1Reply => exact inv_quiet' I hp (stepWrite1Reply_frame hok) (stepWrite1Reply_quiet hok)
    | write2Reply => exact inv_quiet' I hp (stepWrite2Reply_frame hok) (stepWrite2Reply_quiet hok)
    | prepare => exact inv_prepare I hp hm hok
    | preAccept => exact inv_preAccept I hp hm hok
    | accept => exact inv_accept I hp hm hok
    | commit => exact inv_commit I hp hm hok
    | prepareReply => exact inv_prepareReply I hp hm hok
    | preAcceptReply => exact inv_preAcceptReply I hp hm hok
    | preAcceptOK => exact inv_preAcceptOK I hp hm hok
    | acceptReply => exact inv_acceptReply I hp hm hok
    | executed => exact inv_executed I hp hm hok
    | executeOverwrite => exact inv_executeOverwrite I hp hm hok

/-- The invariant along a run. -/
theorem inv_run {c c' : Cfg gNet} {G : GG} {l : List Label} (I : CInv c G) (h : GRun c l c') :
    ∃ G', CInv c' G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c' q i) := by
  induction h generalizing G with
  | nil c => exact ⟨G, I, fun q i => Evolve.refl (I.inst q i).ainv⟩
  | cons hs _ ih =>
    obtain ⟨G1, I1, E1⟩ := inv_step I hs
    obtain ⟨G2, I2, E2⟩ := ih I1
    exact ⟨G2, I2, fun q i => (E1 q i).trans (E2 q i)⟩

/-- A reachable configuration has a history satisfying the invariant. -/
theorem inv_reach {c : Cfg gNet} {l : List Label} (h : GRun (Cfg.init gNet) l c) :
    ∃ G, CInv c G := by
  obtain ⟨G, I, _⟩ := inv_run inv_init h
  exact ⟨G, I⟩

end Perennial.gryff.pureA
