/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica2/Results.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Stage 2: the link module (C)

The frozen theorems of `Replica2/State.lean` and `Replica2/Specs.lean` whose proofs live in unit
files that import those modules, moved here (statement text unchanged) and proved by the unit
proofs: H1's participant, coordinator and handler `*.wp_proof`, H2's `epaxosOwn_inst_open'`, H2a's
`handlePreAccept_wp_link`, H2b's `HandleRMW_wp'`, H2c's and H2c2's `handle*_spec` (H2c2 also
`executeOverwrite_spec`), H3's `*_wp_frozen`, N1's
`ConnectToPeers_wp`, B's `lock_boot_proof`; and their consumers in `Specs.lean`, `Loop.wp` and
`run.wp` (unit B's `Loop_proof`, `run_proof` over the handlers' specs). `Server/Boot.lean` imports
this module.
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.H1.Parti
public import Dsverify.Proof.gryff.H1.CoordStart
public import Dsverify.Proof.gryff.H1.CoordWrite
public import Dsverify.Proof.gryff.H1.CoordRead1
public import Dsverify.Proof.gryff.H1.CoordRead
public import Dsverify.Proof.gryff.H1.CoordForce
public import Dsverify.Proof.gryff.H1.CoordSC
public import Dsverify.Proof.gryff.H1.CoordW1
public import Dsverify.Proof.gryff.H1.CoordW2
public import Dsverify.Proof.gryff.H1.GCoord
public import Dsverify.Proof.gryff.H1.CoordSpecs
public import Dsverify.Proof.gryff.H1.PartiSpecs
public import Dsverify.Proof.gryff.H1.Iparti
public import Dsverify.Proof.gryff.H1.GParti
public import Dsverify.Proof.gryff.H2.InstOpen
public import Dsverify.Proof.gryff.H2a.Results
public import Dsverify.Proof.gryff.H2b.Propose
public import Dsverify.Proof.gryff.H2c.Accept
public import Dsverify.Proof.gryff.H2c.Commit
public import Dsverify.Proof.gryff.H2c.AcceptReply
public import Dsverify.Proof.gryff.H3.Prepare
public import Dsverify.Proof.gryff.H3.PrepareReply
public import Dsverify.Proof.gryff.H3.Recover
public import Dsverify.Proof.gryff.N.Connect
public import Dsverify.Proof.gryff.Replica2.SpecsN
public import Dsverify.Proof.gryff.Lib.MathHyps
public import Dsverify.Proof.gryff.B.LockBoot
public import Dsverify.Proof.gryff.X.Final
public import Dsverify.Proof.gryff.H2c2.PreAcceptOK
public import Dsverify.Proof.gryff.H2c2.Executed
public import Dsverify.Proof.gryff.H2c2.ExecOverwrite
public import Dsverify.Proof.gryff.H2c2.PreAcceptReply
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS TInv Post)
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## From `Replica2/State.lean` (its `laws` section) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]


/-- **An instance-space slot, open** (H3-R1; H2's and H3's handlers creating, updating or
replacing an instance): slot `(q, i)` (in the box) of row `q`'s slice `sq` holds `p` (`nil`: no
instance in `s`; else the copy's struct, `copyRep`); an uncommitted (or absent) instance has the
executor's search state trivial there (`Index = Lowlink = 0`, not executed: H2-R5). Three
closings (one is used): (a) the same pointer with a new copy (a committed copy stays committed
or executed; a copy becoming committed persists its `ρ.ptrs` element: `|==>`); (b) a fresh
pointer in a nil slot; (c) a fresh pointer replacing an uncommitted copy's (the old struct's
`copyRep`, returned by the opening, is the caller's). -/
theorem epaxosOwn_inst_open (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q i : w32)
    (hb : model.inBox q i = true) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (p : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some p⌝ ∗ sq ↦* ptrs ∗
      (match s.inst q i with
       | none => iprop(⌜p = Loc.null⌝)
       | some c => iprop(⌜p ≠ Loc.null⌝ ∗ copyRep ρ xs (sint.Z q, sint.Z i) p c)) ∗
      ⌜committedOrExecuted s (sint.Z q, sint.Z i) = false →
        xs.numF (sint.Z q, sint.Z i) = 0 ∧ xs.lowF (sint.Z q, sint.Z i) = 0 ∧
        (sint.Z q, sint.Z i) ∉ xs.1⌝ ∗
      -- (a) the same pointer, a new copy
      ((∀ c' : Copy, ⌜(s.inst q i).isSome ∧ (committedOrExecuted s (sint.Z q, sint.Z i) = true →
            committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) = true)⌝ -∗
          sq ↦* ptrs -∗ copyRep ρ xs (sint.Z q, sint.Z i) p c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c')) ∧
       -- (b) a fresh pointer in a nil slot
       (∀ (p' : Loc) (c' : Copy), ⌜s.inst q i = none ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c')) ∧
       -- (c) a fresh pointer replacing an uncommitted copy's
       (∀ (p' : Loc) (c' : Copy), ⌜(s.inst q i).isSome ∧
            committedOrExecuted s (sint.Z q, sint.Z i) = false ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c'))) := by
  exact epaxosOwn_inst_open' ρ h r xs s q i hb -- unit H2 (H3-R1)

/-- **The run loop's first `Lock`** (boot): with the run goroutine's boot resources, the lock's
boot state becomes `lockedAt` at the empty trace (`ConnectToPeers` done: the peer writers set). -/
theorem lock_boot (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (p : ProphId) :
    r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaLockInv γ ρ k r p ∗ loopTok γ ρ k r ⊢
      |==> ((∃ (t : List Ev) (xs : XS), lockedAt γ ρ k r p t xs) ∗ loopTok γ ρ k r) := by
  exact unitB.lock_boot_proof γ ρ k r p -- unit B (B-R5)

end laws

/-! ## From `Replica2/Specs.lean` (its `specs` section) -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5
variable [io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [netN.NetSpecs GF]
variable [strA : netN.StringsIndexHyp GF] [mathA : lib.MathPowHyp GF]

/-! ## The H1 callee classes, closed (`H1/PartiSpecs.lean`, `H1/CoordSpecs.lean`)

The participant's and coordinator's methods' specs, which the modules above H1 see through the
classes `GryffPartiDeps`, `GryffSCDeps`, `GryffCoordDeps` (CLAUDE.md, "Import tiers"), proved by
`H1/Parti.lean`'s and `H1/Coord*.lean`'s proofs. Local instances of this module only. -/

theorem gryffPartiDeps_holds : GryffPartiDeps (GF := GF) where
  getStoreMetadata := GryffParticipant.GetStoreMetadata.wp_proof
  handleOverwrite := GryffParticipant.HandleOverwrite.wp_proof
  handleWrite2 := GryffParticipant.HandleWrite2.wp_proof
  handleRead2 := GryffParticipant.HandleRead2.wp_proof
  handleRead1 := GryffParticipant.HandleRead1.wp_proof
  handleWrite1 := GryffParticipant.HandleWrite1.wp_proof

theorem gryffSCDeps_holds : GryffSCDeps (GF := GF) where
  shortCircuit := GryffCoordinator.ShortCircuit.wp_int

attribute [local instance] gryffSCDeps_holds in
theorem gryffCoordDeps_holds : GryffCoordDeps (GF := GF) where
  startRead := GryffCoordinator.StartRead.wp_proof
  startWrite := GryffCoordinator.StartWrite.wp_proof
  handleRead1Reply := GryffCoordinator.HandleRead1Reply.wp_proof
  handleRead2Reply := GryffCoordinator.HandleRead2Reply.wp_proof
  handleWrite1Reply := GryffCoordinator.HandleWrite1Reply.wp_proof
  handleWrite2Reply := GryffCoordinator.HandleWrite2Reply.wp_proof
  handleForceWrite := GryffCoordinator.HandleForceWrite.wp_proof

attribute [local instance] gryffPartiDeps_holds gryffSCDeps_holds gryffCoordDeps_holds

/-- `GetStoreMetadata(0)` (`SendRead1`, `handlePreAccept`): the store's tag cell, borrowed. -/
theorem GryffParticipant.GetStoreMetadata.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (tag : model.Tag) (ong : AMap 32 w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k tag ong }}
      (App (partiM pa go!"GetStoreMetadata") (Val #(W64 0)))
    {{ (md : Loc), RET #md; ∃ (tp : Loc) (gt : src.gryffproto.Tag), ⌜tagOf gt = tag⌝ ∗ tp ↦□ gt ∗
        md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp ∗
        (md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp -∗ partiOwn pa ip k tag ong) }} := by
  exact GryffParticipant.GetStoreMetadata.wp_proof pa ip k tag ong -- unit H1

/-- `HandleOverwrite(0, v, tp)` (the participant's own handlers; `*gryff.Replica.HandleOverwrite`,
the coordinator's callback; `executeOverwrite`): the store moves to `ovw`; the tag cell `tp`,
persistent, may become the store's. -/
theorem GryffParticipant.HandleOverwrite.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (vt : model.ValTag) (ong : AMap 32 w32) (v : w64) (tp : Loc)
    (gt : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k vt.t ong ∗
        ipartiOk ip V ∗ V vt.v ∗ tp ↦□ gt }}
      (App (App (App (partiM pa go!"HandleOverwrite") (Val #(W64 0))) (Val #v)) (Val #tp))
    {{ RET #(); partiOwn pa ip k (ovw vt v (tagOf gt)).t ong ∗ V (ovw vt v (tagOf gt)).v }} := by
  exact GryffParticipant.HandleOverwrite.wp_proof pa ip k V vt ong v tp gt -- unit H1

/-- `HandleRead1(K, &D, RequestId, ClientId, true, &Vt, ReplicaId)` (`handleRead1Proxied`): the
participant's part of the step on `Read1Proxied` `m` (the reply it returns is the step's one
output). The message's `D` and `Vt` fields are persistent (the store may point into them). -/
theorem GryffParticipant.HandleRead1.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Read1ProxiedM) (dp vp : Loc)
    (gd : src.gryffproto.Dep) (gv : src.gryffproto.ValTag) (hd : depOf gd = m.d)
    (hv : vtOf gv = m.vt) (hid : s.id = rid32 k) (hstep : model.stepRead1 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ vp ↦□ gv }}
      (App (App (App (App (App (App (App (partiM pa go!"HandleRead1") (Val #m.k)) (Val #dp))
        (Val #m.requestId)) (Val #m.clientId)) (Val #true)) (Val #vp)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read1Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read1Reply (read1ReplyOf g)) = some o1⌝ }} := by
  exact GryffParticipant.HandleRead1.wp_proof pa ip k V s s' o1 m dp vp gd gv hd hv hid hstep -- unit H1

/-- `HandleRead2(K, Vt, RequestId, ClientId, UpdateId)` (`handleRead2Proxied`). -/
theorem GryffParticipant.HandleRead2.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Read2ProxiedM)
    (gv : src.gryffproto.ValTag) (uid : w64) (hv : vtOf gv = m.vt)
    (hstep : model.stepRead2 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (App (partiM pa go!"HandleRead2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId)) (Val #uid))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read2Reply (read2ReplyOf g)) = some o1⌝ }} := by
  exact GryffParticipant.HandleRead2.wp_proof pa ip k V s s' o1 m gv uid hv hstep -- unit H1

/-- `HandleWrite1(K, V, N, &D, RequestId, ClientId, &MaxAppliedTag, ForceWrite, ReplicaId)`
(`handleWrite1Proxied`): nil for a stale request (no output), else the reply. -/
theorem GryffParticipant.HandleWrite1.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (outs : List Out) (m : model.Write1ProxiedM)
    (val : w64) (n : w32) (dp mp : Loc) (gd : src.gryffproto.Dep) (gmt : src.gryffproto.Tag)
    (hd : depOf gd = m.d) (hid : s.id = rid32 k) (hstep : model.stepWrite1 s m = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ mp ↦□ gmt }}
      (App (App (App (App (App (App (App (App (App (partiM pa go!"HandleWrite1") (Val #m.k))
        (Val #val)) (Val #n)) (Val #dp)) (Val #m.requestId)) (Val #m.clientId)) (Val #mp))
        (Val #m.forceWrite)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ((⌜rp = Loc.null ∧ outs = []⌝) ∨ ∃ (g : src.gryffproto.Write1Reply) (o1 : Out),
          rp ↦ g ∗ ⌜outs = [o1] ∧ model.sendTo m.replicaId (.write1Reply (write1ReplyOf g)) = some o1⌝) }} := by
  exact GryffParticipant.HandleWrite1.wp_proof pa ip k V s s' outs m val n dp mp gd gmt hd hid hstep -- unit H1

/-- `HandleWrite2(K, Vt, RequestId, ClientId)` (`handleWrite2Proxied`): the `OngoingWrites` loop
(Go's random map order) answers nothing (every entry already answered: `partiOwn`). -/
theorem GryffParticipant.HandleWrite2.wp (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Write2ProxiedM)
    (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt) (hid : s.id = rid32 k)
    (hstep : model.stepWrite2 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (partiM pa go!"HandleWrite2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Write2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.write2Reply (write2ReplyOf g)) = some o1⌝ }} := by
  exact GryffParticipant.HandleWrite2.wp_proof pa ip k V s s' o1 m gv hv hid hstep -- unit H1

/-- `StartRead(RequestId, ClientId, 0, &D)` (`handleRead`): the step on a client read. `D` points
into the request (persistent); the client id's writer is known (the request's channel element). -/
theorem GryffCoordinator.StartRead.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (rid cid : w32) (dp w : Loc) (gd : src.gryffproto.Dep)
    (hid : s.id = rid32 k) -- H1-R9
    (hstep : model.stepR k s (.read rid cid 0 (depOf gd)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (coordM co go!"StartRead") (Val #rid)) (Val #cid)) (Val #(W64 0)))
        (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.StartRead.wp_proof ρ co ic k C s s' outs o rid cid dp w gd hid hstep -- unit H1

/-- `StartWrite(RequestId, ClientId, 0, V, &D)` (`handleWrite`): the step on a client write. -/
theorem GryffCoordinator.StartWrite.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (rid cid : w32) (v : w64) (dp w : Loc) (gd : src.gryffproto.Dep)
    (hid : s.id = rid32 k) -- H1-R9
    (hstep : model.stepR k s (.write rid cid 0 v (depOf gd)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ dp ↦□ gd ∗ writerIs ρ cid w }}
      (App (App (App (App (App (coordM co go!"StartWrite") (Val #rid)) (Val #cid))
        (Val #(W64 0))) (Val #v)) (Val #dp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.StartWrite.wp_proof ρ co ic k C s s' outs o rid cid v dp w gd hid hstep -- unit H1

/-- `HandleRead1Reply(ShiftInts(RequestId, ClientId), &Vt, ReplicaId)` (`handleRead1Reply`): the
step on `Read1Reply` `m`; its `Vt` field is persistent (the read op and the store may keep it). -/
theorem GryffCoordinator.HandleRead1Reply.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Read1ReplyM) (vp : Loc) (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt)
    (hid : s.id = rid32 k) -- H1-R9
    (hstep : model.stepR k s (.msg (.read1Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"HandleRead1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #vp)) (Val #m.replicaId))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.HandleRead1Reply.wp_proof ρ co ic k C s s' outs o m vp gv hv hid hstep -- unit H1

/-- `HandleRead2Reply(ShiftInts(RequestId, ClientId), T, ReplicaId)` (`handleRead2Reply`). -/
theorem GryffCoordinator.HandleRead2Reply.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Read2ReplyM) (gt : src.gryffproto.Tag) (rep : w32)
    (hstep : model.stepR k s (.msg (.read2Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (coordM co go!"HandleRead2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #gt)) (Val #rep))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.HandleRead2Reply.wp_proof ρ co ic k C s s' outs o m gt rep hstep -- unit H1

/-- `HandleForceWrite()` (`handleForceWrite`): no effect on the model state (`ForcedKeysChanged`
is always empty). -/
theorem GryffCoordinator.HandleForceWrite.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (s : RState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s }}
      (App (coordM co go!"HandleForceWrite") (Val #()))
    {{ RET #(); coordOwn ρ co ic k s }} := by
  exact GryffCoordinator.HandleForceWrite.wp_proof ρ co ic k s -- unit H1

/-- `HandleWrite1Reply(ShiftInts(RequestId, ClientId), ClientId, ReplicaId, &Vt)`
(`handleWrite1Reply`). -/
theorem GryffCoordinator.HandleWrite1Reply.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Write1ReplyM) (rep : w32) (vp : Loc) (gv : src.gryffproto.ValTag)
    (hv : vtOf gv = m.vt) (hid : s.id = rid32 k) -- H1-R9
    (hstep : model.stepR k s (.msg (.write1Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (App (coordM co go!"HandleWrite1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #m.clientId)) (Val #rep)) (Val #vp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.HandleWrite1Reply.wp_proof ρ co ic k C s s' outs o m rep vp gv hv hid hstep -- unit H1

/-- `HandleWrite2Reply(ShiftInts(RequestId, ClientId), ReplicaId, &T, ClientId, Applied)`
(`handleWrite2Reply`; `T` is only logged). -/
theorem GryffCoordinator.HandleWrite2Reply.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Write2ReplyM) (rep : w32) (tp : Loc)
    (hstep : model.stepR k s (.msg (.write2Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (App (App (coordM co go!"HandleWrite2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #rep)) (Val #tp))
        (Val #m.clientId)) (Val #m.applied))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  exact GryffCoordinator.HandleWrite2Reply.wp_proof ρ co ic k C s s' outs o m rep tp hstep -- unit H1

/-- `ShortCircuit(n, value, fastOverwrite)` (`HandleWrite1Reply`, `HandleWrite2Reply`; internal to
`gryffcommon`, stated because the model transcribes it as one function, `shortCircuit`). -/
theorem GryffCoordinator.ShortCircuit.wp (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (vt : model.ValTag) (n : w32) (vp : Loc) (gv : src.gryffproto.ValTag) (fo : Bool)
    (hsc : model.shortCircuit s n (vtOf gv) fo = some (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C vt (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"ShortCircuit") (Val #n)) (Val #vp)) (Val #fo))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C vt o }} := by
  exact GryffCoordinator.ShortCircuit.wp_proof ρ co ic k C s s' outs o vt n vp gv fo hsc -- unit H1

/-- The participant's callbacks act on the store's value `r.State.Store[0]` (moved from
`Specs.lean`; H1b-R2: `gryff`'s initialization for `Printf`, `h1Fixed` for `GetStats`). -/
theorem Replica_ipartiOk (r gR : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
      r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ □ h1Fixed r gR ⊢
      ipartiOk (replicaIface r) (valOwn gR) :=
  Replica_ipartiOk_proof r gR

/-- The coordinator's callbacks (`SendRead1` ... through `send*To`: `SendMsg` or the own channel;
`Complete*` through `GetClientWriter` and the client writer; `HandleOverwrite` through the
participant) on `coordCtx` (moved from `Specs.lean`). -/
theorem Replica_icoordOk (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ -- H1b-R2
      isReplica γ ρ k r ∗ r.[src.gryff.Replica, go!"parti"] ↦□ pa ⊢
      icoordOk ρ (replicaIface r) k (coordCtx γ ρ k r pa t ong) :=
  Replica_icoordOk_proof γ ρ k r pa t ong -- unit H1c (`H1/Icoord.lean`)

/-- **`ConnectToPeers()`** (`run`, before the run loop): dials the lower peers (handshake with
`k`'s id), accepts the higher ones (`waitForPeerConnections`, which also hands client
connections to `serveClient`), starts one `replicaListener` per peer; returns the run goroutine's
token with the connected writers (`loopTok`). -/
theorem Replica.ConnectToPeers.wp (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG))
    (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ connectRes γ ρ k r gR }} -- N1-2
      (App (genM gR go!"ConnectToPeers") (Val #()))
    {{ RET #(); loopTok γ ρ k r ∗ listenerOwn γ ρ k gR }} := by
  exact netN.ConnectToPeers_wp γ ρ k r gR (fun conn rd hs => Replica.serveClient.wp γ ρ k r gR conn rd hs)
    wp_rfl -- unit N1 (N1-2, N1-4)

/-- `HandleRMW(rmw)` (`IRMWHandler`'s method; the proposal's writer is the client id's). -/
theorem HandleRMW.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p w : Loc)
    (g : src.gryffproto.RMW) :
    stepSpec γ ρ k r (App (epM h go!"HandleRMW") (Val #p))
      iprop(handlerOf r h ∗ p ↦ g ∗ writerIs ρ g.ClientId' w) (rmwEvOf g) := by
  exact h2b.HandleRMW_wp' γ ρ k r h p w g -- unit H2b

/-- `startRecoveryForInstance(q, i)` (the recovery trigger: `instancesToRecover`). -/
theorem startRecoveryForInstance.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (q i : w32) :
    stepSpec γ ρ k r (App (App (epM h go!"startRecoveryForInstance") (Val #q)) (Val #i))
      (handlerOf r h) (.recover q i) := by
  exact h3.startRecoveryForInstance_wp_frozen γ ρ k r h q i -- unit H3

theorem handlePrepare.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PrepareM) : epHandlerSpec γ ρ k r h go!"handlePrepare" (.prepare m) := by
  exact h3.handlePrepare_wp_frozen γ ρ k r h m -- unit H3

theorem handlePreAccept.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PreAcceptM) : epHandlerSpec γ ρ k r h go!"handlePreAccept" (.preAccept m) := by
  exact handlePreAccept_wp_link γ ρ k r h m -- unit H2a

theorem handleAccept.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.EAcceptM) : epHandlerSpec γ ρ k r h go!"handleAccept" (.accept m) := by
  exact handleAccept_spec γ ρ k r h m -- unit H2c

theorem handleCommit.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ECommitM) : epHandlerSpec γ ρ k r h go!"handleCommit" (.commit m) := by
  exact handleCommit_spec γ ρ k r h m -- unit H2c

theorem handlePrepareReply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PrepareReplyM) :
    epHandlerSpec γ ρ k r h go!"handlePrepareReply" (.prepareReply m) := by
  exact h3.handlePrepareReply_wp_frozen γ ρ k r h m -- unit H3

theorem handleAcceptReply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.AcceptReplyM) :
    epHandlerSpec γ ρ k r h go!"handleAcceptReply" (.acceptReply m) := by
  exact handleAcceptReply_spec γ ρ k r h m -- unit H2c

theorem handlePreAcceptReply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PreAcceptReplyM) :
    epHandlerSpec γ ρ k r h go!"handlePreAcceptReply" (.preAcceptReply m) := by
  exact handlePreAcceptReply_spec γ ρ k r h m -- unit H2c2

theorem handlePreAcceptOK.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PreAcceptOKM) :
    epHandlerSpec γ ρ k r h go!"handlePreAcceptOK" (.preAcceptOK m) := by
  exact handlePreAcceptOK_spec γ ρ k r h m -- unit H2c2

theorem handleExecuted.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ExecutedM) : epHandlerSpec γ ρ k r h go!"handleExecuted" (.executed m) := by
  exact handleExecuted_spec γ ρ k r h m -- unit H2c2

/-- `executeOverwrite(eo)` (the executor's result, a self-message). -/
theorem executeOverwrite.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.ExecuteOverwriteM) :
    epHandlerSpec γ ρ k r h go!"executeOverwrite" (.executeOverwrite m) := by
  exact executeOverwrite_spec γ ρ k r h m -- unit H2c2

/-! ### The handlers (unit H1: `H1/GCoord.lean`, `H1/GParti.lean`; C-H1) -/

theorem handleRead.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r p w : Loc)
    (g : src.gryffproto.Read) :
    stepSpec γ ρ k r (App (repM r go!"handleRead") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (readEvOf g) := by
  exact handleRead.wp_proof γ ρ k r p w g -- unit H1
theorem handleWrite.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r p w : Loc)
    (g : src.gryffproto.Write) :
    stepSpec γ ρ k r (App (repM r go!"handleWrite") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (writeEvOf g) := by
  exact handleWrite.wp_proof γ ρ k r p w g -- unit H1
theorem handleForceWrite.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    stepSpec γ ρ k r (App (repM r go!"handleForceWrite") (Val #())) iprop(True) .forceWrite := by
  exact handleForceWrite.wp_proof γ ρ k r -- unit H1

theorem handleRead1Proxied.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read1ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead1Proxied") (.read1 m) := by
  exact handleRead1Proxied.wp_proof γ ρ k r m -- unit H1
theorem handleRead2Proxied.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read2ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead2Proxied") (.read2 m) := by
  exact handleRead2Proxied.wp_proof γ ρ k r m -- unit H1
theorem handleWrite1Proxied.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write1ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite1Proxied") (.write1 m) := by
  exact handleWrite1Proxied.wp_proof γ ρ k r m -- unit H1
theorem handleWrite2Proxied.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write2ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite2Proxied") (.write2 m) := by
  exact handleWrite2Proxied.wp_proof γ ρ k r m -- unit H1
theorem handleRead1Reply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read1ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead1Reply") (.read1Reply m) := by
  exact handleRead1Reply.wp_proof γ ρ k r m -- unit H1
theorem handleRead2Reply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read2ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead2Reply") (.read2Reply m) := by
  exact handleRead2Reply.wp_proof γ ρ k r m -- unit H1
theorem handleWrite1Reply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write1ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite1Reply") (.write1Reply m) := by
  exact handleWrite1Reply.wp_proof γ ρ k r m -- unit H1
theorem handleWrite2Reply.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write2ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite2Reply") (.write2Reply m) := by
  exact handleWrite2Reply.wp_proof γ ρ k r m -- unit H1

/-- **`Loop(slowClockChan)`**: one iteration of the run loop's `select`. A ready channel's element
(`msgChanP`: a message with its receive token, a peer's or, for a self-message, minted by the
replica's own send under the lock, `pendingOuts_self`; `reqChanP`: a request with its token and
its shape `Ev.Producible`; `recoverChanP`: a trigger whose guard
holds by `epaxosOwn_crtLb_le`; `forceWriteChan`), then `Lock` (the first time, `lock_boot`), the
type assertion (the element's kind is its channel's), the resolution (`resolve*`), the step
(`critical_step`, its `£ 2` from the iteration's pure steps before the resolution: `wp_pure_lc`),
the handler (`stepSpec`), `Unlock` with `lockedAt` at `t ++ [e]`. The cases
without an event (`slowClockChan`, the channels nothing sends to) have a `False` element. -/
theorem Loop.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h sc : Loc)
    (γsc : ChanNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗ handlerOf r h ∗
        isChanBag γsc sc (fun _ : Bool => iprop(False)) ∗ loopTok γ ρ k r }}
      (App (epM h go!"Loop") (Val #sc))
    {{ RET #(); loopTok γ ρ k r }} := by
  exact unitB.Loop_proof γ ρ k r h sc γsc
    (fun m p => handleRead1Proxied.wp γ ρ k r m p) (fun m p => handleRead2Proxied.wp γ ρ k r m p)
    (fun m p => handleWrite1Proxied.wp γ ρ k r m p) (fun m p => handleWrite2Proxied.wp γ ρ k r m p)
    (fun m p => handleRead1Reply.wp γ ρ k r m p) (fun m p => handleRead2Reply.wp γ ρ k r m p)
    (fun m p => handleWrite1Reply.wp γ ρ k r m p) (fun m p => handleWrite2Reply.wp γ ρ k r m p)
    (fun m p => handlePrepare.wp γ ρ k r h m p) (fun m p => handlePreAccept.wp γ ρ k r h m p)
    (fun m p => handleAccept.wp γ ρ k r h m p) (fun m p => handleCommit.wp γ ρ k r h m p)
    (fun m p => handlePrepareReply.wp γ ρ k r h m p)
    (fun m p => handlePreAcceptReply.wp γ ρ k r h m p)
    (fun m p => handlePreAcceptOK.wp γ ρ k r h m p) (fun m p => handleAcceptReply.wp γ ρ k r h m p)
    (fun m p => handleExecuted.wp γ ρ k r h m p) (fun m p => executeOverwrite.wp γ ρ k r h m p)
    (fun p w g => handleRead.wp γ ρ k r p w g) (fun p w g => handleWrite.wp γ ρ k r p w g)
    (fun p w g => HandleRMW.wp γ ρ k r h p w g) (handleForceWrite.wp γ ρ k r)
    (fun q i => startRecoveryForInstance.wp γ ρ k r h q i)

/-- **`run()`** (the goroutine `NewReplica` starts): `ConnectToPeers`, the `SetForceWrite` and
`WaitForClientConnections` goroutines, then `Loop` forever (`Shutdown` is false for good). -/
theorem run.wp (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG)) (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ connectRes γ ρ k r gR }}
      (App (repM r go!"run") (Val #()))
    {{ RET #(); True }} := by
  exact unitB.run_proof γ ρ k r gR (connectRes γ ρ k r gR) (listenerOwn γ ρ k gR)
    (Replica.ConnectToPeers.wp wp_rfl γ ρ k r gR) (Replica.WaitForClientConnections.wp γ ρ k r gR)
    (fun h sc γsc => Loop.wp γ ρ k r h sc γsc)

/-! ## The executor -/

/-- **`executeCommands()`** (the executor goroutine, started by `NewEPaxosRMWHandler` before the
replica is complete: `isExec`, the lock possibly in its boot state): the scan under the lock,
`executeCommand` → `findSCC` → `strongconnect` for each committed instance, a recovery trigger
(`recoverChanP`, with `epaxosOwn_crtLb`) for an instance missing too long. No credit budget: each
execution's `£ 2` comes from its own loop iteration's pure steps (`strongconnect.wp`'s "Later
credits"). -/
theorem executeCommands.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (xs : XS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isExec γ ρ k r h ∗
        execPriv2 ρ h xs [] ∗ ⌜xs.1 = [] ∧ ∀ u, xs.numF u = 0⌝ }} -- H-X-2 (b)
      (App (epM h go!"executeCommands") (Val #()))
    {{ RET #(); True }} := by
  exact X.executeCommands_wp γ ρ k r h xs -- unit X

/-- **`strongconnect(v, index)`** (stage 1's `wp_strongconnect`, over the model state): with the
lock held at trace `t` (search state `xs`, stack `S`), on a committed instance `vn` not yet
visited, Tarjan's invariant `TInv` over the dependencies of `stOf k t`: it returns with the lock
held at a later trace `t'` (it releases the lock while it waits for a missing or uncommitted
dependency: other events happen) and the search's post-state (`Post`). A popped component's
instances are executed in G4's order, each one (fork 9b1b858: the event is resolved before its
effects): `resolveExec`, the step `exec (Leader, Slot)` (`critical_step` with `execGuard` from the
component: `sccStep`), `PrevValTag`, the CAS, the `ExecuteOverwrite` sent to the run loop with its
receive token (`pendingOuts_self`: an ordinary owed self-message), `Status = EXECUTED`.

**Later credits** (review stage 2, finding 7). Each member's `critical_step` consumes `£ 2`; a
component's size is not known up front, so the precondition carries no credit budget. The proof
takes each member's two credits from that member's own iteration of `for _, w := range list`
(`epaxos-exec.go`): Perennial's GooseLang WP (`GooseGlobalGS .hasLC`) yields `£ 1` per pure
step (`wp_pure_lc`, `Perennial/Golang/Theory/ProofMode.lean`), and every iteration takes pure
steps before its `resolveExec` (the range loop's index test and increment, the `w.Cmds == nil`
comparison and its `for` test, the `w.lb != nil` test), at least two after the previous member's
`critical_step`. So credits are per iteration, not per call; the same holds in `Loop` (the
`select`'s dispatch and the type assertion step before `resolve*`). -/
theorem strongconnect.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h ex mtx : Loc)
    (p : ProphId) (t : List Ev) (xs : XS) (S : List replica.Node) (idx : Nat)
    (Gs : List replica.Node) (vn : replica.Node) (v idxp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isExec γ ρ k r h ∗
        h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ sync.ownMutex mtx ∗ lockedAt γ ρ k r p t xs ∗
        execPriv2 ρ h xs S ∗ idxp ↦ W64 (idx : Int) ∗ ghostMapElem ρ.ptrs vn DFrac.discard v ∗
        ⌜TInv (model.depR (pure.stOf k t)) (xs.toT S idx) Gs ∧ vn ∉ xs.1 ∧ xs.numF vn = 0 ∧
          (model.committedCopy (pure.stOf k t) vn).isSome ∧ scFacts2 (pure.stOf k t) xs S idx⌝ }}
      (App (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"strongconnect"))
        (Val #v)) (Val #idxp))
    {{ RET #true; ∃ (t' : List Ev) (xs' : XS) (S' : List replica.Node) (idx' : Nat),
        sync.ownMutex mtx ∗ lockedAt γ ρ k r p t' xs' ∗ execPriv2 ρ h xs' S' ∗
        idxp ↦ W64 (idx' : Int) ∗
        ⌜t <+: t' ∧ Post (model.depR (pure.stOf k t')) (xs.toT S idx) Gs vn (xs'.toT S' idx') ∧
          scFacts2 (pure.stOf k t') xs' S' idx'⌝ }} := by
  exact X.strongconnect_wp γ ρ k r h ex mtx p t xs S idx Gs vn v idxp -- unit X

end specs

end Perennial.gryff.replica2
