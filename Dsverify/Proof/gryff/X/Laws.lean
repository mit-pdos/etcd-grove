/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Laws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: the laws the executor's proofs assume, over a generic `GF`

The parts of the replica's lock invariant and handle that are stated at `GF` only (the
trace's half `traceHalf`, the prophecy `replicaProph`, the obligations `pendingOuts`, the rest of
the replica's heap, the boot flag, the receive tokens, the invariant `gryffInv2`) are abstract
predicates here, with the laws the executor uses (`critical_step`, `resolveExec`,
`pendingOuts_self`, `step_ok_exec`, the trace's lower bound, the stability of committed copies:
request H-X-1, and the dependencies' range: request H-X-3) as fields of `ExecLaws`.
`GryffProof/X/Bridge.lean` builds an `ExecLaws` at `GF` from `Replica2/*` and `Proto2/*`.
-/
module

public import Dsverify.Proof.gryff.X.Defs
public import Dsverify.Proof.gryff.X.Pure
public import Dsverify.Proof.gryff.Pure.Run
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out StepRes committedCopy execGuard inBox)
open Perennial.gryff.replica (XS Node)
open Perennial.gryff.replica2 (Repl2Names rid32 handlerIface)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

/-- The committed copies' dependencies are inside the instance space (each `Deps[q]` below
`SLOTS`: `strongconnect` indexes `InstanceSpace[q][i]` for `i ≤ Deps[q]`), and their commands
have the system's shape (`cmdsOk`: CAS on key 0; the executor indexes `PrevValTag` by the
command's key, the model by key 0). Request H-X-3. -/
def DepsOk (s : RState) : Prop :=
  (∀ n c, committedCopy s n = some c →
    (∀ j : Nat, j < 3 → sint.Z (c.deps.at j) < model.SLOTS) ∧ model.cmdsOk c.cmds = true) ∧
  ∀ q : w32, sint.Z (s.crt q) ≤ model.SLOTS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The executor's view of replica `k`'s lock and handle (`*gryff.Replica` at `r`, its EPaxos
handler at `h`, its trace prophecy `p`, the executor's search names in `ρ`). -/
structure ExecLaws (k : Fin 3) (ρ : Repl2Names) (r h : Loc) (p : ProphId) where
  /-- the trace's half (`traceHalf`) -/
  TH : List Ev → IProp GF
  /-- the trace's lower bound (`traceLb`, persistent) -/
  TLb : List Ev → IProp GF
  /-- the prophecy at a trace, with words resolved ahead (`replicaProph`) -/
  Pr : List Ev → List w64 → IProp GF
  /-- the obligations (`pendingOuts`) -/
  PO : List Ev → List Out → IProp GF
  /-- the replica's heap but the EPaxos handler's and the search state's half -/
  Rs : RState → IProp GF
  /-- the lock's boot half after the boot (`ghostVar ρ.boot ½ false`) -/
  Bt : IProp GF
  /-- the lock's boot half before the boot (`ghostVar ρ.boot ½ true`) -/
  B : IProp GF
  /-- a self-message's receive token (`∃ n, rxTok γ k k n m`) -/
  Tok : Msg → IProp GF
  /-- the lock invariant (`replicaLockInv`) -/
  LI : IProp GF
  /-- the persistent facts the laws need (`gryffInv2`, `predsSet`, the handler field) -/
  Inv : IProp GF
  tlb_pers : ∀ t, Persistent (TLb t)
  inv_pers : Persistent Inv
  /-- the lock invariant, opened -/
  li_open : Inv ∗ LI ⊢ (∃ t xs, TH t ∗ Pr t [] ∗ Rs (stOf k t) ∗
      epaxosOwnG ρ h r xs (stOf k t) ∗ ghostVar ρ.xs (1 : Qp).half xs ∗ PO t [] ∗ Bt) ∨
    (∃ xs, epaxosOwnG ρ h r xs (model.RState.init k.val) ∗ ghostVar ρ.xs (1 : Qp).half xs ∗ B)
  li_closeA : ∀ t xs, TH t ∗ Pr t [] ∗ Rs (stOf k t) ∗ epaxosOwnG ρ h r xs (stOf k t) ∗
      ghostVar ρ.xs (1 : Qp).half xs ∗ PO t [] ∗ Bt ⊢ LI
  li_closeB : ∀ xs, Inv ∗ epaxosOwnG ρ h r xs (model.RState.init k.val) ∗
      ghostVar ρ.xs (1 : Qp).half xs ∗ B ⊢ LI
  /-- the trace's lower bound (`traceHalf_lb`) -/
  th_lb : ∀ t, TH t ⊢ |={⊤}=> TH t ∗ TLb t
  /-- after a release of the lock: the trace extends the bound and the committed copies are
  stable (request H-X-1) -/
  th_relock : ∀ t t', Inv ∗ TH t' ∗ TLb t ⊢ |={⊤}=> TH t' ∗ ⌜t <+: t' ∧ Stable (stOf k t) (stOf k t')⌝
  /-- after a release of the lock: existing instances still exist (request H-X-1) -/
  th_kept : ∀ t t', Inv ∗ TH t' ∗ TLb t ⊢ |={⊤}=> TH t' ∗
    ⌜∀ q i : w32, ((stOf k t).inst q i).isSome → ((stOf k t').inst q i).isSome⌝
  /-- the committed copies' dependencies are in the instance space (request H-X-3) -/
  th_deps : ∀ t, Inv ∗ TH t ⊢ |={⊤}=> TH t ∗ ⌜DepsOk (stOf k t)⌝
  /-- the execution's step is `.ok` with its guard (`step_ok_exec`) -/
  th_ok : ∀ t q i c, inBox q i = true → (stOf k t).inst q i = some c →
    c.status = model.St.COMMITTED → execGuard (stOf k t) (sint.Z q, sint.Z i) →
    Inv ∗ TH t ⊢ |={⊤}=> TH t ∗ ⌜∃ s' o, model.stepR k (stOf k t) (.exec q i) = .ok (s', o)⌝
  /-- `resolveExec(q, i)` (`resolveExec.wp`) -/
  res_wp : ∀ t ws (q i : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        globalAddr src.gryff.traceProph ↦□ p ∗ Pr t ws ∗ iprop(True) }}
      (App (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"resolveExec"))
        (Val #q)) (Val #i))
    {{ RET #(); Pr t (ws ++ model.evCodec.enc (.exec q i)) ∗ iprop(True) }}
  /-- the step (`critical_step`) -/
  crit : ∀ t (q i : w32) s' outs, model.stepR k (stOf k t) (.exec q i) = .ok (s', outs) →
    Inv ∗ TH t ∗ Pr t (model.evCodec.enc (.exec q i)) ∗ £ 2 ∗ PO t [] ⊢
      |={⊤}=> TH (t ++ [.exec q i]) ∗ Pr (t ++ [.exec q i]) [] ∗ PO (t ++ [.exec q i]) outs ∗
        ⌜stOf k (t ++ [.exec q i]) = s'⌝
  /-- a self-message's token (`pendingOuts_self`) -/
  self : ∀ t m outs, Inv ∗ PO t (.send k m :: outs) ⊢ |={⊤}=> PO t outs ∗ Tok m
  /-- the rest of the heap does not see an execution (`coordOwn_congr`, ...) -/
  rs_congr : ∀ s s' (q i : w32) outs, model.stepR k s (.exec q i) = .ok (s', outs) →
    Rs s ⊢ Rs s'
  /-- the replica id -/
  rs_id : ∀ s, Rs s ⊢ ⌜s.id = rid32 k⌝

attribute [instance] ExecLaws.tlb_pers ExecLaws.inv_pers

variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

/-- The lock's contents at trace `t` and search state `xs` (`lockedAt`, opened). -/
def ExecLaws.LA (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) : IProp GF :=
  iprop(L.TH t ∗ L.Pr t [] ∗ L.Rs (stOf k t) ∗ epaxosOwnG ρ h r xs (stOf k t) ∗
    ghostVar ρ.xs (1 : Qp).half xs ∗ L.PO t [] ∗ L.Bt)

theorem ExecLaws.LA_open (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.LA t xs ⊣⊢ L.TH t ∗ L.Pr t [] ∗ L.Rs (stOf k t) ∗ epaxosOwnG ρ h r xs (stOf k t) ∗
      ghostVar ρ.xs (1 : Qp).half xs ∗ L.PO t [] ∗ L.Bt := .rfl

/-- The executor's handle (`isExec`, with the handler `h`, the mutex `mtx`, the `Exec` at `ex`,
the generic replica `gR`), the persistent facts of the laws, and `dlog` off. -/
def ExecLaws.isExecG (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) : IProp GF :=
  iprop(r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗ globalAddr src.gryff.traceProph ↦□ p ∗
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ ex.[src.gryff.Exec, go!"r"] ↦□ h ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
    gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
    sync.isMutex mtx L.LI ∗
    bagAtG (t := go.GoType.PointerType src.gryff.ExecuteOverwrite.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"executeOverwriteChan" "executeOverwrite" (eoChanPG L.Tok) ∗
    bagAtG (t := go.GoType.PointerType src.gryff.instanceId.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"instancesToRecover" "recover" (recoverChanPG ρ) ∗
    L.Inv ∗ globalAddr src.dlog.DLOG ↦□ false)

instance ExecLaws.isExecG_pers (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) :
    Persistent (L.isExecG gR mtx ex) := by
  unfold ExecLaws.isExecG bagAtG; infer_instance

theorem ExecLaws.isExecG_open (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) :
    L.isExecG gR mtx ex ⊣⊢ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h ∗
    r.[src.gryff.Replica, go!"mtx"] ↦□ mtx ∗ globalAddr src.gryff.traceProph ↦□ p ∗
    h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ ex.[src.gryff.Exec, go!"r"] ↦□ h ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
    gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
    sync.isMutex mtx L.LI ∗
    bagAtG (t := go.GoType.PointerType src.gryff.ExecuteOverwrite.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"executeOverwriteChan" "executeOverwrite" (eoChanPG L.Tok) ∗
    bagAtG (t := go.GoType.PointerType src.gryff.instanceId.ty) ρ src.gryff.EPaxosRMWHandler h
      go!"instancesToRecover" "recover" (recoverChanPG ρ) ∗
    L.Inv ∗ globalAddr src.dlog.DLOG ↦□ false :=
  .rfl

end

end Perennial.gryff.X
