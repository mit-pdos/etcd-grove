/-
**The server's raft contracts discharged from raft's node specs** (2026-10-16, stage R7b of the
raft v3.7 retarget, task B3; `notes/decisions.md`, D10). The three contracts the server's proofs
take on `raft.Node` and its storage -- `isRaftNodeIfc` (`Ready`, `Advance`, `Tick`, `Stop`,
`ReadIndex`), `raftPropose` (`Propose`) and `isRNMemStor` (`MemoryStorage.Append`),
`InvRaftNode.lean`/`InvRequest.lean` -- are theorems over raft's verified specs
(`Spec/go_etcd_io/raft/v3/node__*.lean`, `MemstorageInstance.lean`'s `memStorage_Append`), taken
as hypotheses the way a proof file takes its callees' specs; `Results.lean` instantiates them with
raft's linked `wp_*`. Lean-first (no Rocq counterpart).

What stays a premise (a persistent predicate below, so that it is visibly the only
assumption): `rnStopOk`, `Stop` returns. Raft's model never stops (`node.Stop` has no spec;
`run`'s stop case is vacuous: D10, "One premise stays").

The errors are proved to be ones the gRPC layer takes (`applyErrIs`): `nil` (`applyErrIs_nil`);
raft's `ErrStopped` (a package variable holding an `errors.New` error: the read package's facts,
`readInit`'s `errVarLeaf go_etcd_io.raft.v3.ErrStopped`); the context's (`applyErrIs_of_ctxErr`;
stage R7c, 2026-10-16: raft's `ctxErr` carries the value, `Canceled` or `DeadlineExceeded`, from
this repository's trust-boundary spec `context.ErrDone`, which `node.stepWithWaitOption` takes as
a callee; until then the premise `rnCtxErrOk`), by the read package's facts again (`errVarLeaf
context.Canceled`, `ctxDeadlineLeaf`), as `LinearizableReadNotify`'s own `ctx.Err()` is; and the
proposal's own result (`applyErrIs_of_stepErr`; stage R7c: raft's `propErr` carries `raft.Step`'s
error for the proposal, `stepErr`, `nil` or `ErrProposalDropped`, through the result channel's
handoff `propP`; until then the premise `rnPropErrOk` over any non-`nil` error), by the server's
package facts (`srvErrVars`' `errVarLeaf go_etcd_io.raft.v3.ErrProposalDropped`).
-/
module

public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section bridge
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The premises that stay (see the file header) -/

/-- **`Stop` returns** (persistent): the one clause of `isRaftNodeIfc` raft's specs do not
cover. -/
def rnStopOk (n : Loc) : IProp GF :=
  iprop(□ ({{ True }} (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }}))

instance rnStopOk_persistent (n : Loc) : Persistent (rnStopOk (GF := GF) n) := by
  unfold rnStopOk; infer_instance

/-! ## Raft's node, by the wrapper's names -/

/-- Raft's node, by the wrapper's names (`isNode`, with the storage registry's name). -/
abbrev rnIsNode (γ : RNNames) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  isNode γ.node γ.id γ.nl

/-- The `MemoryStorage`'s registration, by the wrapper's names (`isRaftNode`'s `Hreg`). -/
abbrev rnMemStorReg (γ : RNNames) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  memStorReg γ.ms γ.γs

/-- The `raft.Node` interface value holding the `*node` `γ.nl`. -/
abbrev rnNodeIface (γ : RNNames) : GoInterface :=
  interface.mkOk (go.GoType.PointerType node.ty) #γ.nl

/-- **The node's inbound methods** (persistent; D21 M2, 2026-10-19): `Step` of a peer's message
(raft's `stepP`, over a context the node API takes) and the two reports, which
`EtcdServer.Process`/`ReportUnreachable`/`ReportSnapshot` call (from the transport's goroutines,
as soon as it starts: so stated apart from `isRaftNodeIfc`, whose `ReadIndex` needs the server's
committed index, allocated later). -/
def rnStepIfc (γ : RNNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ml : Loc),
      {{ nodeCtx ctx cd ∗ stepP γ.node γ.id ml }}
        (App (App (Val #(methods ni.ty go!"Step" ni.v)) (Val #(GoInterface.ok ctx))) (Val #ml))
      {{ (err : GoInterface), RET #err; True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods ni.ty go!"ReportUnreachable" ni.v)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ (x : w64) (st : SnapshotStatus), {{ True }}
      (App (App (Val #(methods ni.ty go!"ReportSnapshot" ni.v)) (Val #x)) (Val #st))
      {{ RET #(); True }}))

instance rnStepIfc_persistent (γ : RNNames) (n : GoInterface) :
    Persistent (rnStepIfc (GF := GF) γ n) := by
  unfold rnStepIfc; infer_instance

/-- **`Stop` returns, of every node raft started** (persistent; D19r (A), 2026-10-18): `rnStopOk`
at the `*node` of every `rnIsNode` (a node `StartNode` returned, its `run` loop running), not at
every location (`∀ n, rnStopOk n`, until then, was false of Go: `Stop` on `nil` faults). True of
Go: `(*node).Stop` sends on `n.stop`, which the running loop receives, or finds `n.done` closed,
and then waits for `n.done`; it panics on no path. -/
def rnStopOkStarted : IProp GF :=
  iprop(□ ∀ γ : RNNames, rnIsNode γ -∗ rnStopOk γ.nl)

instance rnStopOkStarted_persistent : Persistent (rnStopOkStarted (GF := GF)) := by
  unfold rnStopOkStarted; infer_instance

/-! ## The errors -/

/-- **A done context's error is one the gRPC layer can take**: raft's `ctxErr` carries the value
(`ctxErrVal`: `context.Canceled` or `context.DeadlineExceeded`, by `context.ErrDone`), which the
read package's facts make `applyErrIs` (`errVarLeaf context.Canceled`, `ctxDeadlineLeaf`), as
`LinearizableReadNotify`'s own `ctx.Err()` is. -/
theorem applyErrIs_of_ctxErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      ctxErr cd err -∗ applyErrIs err := by
  iintro #Hpkg #Hcerr
  ihave #Hprd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
  · iPkgInit
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hprd
  icases Hinit with ⟨-, -, -, -, -, -, -, #HCan, #HDE⟩
  iunfold ctxErr at Hcerr
  icases Hcerr with ⟨-, -, -, #Hval⟩
  iunfold ctxErrVal at Hval
  icases Hval with ⟨%Hty, #Hcv⟩
  cases err with
  | nil => exact absurd Hty (by simp [context.isTypedErr])
  | ok ce =>
    icases Hcv with (#Hcv | #Hcv)
    · iapply errVar_applyErrIs _ (GoInterface.ok ce) $$ HCan
      iexists ce
      iframe Hcv
      ipureintro; rfl
    · icases HDE with ⟨%eD, #HeD, %HDl, #HDm⟩
      icombine Hcv HeD gives %Hce
      cases Hce
      obtain ⟨hl, hIs, hty, hkey⟩ := HDl
      iapply applyErrIs_valLeaf _ hl hIs hty hkey $$ HDm

/-- **The error of a `node` call that hands a message to `run`** (`nodeErr`: `nil`, `ErrStopped`,
or the context's), as the gRPC layer takes it (`applyErrIs`). -/
theorem applyErrIs_of_nodeErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      nodeErr cd err -∗ applyErrIs err := by
  iintro #Hpkg #Herr
  iunfold nodeErr at Herr
  icases Herr with (%Hnil | #Hstop | #Hcerr)
  · subst Hnil
    iapply applyErrIs_nil
  · ihave #Hprd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hprd
    icases Hinit with ⟨-, -, -, -, -, -, #HES, -, -⟩
    ihave ⟨%e, #He, #Ha⟩ := errVarLeaf_get _ $$ HES
    iunfold errStopped at Hstop
    icases Hstop with ⟨#He', %Hne⟩
    icombine He He' gives %Heq
    subst Heq
    iexact Ha
  · iapply applyErrIs_of_ctxErr cd err $$ Hpkg Hcerr

/-- **A proposal's own result is one the gRPC layer can take**: raft's `stepErr` (`nil` or
`ErrProposalDropped`), by the server's package facts (`srvErrVars`' `errVarLeaf` of raft's
`ErrProposalDropped`). -/
theorem applyErrIs_of_stepErr (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      stepErr err -∗ applyErrIs err := by
  iintro #Hpkg #Herr
  iunfold stepErr at Herr
  icases Herr with (%Hnil | #Hpd)
  · subst Hnil
    iapply applyErrIs_nil
  · ihave Hinit : (srvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, -, -, -, -, -, -, #HPD, -⟩⟩, -⟩
    iunfold errProposalDropped at Hpd
    icases Hpd with ⟨#He, %Hne⟩
    cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      iapply errVar_applyErrIs _ (GoInterface.ok e) $$ HPD
      iexists e
      iframe He
      ipureintro; rfl

/-- **The error of a proposal** (`propErr`: `nodeErr`, or the proposal's own result), as the
gRPC layer takes it. -/
theorem applyErrIs_of_propErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      propErr cd err -∗ applyErrIs err := by
  iintro #Hpkg #Herr
  iunfold propErr at Herr
  icases Herr with (#Hn | #Hs)
  · iapply applyErrIs_of_nodeErr cd err $$ Hpkg Hn
  · iapply applyErrIs_of_stepErr err $$ Hpkg Hs

/-! ## The entries -/

/-- The server's `entriesAt` as raft's list of read-only entries (the converse of
`entriesAt_of_entRO`). -/
theorem entRO_of_entriesAt (ls : List Loc) (es : List EntryModel) :
    entriesAt (GF := GF) ls es ⊢ [∗list] l;e ∈ ls;es.map EntryModel.toM, entRO l e := by
  iintro H
  iunfold entriesAt at H
  icases H with ⟨%Hlen, #Hall⟩
  iapply BigSepL2.bigSepL2_intro
  isplit
  · ipureintro; simp [Hlen]
  iintro !> %k %l %m %Hl %Hm
  rw [List.getElem?_map] at Hm
  cases He : es[k]? with
  | none => rw [He] at Hm; cases Hm
  | some e =>
    rw [He] at Hm
    simp only [Option.map_some, Option.some.injEq] at Hm
    subst Hm
    ihave #H := Hall $$ %k %l %e %Hl %He
    iunfold entryAt at H
    iexact H

/-- `rnFits` is `MemoryStorage.Append`'s premise, of the converted batch. -/
theorem rnFits_toM (es : List EntryModel) (h : rnFits es) :
    ∀ e0, (es.map EntryModel.toM).head? = some e0 →
      uint.Z e0.Index' + ((es.map EntryModel.toM).length : Int) ≤ 2 ^ 61 := by
  intro e0 he0
  rw [List.head?_map] at he0
  cases hh : es.head? with
  | none => rw [hh] at he0; cases he0
  | some e =>
    rw [hh] at he0
    simp only [Option.map_some, Option.some.injEq] at he0
    subst he0
    have := h e hh
    simpa [EntryModel.toM] using this

/-! ## The discharges -/

/-- **The `MemoryStorage` meets `isRNMemStor`** (raft's `memStorage_Append`, over the linked
`MemoryStorage.wp_Append`): the `Ready`'s right to append, with the index bound `rnAppendRight`
carries (`rnLogFits`'s), is the receipt `Advance` takes. -/
theorem isRNMemStor_of_memstorage (γ : RNNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rnMemStorReg γ ⊢
      isRNMemStor γ γ.ms := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Hreg⟩
  iunfold isRNMemStor
  iintro !> %sl %esL %es %Φ !> ⟨#Hsl, #Hents, Hright⟩ HΦ
  iunfold rnAppendRight at Hright
  icases Hright with ⟨Hright, %Hfit⟩
  ihave #Hpts : entsPts sl DFrac.discard (es.map EntryModel.toM) $$ []
  · iunfold entsPts
    iexists esL
    iframe Hsl
    iapply entRO_of_entriesAt esL es $$ Hents
  wp_apply memStorage_Append γ.ms γ.γs (es.map EntryModel.toM) sl DFrac.discard (rnFits_toM es Hfit)
    $$ [Hright] as ⟨Hrcpt, -⟩
  · iframe #; iframe Hright
  iapply HΦ
  iunfold rnAppendReceipt
  iexact Hrcpt

/-- **A change `ccRaftOk` admits leaves the voters as they are** (`CCShrink`, the static mode's
premise of `node.ApplyConfChange`; audit phase B3, 2026-10-18): an `AddNode` of a voter
(`makeVoter` of a voter), or of the node `0` (skipped), on a non-empty configuration. -/
theorem ccShrink_of_raftOk (cfg : GSet w64) (cm : CCV1M) (h : ccRaftOk cfg cm) :
    CCShrink cfg (ccV2Of (.v1 cm)).1 (ccV2Of (.v1 cm)).2 := by
  obtain ⟨ht, k, hk, hid⟩ := h
  have hne : cfg ≠ ∅ := by
    intro he
    rw [he] at hk
    have := (GMap.elem_of_gset _ _).1 hk
    simp at this
  rcases hid with hid | hid0
  · by_cases h0 : cm.nodeId = W64 0
    · exact CCNoop.shrink (ccApplyM_v1_noop cfg cm h0 hne)
    · intro lrn Hd
      refine ⟨lrn, GMap.subseteq_refl _, ?_⟩
      have hin : cm.nodeId ∈ cfg := by rw [hid]; exact hk
      have hL : cm.nodeId ∉ lrn := fun h' => Hd _ h' hin
      have hc : ({ Type' := cm.type, NodeId' := cm.nodeId } : ConfChangeSingleM) =
          addNodeCC cm.nodeId := by rw [ht]
      show ccApplyM (W32 0) [{ Type' := cm.type, NodeId' := cm.nodeId }] (cfgState cfg lrn) =
        some (cfgState cfg lrn)
      apply ccApplyM_single
      rw [hc]
      have := simpleM_cfgState_addNode cfg lrn cm.nodeId h0 hL Hd
      rw [GMap.insert_id _ _ _ ((GMap.elem_of_gset _ _).1 hin)] at this
      exact this
  · exact CCNoop.shrink (ccApplyM_v1_noop cfg cm hid0 hne)

/-- **The node meets `raftPropose`** (`node.Propose.spec`, and since audit phase B3,
2026-10-18, `node.ApplyConfChange.spec` in the static mode for a change `ccRaftOk` admits,
`ccShrink_of_raftOk`): raft's commit invariant and the
proposals' witnesses are the server's (`srvPropWits_of_raft`); a `Propose` over the request
path's context (`txnCtx_nodeCtx`) with the server's argument (`srvPropArg`, converted by
`srvPropAu1_to_propAu1`) returns raft's result in the server's terms (`srvPropRes`) and an error
the gRPC layer takes (`applyErrIs_of_propErr`). -/
theorem raftPropose_of_isNode (E : RNEnv GF) (γ : RNNames)
    (wp_Propose : letI : MemStorReg GF := ⟨γ.reg⟩; node.Propose.spec (GF := GF) (hG := hG))
    (wp_ApplyConfChange : letI : MemStorReg GF := ⟨γ.reg⟩;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ⊢
      raftPropose E.γr.raft (rnNodeIface γ) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hinv⟩
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, %Hmode, -, -, -, -, -⟩
  obtain ⟨Hraft, -, -⟩ := Hn
  obtain ⟨Hstatic, -⟩ := Hmode
  iunfold raftPropose
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hinv
  isplitr
  · iapply srvPropWits_of_raft E.γr.raft $$ Hinv
  isplitr
  rotate_left
  · -- `ApplyConfChange` (audit phase B3): raft's static mode, a change that keeps the voters
    iintro !> %c %cm %Hok %Φ !> Hc HΦ
    have hsh : CCShrink γ.node.raft.reCfg (ccV2Of (.v1 cm)).1 (ccV2Of (.v1 cm)).2 := by
      rw [← Hraft]; exact ccShrink_of_raftOk _ cm Hok
    wp_apply (wp_ApplyConfChange γ.node γ.id γ.nl c (.v1 cm) [] 0 (cfgState ∅ ∅) 0 ⟨W64 0, W64 0, W32 0, []⟩
        (cfgState ∅ ∅) (fun _ => hsh)
        (fun dec c0 h0 h1 hd => absurd (hd ▸ Hstatic) (by simp))) $$ [Hc]
      as %csp %cs ⟨Hcs, -⟩
    · iframe #
      iframe Hc
      ileft; ipureintro; exact Hstatic
    iapply HΦ
    iexists cs
    iexact Hcs
  iintro !> %ctx %cd %dsl %data %Q %Φ !> ⟨#Hctx, #Hdata, %Hne, Harg⟩ HΦ
  ihave #Hnctx := txnCtx_nodeCtx ctx cd $$ Hctx
  iunfold srvPropArg at Harg
  icases Harg with ⟨Hfr, Hau⟩
  iunfold srvPropFresh at Hfr
  -- (2026-10-21) the data registered with the lifted predicate (raft's public ghost step), then
  -- proposed once with the update (D21 M6: fired at most once)
  ihave #Hnode' : isNode γ.node γ.id γ.nl $$ []
  · iunfold rnIsNode at Hnode; iexact Hnode
  imod node_prop_register γ.node γ.id γ.nl data (srvLift E.γr.raft Q) ⊤ CoPset.subseteq_top
    $$ Hnode' [Hfr] with #Hpi
  · rw [← Hraft]; iexact Hfr
  ihave Harg' : propArg γ.node.raft data (srvLift E.γr.raft Q) $$ [Hau]
  · unfold propArg
    iframe Hpi
    rw [← Hraft]
    iapply srvPropAu1_to_propAu1 E.γr.raft data Q $$ Hinv Hau
  wp_apply wp_Propose γ.node γ.id γ.nl dsl data (srvLift E.γr.raft Q) ctx cd $$ [Harg']
    as %err #Herr
  · iframe #
    iframe Harg'
    ipureintro; exact Hne
  iapply HΦ
  isplitr
  · iunfold srvPropRes
    ihave #Hdep := propIs_deposited $$ Hpi
    isplitr
    · iunfold srvDeposited
      rw [Hraft]
      iexact Hdep
    iunfold srvIsProp
    rw [Hraft]
    iexact Hpi
  · iapply applyErrIs_of_propErr cd err $$ Hpkg Herr

/-- **The node meets `isRaftNodeIfc`** but for `Stop` (`rnStopOk`, the premise): `Ready` from
`node.Ready.spec` (`rnReadyP` is raft's `readyP`), `Advance` from `node.Advance.spec` (the
static mode's premise vacuous, the storage the `MemoryStorage`: `rnEnvOk`), `Tick` from
`node.Tick.spec` (`E.T` raft's tick credit), `ReadIndex` from `node.ReadIndex.spec` over the
request's context: the committed log reaching the caller's bound (`committedAtLeast_log`), the
read's update converted (`srvReadAu_to_readAu`), the credit and the fresh token raft's; the
registration `E.RQ id n Qr` is raft's deposit (`srvRQ`), the error `applyErrIs_of_nodeErr`'s. -/
theorem isRaftNodeIfc_of_isNode (E : RNEnv GF) (γ : RNNames) (s : Loc)
    (wp_Ready : letI : MemStorReg GF := ⟨γ.reg⟩; node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : letI : MemStorReg GF := ⟨γ.reg⟩; node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : letI : MemStorReg GF := ⟨γ.reg⟩; node.Tick.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : letI : MemStorReg GF := ⟨γ.reg⟩; node.ReadIndex.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ∗ srvCommittedInv s E.γr ∗
      rnStopOk γ.nl ∗ rnMemStorReg γ ⊢
      isRaftNodeIfc E γ (rnNodeIface γ) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hinv, #Hcinv, #Hstop, #Hreg⟩
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnEnvOk at Henv
  icases Henv with ⟨%HT, %Hn, %Hmode, -, -, -, -, %HRQ⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  obtain ⟨Hstatic, Hstor⟩ := Hmode
  iunfold isRaftNodeIfc
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · -- `Ready`
    iintro !> %Φ !> - HΦ
    wp_apply wp_Ready γ.node γ.id γ.nl $$ [] as %ch #Hch
    · iframe #
    iapply HΦ
    iunfold isReadyChan at Hch
    iunfold rnReadyP
    iexact Hch
  isplitr
  · -- `Advance`
    iintro !> %d %ce %es %Φ !> ⟨Hbusy, Hrcpt⟩ HΦ
    iunfold rnBusy at Hbusy
    icases Hbusy with ⟨Hbusy, %ca, %cfg, Hcfg⟩
    iunfold rnAppendReceipt at Hrcpt
    wp_apply wp_Advance γ.node γ.id γ.nl (rnLogOf γ (d ++ ce)) (es.map EntryModel.toM) ca cfg
      (fun h => by rw [Hstatic] at h; simp [RNMode.isDyn] at h) $$ [Hbusy Hrcpt Hcfg]
      as ⟨Hdrv, Hcfg, %x, #Hfl, %Hx⟩
    · iframe #
      rw [Hstor]
      iframe Hbusy Hrcpt Hcfg
    iapply HΦ
    isplitl [Hdrv Hcfg]
    · iunfold rnDrv
      iframe Hdrv
      iexists ca, cfg
      iexact Hcfg
    -- (D19i part 1) the floor's witness, the `MemoryStorage`'s
    iunfold memFloorAtLeast
    iexists x
    isplitr
    · ihave #Hfl' : storFloor (memStorIface γ.ms) x $$ []
      · rw [← Hstor]; iexact Hfl
      iapply memStorFloor_at γ.ms γ.γs x $$ Hreg Hfl'
    ipureintro
    simp only [rnLogOf, List.length_map, List.append_assoc] at Hx ⊢
    exact Hx
  isplitr
  · -- `Tick`, for a time receipt (D19b: raft's tick credit)
    iintro !> %Φ !> Hcred HΦ
    wp_apply wp_Tick γ.node γ.id γ.nl $$ [Hcred]
    · iframe #; unfold tickCred; iframe Hcred
    iapply HΦ
    itrivial
  isplitr
  · -- `Stop`: the premise
    iunfold rnStopOk at Hstop
    iexact Hstop
  · -- `ReadIndex`
    iintro !> %ctx %cd %sl %id %n %Qr %Φ !> ⟨#Hctx, #Hsl, #Hcal, #Hau, Hcred, Hfresh⟩ HΦ
    imod committedAtLeast_log s E.γr n ⊤ CoPset.subseteq_top $$ Hcinv Hcal with ⟨%L, #HL, %HnL⟩
    ihave #HL' : isCommitted γ.node.raft (srvLogOf E.γr.raft L) $$ []
    · iunfold srvRLogLb at HL
      rw [← Hraft]
      iexact HL
    ihave #Hau' : readAu γ.node.raft (srvLift E.γr.raft Qr) $$ []
    · rw [← Hraft]
      iapply srvReadAu_to_readAu E.γr.raft Qr $$ Hinv Hau
    ihave Hfresh' : rdFresh γ.node.raft (beBytes id) $$ [Hfresh]
    · iunfold srvRdFresh at Hfresh
      rw [← Hraft]
      iexact Hfresh
    ihave #Hnctx : nodeCtx ctx cd $$ []
    · iunfold nodeCtx
      iright
      iexact Hctx
    iunfold rnReadCred at Hcred
    wp_apply wp_ReadIndex γ.node γ.id γ.nl sl (beBytes id) (srvLift E.γr.raft Qr)
      (srvLogOf E.γr.raft L) ctx cd $$ [Hfresh' Hcred] as %err ⟨⟨%Lc, %HLc, #Hreq, #Hrd⟩, #Herr⟩
    · iframe #; iframe Hfresh' Hcred
    iapply HΦ
    isplitr
    · iapply applyErrIs_of_nodeErr cd err $$ Hpkg Herr
    · iintro %_
      rw [HRQ]
      iunfold srvRQ
      iintro !>
      iexists Lc
      isplitr
      · rw [Hraft]; iexact Hrd
      isplitr
      · rw [Hraft]; iexact Hreq
      · ipureintro
        have h := HLc.length_le
        rw [srvLogOf_length, Hpre] at h
        push_cast
        omega

/-- **The node meets `rnStepIfc`** (D21 M2): raft's `node.Step`, `ReportUnreachable`,
`ReportSnapshot`, over raft's `isNode`. -/
theorem rnStepIfc_of_isNode (γ : RNNames)
    (wp_Step : letI : MemStorReg GF := ⟨γ.reg⟩; node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : letI : MemStorReg GF := ⟨γ.reg⟩;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : letI : MemStorReg GF := ⟨γ.reg⟩;
      node.ReportSnapshot.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ rnIsNode γ ⊢
      rnStepIfc γ (rnNodeIface γ) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Hnode⟩
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnStepIfc
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %ml %Φ !> ⟨#Hctx, Hst⟩ HΦ
    wp_apply wp_Step γ.node γ.id γ.nl ml ctx cd $$ [Hst] as %err -
    · iframe #; iframe Hst
    iapply HΦ
    itrivial
  isplitr
  · iintro !> %x %Φ !> - HΦ
    wp_apply wp_ReportUnreachable γ.node γ.id γ.nl x $$ []
    · iframe #
    iapply HΦ
    itrivial
  · iintro !> %x %st %Φ !> - HΦ
    wp_apply wp_ReportSnapshot γ.node γ.id γ.nl x st $$ []
    · iframe #
    iapply HΦ
    itrivial

end bridge

end EtcdGrove
end Perennial
