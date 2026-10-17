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
  icases Hinit with ⟨-, -, -, -, -, -, -, #HCan, #HDE, -⟩
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

/-- **The node meets `raftPropose`** (`node.Propose.spec`): raft's commit invariant and the
proposals' witnesses are the server's (`srvPropWits_of_raft`); a `Propose` over the request
path's context (`txnCtx_nodeCtx`) with the server's argument (`srvPropArg`, converted by
`srvPropAu_to_propAu`) returns raft's result in the server's terms (`srvPropRes`) and an error
the gRPC layer takes (`applyErrIs_of_propErr`). -/
theorem raftPropose_of_isNode (E : RNEnv GF) (γ : RNNames)
    (wp_Propose : letI : MemStorReg GF := ⟨γ.reg⟩; node.Propose.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ⊢
      raftPropose E.γr.raft (rnNodeIface γ) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hinv⟩
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, -, -, -, -⟩
  obtain ⟨Hraft, -, -⟩ := Hn
  iunfold raftPropose
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hinv
  isplitr
  · iapply srvPropWits_of_raft E.γr.raft $$ Hinv
  iintro !> %ctx %cd %dsl %data %Q %fresh %Φ !> ⟨#Hctx, #Hdata, %Hne, Harg⟩ HΦ
  ihave #Hnctx := txnCtx_nodeCtx ctx cd $$ Hctx
  ihave Harg' : propArg γ.node.raft data (srvLift E.γr.raft Q) fresh $$ [Harg]
  · iunfold srvPropArg at Harg
    unfold propArg
    rw [← Hraft]
    cases fresh with
    | true =>
      simp only [↓reduceIte]
      icases Harg with ⟨Hfr, #Hau⟩
      iunfold srvPropFresh at Hfr
      iframe Hfr
      iapply srvPropAu_to_propAu E.γr.raft data Q $$ Hinv Hau
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold srvDeposited at Harg
      iexact Harg
  wp_apply wp_Propose γ.node γ.id γ.nl dsl data (srvLift E.γr.raft Q) fresh ctx cd $$ [Harg']
    as %err ⟨Hres, #Herr⟩
  · iframe #
    iframe Harg'
    ipureintro; exact Hne
  iapply HΦ
  isplitl [Hres]
  · iunfold srvPropRes
    unfold propRes
    icases Hres with ⟨#Hdep, Hp⟩
    isplitr
    · iunfold srvDeposited
      rw [Hraft]
      iexact Hdep
    cases fresh with
    | true =>
      simp only [↓reduceIte]
      icases Hp with ⟨%γq, #Hp⟩
      iunfold srvIsProp
      iexists γq
      rw [Hraft]
      iexact Hp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
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
      rnStopOk γ.nl ⊢
      isRaftNodeIfc E γ (rnNodeIface γ) := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hinv, #Hcinv, #Hstop⟩
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnEnvOk at Henv
  icases Henv with ⟨%HT, %Hn, %Hmode, -, -, -, %HRQ⟩
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
      as ⟨Hdrv, Hcfg⟩
    · iframe #
      rw [Hstor]
      iframe Hbusy Hrcpt Hcfg
    iapply HΦ
    iunfold rnDrv
    iframe Hdrv
    iexists ca, cfg
    iexact Hcfg
  isplitr
  · -- `Tick`
    rw [HT]
    iintro !> %Φ !> Hcred HΦ
    wp_apply wp_Tick γ.node γ.id γ.nl $$ [Hcred]
    · iframe #; iframe Hcred
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

end bridge

end EtcdGrove
end Perennial
