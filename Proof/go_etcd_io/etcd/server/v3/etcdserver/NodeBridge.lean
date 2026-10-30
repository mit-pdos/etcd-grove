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

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink


open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! (2026-10-30, the repair) The premises `rnStopOk`/`rnStopOkStarted` (`Stop` returns) are gone:
raft's `node.Stop.spec` covers `Stop`, over the node's whole running token. -/

/-! ## Raft's node, by the wrapper's names -/

/-- Raft's node, by the wrapper's names (the node API's `isNode` of the node `nl` in the
server's cluster). -/
def rnIsNode (γ : RNNames) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  isNode γ.nl γ.node.cl srvClusterN γ.id

instance rnIsNode_persistent (γ : RNNames) : Persistent (rnIsNode (GF := GF) γ) := by
  unfold rnIsNode
  letI := srvStor (GF := GF) γ.node
  exact isNode_persistent _ _ _ _

/-- The `MemoryStorage`'s registration, by the wrapper's names (`isRaftNode`'s `Hreg`). -/
abbrev rnMemStorReg (γ : RNNames) : IProp GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  memStorReg γ.ms γ.γs

/-- The `raft.Node` interface value holding the `*node` `γ.nl`. -/
abbrev rnNodeIface (γ : RNNames) : GoInterface :=
  interface.mkOk (go.GoType.PointerType node.ty) #γ.nl

/-- **The node's inbound methods** (persistent; D21 M2, 2026-10-19): `Step` of a peer's message
(the node API's `stepIn`, over a context the node API takes) and the two reports, which
`EtcdServer.Process`/`ReportUnreachable`/`ReportSnapshot` call (from the transport's goroutines,
as soon as it starts: so stated apart from `isRaftNodeIfc`, whose `ReadIndex` needs the server's
committed index, allocated later). -/
def rnStepIfc (γ : RNNames) (n : GoInterface) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ml : Loc),
      {{ nodeCtx ctx cd ∗ stepIn γ.node.cl srvClusterN γ.id ml }}
        (App (App (Val #(methods ni.ty go!"Step" ni.v)) (Val #(GoInterface.ok ctx))) (Val #ml))
      {{ (err : GoInterface), RET #err; nodeErr cd err }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods ni.ty go!"ReportUnreachable" ni.v)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ (x : w64) (st : SnapshotStatus), {{ True }}
      (App (App (Val #(methods ni.ty go!"ReportSnapshot" ni.v)) (Val #x)) (Val #st))
      {{ RET #(); True }}))

instance rnStepIfc_persistent (γ : RNNames) (n : GoInterface) :
    Persistent (rnStepIfc (GF := GF) γ n) := by
  unfold rnStepIfc; infer_instance


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

/-- **The `MemoryStorage` meets `isRNMemStor`** (raft's linked `MemoryStorage.wp_Append`, under the
storage's lock invariant `memStorLock`; 2026-10-30, the repair: until then raft's `memStorage_Append`): the `Ready`'s right to append, with the index bound `rnAppendRight`
carries (`rnLogFits`'s), is the receipt `Advance` takes. -/
theorem isRNMemStor_of_memstorage (γ : RNNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rnMemStorReg γ ∗
      memStorLock γ.ms γ.γs ⊢
      isRNMemStor γ γ.ms := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Hreg, #Hlock⟩
  iunfold isRNMemStor
  iintro !> %sl %esL %es %Φ !> ⟨#Hsl, #Hents, Hright⟩ HΦ
  iunfold rnAppendRight at Hright
  icases Hright with ⟨Hright, %Hfit⟩
  obtain ⟨Hfits, Hcons⟩ := Hfit
  ihave #Hpts : entsPts sl DFrac.discard (es.map EntryModel.toM) $$ []
  · iunfold entsPts
    iexists esL
    iframe Hsl
    iapply entRO_of_entriesAt esL es $$ Hents
  iunfold appendRight at Hright
  icases Hright with (%Hnil | ⟨%e0, %old, %Hh, Hl, He⟩)
  · -- nothing to append
    have hes : es = [] := by simpa using Hnil
    subst hes
    wp_apply (MemoryStorage.wp_Append γ.ms γ.γs 0 [] [] sl DFrac.discard
        (fun _ _ h => by cases h) (by simp)) $$ [] as -
    · iframe #
      simp only [List.map_nil, ite_true]
      iframe Hpts
    iapply HΦ
    iunfold rnAppendReceipt
    iunfold appendReceipt
    ileft; ipureintro; rfl
  · obtain ⟨x, hx, rfl⟩ : ∃ x, es.head? = some x ∧ e0 = x.toM := by
      rw [List.head?_map] at Hh
      cases hh : es.head? with
      | none => rw [hh] at Hh; cases Hh
      | some x => rw [hh] at Hh; cases Hh; exact ⟨x, rfl, rfl⟩
    have hne : es.map EntryModel.toM ≠ [] := by
      intro h; rw [List.map_eq_nil_iff] at h; subst h; cases hx
    have hidx : ∀ (j : Nat) (e : EntryM), (es.map EntryModel.toM)[j]? = some e →
        uint.nat e.Index' = uint.nat x.toM.Index' + j := by
      intro j e he
      rw [List.getElem?_map] at he
      cases hj : es[j]? with
      | none => rw [hj] at he; cases he
      | some y =>
        rw [hj] at he; cases he
        exact Hcons x hx j y hj
    have hfit : uint.nat x.toM.Index' + (es.map EntryModel.toM).length ≤ 2 ^ 61 := by
      have := Hfits x hx
      simp only [List.length_map]
      show uint.nat x.index + es.length ≤ 2 ^ 61
      have : (uint.nat x.index : Int) = uint.Z x.index := by word
      omega
    ihave Hl := memStorLog_to γ.ms γ.γs _ _ _ $$ Hreg Hl
    ihave He := memStorEnd_to γ.ms γ.γs _ $$ Hreg He
    wp_apply (MemoryStorage.wp_Append γ.ms γ.γs (uint.nat x.toM.Index') old
        (es.map EntryModel.toM) sl DFrac.discard hidx hfit) $$ [Hl He] as ⟨-, Hpost⟩
    · iframe #
      simp only [ite_eq_right hne]
      iframe Hl He
    simp only [ite_eq_right hne]
    icases Hpost with ⟨Hl, He⟩
    iapply HΦ
    iunfold rnAppendReceipt
    iunfold appendReceipt
    iright
    iexists x.toM, es.map EntryModel.toM
    isplitr
    · ipureintro
      refine ⟨?_, rfl⟩
      rw [List.head?_map, hx]; rfl
    ihave #Hnil := memLog_nil γ.γs (uint.nat x.toM.Index') DFrac.discard
    ihave #Hnil' := memStorLog_of γ.ms γ.γs _ _ _ $$ Hreg Hnil
    ihave Hl := memStorLog_of γ.ms γ.γs _ _ _ $$ Hreg Hl
    ihave He := memStorEnd_of γ.ms γ.γs _ $$ Hreg He
    simp only [List.length_nil, Nat.add_zero]
    rw [show x.toM.Index' = x.index from rfl]
    iframe Hnil' Hl He

/-- **The error of `Propose`** (the node API's: `nil`, `ErrStopped`, `ErrProposalDropped` or the
context's), as the gRPC layer takes it. -/
theorem applyErrIs_of_proposeErr (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      (⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err) -∗
      applyErrIs err := by
  iintro #Hpkg #Herr
  icases Herr with (%Hnil | #Hs | #Hpd | #Hc)
  · iapply applyErrIs_of_nodeErr cd err $$ Hpkg []
    iunfold nodeErr; ileft; ipureintro; exact Hnil
  · iapply applyErrIs_of_nodeErr cd err $$ Hpkg []
    iunfold nodeErr; iright; ileft; iexact Hs
  · iapply applyErrIs_of_stepErr err $$ Hpkg []
    iunfold stepErr; iright; iexact Hpd
  · iapply applyErrIs_of_ctxErr cd err $$ Hpkg Hc

/-- The cluster's kind reads only the cluster. -/
theorem srvClusterOk_congr (γ1 γ2 : ServerRaftNames) (h : γ1.raft = γ2.raft) :
    srvClusterOk (GF := GF) γ1 = srvClusterOk γ2 := by
  unfold srvClusterOk; rw [h]

variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The node meets `raftPropose`** (2026-10-27: the node API's `node.Propose.spec`, the server's
proposal registered and its update converted, `srvProp_register`/`srvPropAu_api`; and
`node.ApplyConfChange.spec` in a static cluster for a change `ccRaftOk` admits,
`ccShrink_addVoter`): the proposals' witnesses are the server's registry's
(`srvPropWits_of`). -/
theorem raftPropose_of_isNode (E : RNEnv GF) (γ : RNNames)
    (wp_Propose : letI := srvStor (GF := GF) γ.node;
      node.Propose.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvRaftLogInv E.γr.raft ⊢
      raftPropose E.γr.raft (rnNodeIface γ) := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hinv⟩
  iunfold rnIsNode at Hnode
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %Hn, -, -, -, -, -, -⟩
  obtain ⟨Hraft, -, -⟩ := Hn
  ihave #Hnode' : isNode γ.nl E.γr.raft.raft.cl srvClusterN γ.id $$ []
  · rw [Hraft]; iexact Hnode
  ihave %Hdup : ⌜E.γr.raft.raft.cl.dup = false⌝ $$ []
  · ihave #Hcl := Hinv
    iunfold srvRaftLogInv at Hcl
    icases Hcl with ⟨-, #Hcl, -⟩
    iunfold srvClusterOk at Hcl
    icases Hcl with ⟨-, -, -, -, %H, -⟩
    ipureintro; exact H
  iunfold raftPropose
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hinv
  isplitr
  · iapply srvPropWits_of E.γr.raft $$ Hinv
  iintro !> %ctx %cd %dsl %data %Q %Φ !> ⟨#Hctx, #Hdata, %Hne, Harg, Hlc⟩ HΦ
  ihave #Hnctx := txnCtx_nodeCtx ctx cd $$ Hctx
  iunfold srvPropArg at Harg
  icases Harg with ⟨Hfr, Hau, #HQinv⟩
  -- (2026-10-27) the proposal registered with the server's registry, then proposed once with the
  -- node API's update
  imod srvProp_register E.γr.raft data Q ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hfr
    with ⟨%γQ, %γt, #Hel, #HQ, Htk⟩
  ihave Hapi := srvPropAu_api E.γr.raft data Q γQ γt Hne $$ Hinv Hel HQ Htk Hlc Hau
  wp_apply wp_Propose γ.nl E.γr.raft.raft.cl srvClusterN γ.id dsl data ctx cd $$ [Hapi]
    as %err #Herr
  · iframe #
    rw [Hdup]
    iexact Hapi
  iapply HΦ
  isplitr
  · iunfold srvPropRes
    isplitr
    · iunfold srvDeposited
      iexists (γQ, γt)
      iexact Hel
    iunfold srvIsProp
    iexists γQ, γt
    iframe Hel HQ HQinv
  · ihave #Herr' := propErrS_propErr _ _ _ cd err $$ Herr
    iapply applyErrIs_of_propErr cd err $$ Hpkg Herr'

/-- **The node meets `raftApplyCC`** (D43 M3; 2026-10-27: over the node API; 2026-10-30, the
repair: `node.ApplyConfChange.spec`, the decision the cluster's rule's by `confPolicy_decide`
(`srvClusterOk`'s policy, the committed log delivered, `deliveredLogLb_committed`, the membership
at `k` from the view's by `nodeConfig_confAt` and `confAt_noConf`), the conf entries between the
view and `k` none, `skippedIn_noConf`; the stopped answer refuted by the running token's share,
`nodeRunning_stopped`; until then `node.ApplyConfChange.dynamicSpec` at the decoder): with the
driver's view and the committed log delivered; its answer is the view at `⟨k + 1, m'⟩`. -/
theorem raftApplyCC_of_isNode (γ : RNNames)
    (wp_ApplyConfChange : letI := srvStor (GF := GF) γ.node;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rnIsNode γ ∗ srvClusterOk γ.srv ⊢
      raftApplyCC γ.srv γ.nl (rnNodeIface γ) := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hpraft, #Hnode, #Hcl⟩
  iunfold rnIsNode at Hnode
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨#Hisc, #Hpol, -⟩
  iunfold raftApplyCC
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  iintro !> %c %cm %l %v %k %e %m' %q %Hpre %Φ !> ⟨Hc, Hcfg, #Hdl, Hrun⟩ HΦ
  obtain ⟨h1, h2, h3, h4, o', h5, h6, h7, -⟩ := Hpre
  have hk : k ≤ l.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 h2).1
  ihave ⟨Hcfg, #Hca⟩ := nodeConfig_confAt γ.nl γ.node.cl srvClusterN v $$ Hcfg
  ihave #Hcom := deliveredLogLb_committed γ.nl γ.node.cl srvClusterN l $$ Hdl
  ihave #Hck : confAt γ.node.cl k v.membership $$ []
  · iapply confAt_noConf γ.node.cl l v.applied k v.membership h4 h1 hk
    iframe Hcom Hca
  have hstep : (ConfDecision.ofRule (γ.node.rule (List.take k l) v.membership e)).step
      v.membership = some m' := by
    rw [h5]; exact h6
  imod confPolicy_decide γ.node.cl srvClusterN srvConfN ⊤ γ.node.rule l k e v.membership m'
      h2 h3 (fun _ _ => CoPset.mem_full) hstep $$ [Hisc Hpol Hcom Hck] with #Hdec
  · iframe Hisc Hpol Hcom Hck
  ihave #Hdec' : confDecided γ.node.cl k (ConfDecision.apply o') $$ []
  · rw [show ConfDecision.apply o' = ConfDecision.ofRule (γ.node.rule (List.take k l)
      v.membership e) by rw [h5]; rfl]
    iexact Hdec
  ihave #Hsk := skippedIn_noConf γ.node.cl l v.applied k h4
  wp_apply (wp_ApplyConfChange γ.nl γ.node.cl srvClusterN γ.id c (.v1 cm) o' l k e v m'
      h1 h2 h3 h6 h7) $$ [Hc Hcfg] as %csp %cs Hres
  · iframe #
    iframe Hc Hcfg
  icases Hres with (⟨Hcs, Hcfg, %Hcsi⟩ | ⟨%-, #Hst⟩)
  · iapply HΦ
    iframe Hcfg Hrun
    iexists cs
    iframe Hcs
    ipureintro; exact Hcsi
  · iexfalso
    iapply nodeRunning_stopped γ.nl γ.node.cl srvClusterN q $$ [Hrun Hst]
    iframe Hrun Hst

/-- **The node meets `isRaftNodeIfc`** (2026-10-27: over the node API; 2026-10-30, the repair:
raft's unified specs, `Stop` too, so no premise): `ApplyConfChange` (`raftApplyCC_of_isNode`),
`Ready` from `node.Ready.spec`, `Advance` from `node.Advance.spec` (at the driver's view after
the batch, its conf entries skipped from the view's index, `skippedIn_noConf`; the append receipt
`advReceipt`'s at the frozen prefix `[]`; the stopped answer refuted by the loop's half), `Tick`
from `node.Tick.spec`, `Stop` from `node.Stop.spec`, `ReadIndex` from `node.ReadIndex.spec`, the
context committed to the read's update after the committed log the caller's bound names
(`srvReadCtx_commit`, by the context's fresh token); the registration `E.RQ id n Qr` is the
context's (`srvRQ`), the error `applyErrIs_of_nodeErr`'s (through `nodeErrS_nodeErr`). -/
theorem isRaftNodeIfc_of_isNode (E : RNEnv GF) (γ : RNNames) (s : Loc) (issued : GName)
    (wp_Ready : letI := srvStor (GF := GF) γ.node; node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : letI := srvStor (GF := GF) γ.node;
      node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : letI := srvStor (GF := GF) γ.node; node.Tick.spec (GF := GF) (hG := hG))
    (wp_Stop : letI := srvStor (GF := GF) γ.node; node.Stop.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : letI := srvStor (GF := GF) γ.node;
      node.ReadIndex.spec (GF := GF) (hG := hG))
    (wp_ApplyConfChange : letI := srvStor (GF := GF) γ.node;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnIsNode γ ∗ srvCommittedInv s E.γr ∗
      rnMemStorReg γ ∗ srvRdCtxInv E.γr.raft issued ⊢
      isRaftNodeIfc E γ (rnNodeIface γ) := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hpkg, #Henv, #Hnode, #Hcinv, #Hreg, #Hci⟩
  ihave #Hnode0 := Hnode
  iunfold rnIsNode at Hnode0
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨%HT, %Hn, -, #Hinv, -, -, -, %HRQ⟩
  obtain ⟨Hraft, Hpre, Hai0⟩ := Hn
  ihave #Hcl : srvClusterOk γ.srv $$ []
  · iunfold srvRaftLogInv at Hinv
    icases Hinv with ⟨-, #H, -⟩
    rw [srvClusterOk_congr γ.srv E.γr.raft (by rw [Hraft])]
    iexact H
  ihave #Hisc : isCluster γ.node.cl srvClusterN $$ []
  · iunfold srvClusterOk at Hcl
    icases Hcl with ⟨#H, -⟩
    iexact H
  iunfold isRaftNodeIfc
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply raftApplyCC_of_isNode γ wp_ApplyConfChange
    iframe Hpraft Hnode Hcl
  isplitr
  · -- `Ready`
    iintro !> %Φ !> - HΦ
    wp_apply wp_Ready γ.node.cl srvClusterN γ.id γ.nl $$ [] as %ch #Hch
    · iframe #
    iapply HΦ
    iexact Hch
  isplitr
  · -- `Advance`, after a `Ready` without a snapshot
    iintro !> %d %ce %es %p %Φ !> ⟨Hbusy, Hcv, Hrcpt, Hrun⟩ HΦ
    iunfold rnBusyN at Hbusy
    iunfold rnAdvReceipt at Hrcpt
    iunfold rnCfgAt at Hcv
    iunfold srvCfgView at Hcv
    icases Hcv with ⟨%v, Hcfg, %Hok⟩
    have Hnc : NoConfChangeIn (srvLE γ.srv (d ++ ce)) v.applied (srvLE γ.srv (d ++ ce)).length := by
      have h := Hok.2.1
      simp only [srvLE, List.length_map] at h ⊢
      exact h
    ihave #Hsk := skippedIn_noConf γ.node.cl (srvLE γ.srv (d ++ ce)) v.applied _ Hnc
    wp_apply (wp_Advance γ.nl γ.node.cl srvClusterN γ.id
        ⟨memStorIface γ.ms, srvLE γ.srv (d ++ ce), p, some (es.map EntryModel.toM, none)⟩
        (es.map EntryModel.toM) none v rfl (fun _ h => by cases h)) $$ [Hbusy Hrcpt Hcfg]
      as Hres
    · iframe #
      iframe Hbusy Hrcpt Hcfg
    icases Hres with (⟨Hdrv, #Hal, Hcfg⟩ | ⟨#Hst, -⟩)
    · iapply HΦ
      iframe Hrun
      isplitl [Hdrv Hcfg]
      · iunfold rnDrv
        isplitl [Hdrv]
        · iExactEq Hdrv; rfl
        iunfold rnCfgAt
        iunfold srvCfgView
        iexists v
        iframe Hcfg
        ipureintro; exact Hok
      iapply nodeAppliedLb_mono γ.node.cl γ.id _ _ (by simp [srvLE]) $$ Hal
    · iexfalso
      iapply nodeRunning_stopped γ.nl γ.node.cl srvClusterN _ $$ [Hrun Hst]
      iframe Hrun Hst
  isplitr
  · -- SNAPSHOT-SORRY: the snapshot `Advance` clause (`node.Advance.spec` at `L = some l`:
    -- `snapReceipt`, `snapshotCert`; the view at the snapshot from `confAt`/`confStateIs`, D3)
    sorry
  isplitr
  · -- `Tick`
    iintro !> %Φ !> - HΦ
    wp_apply wp_Tick γ.nl γ.node.cl srvClusterN γ.id $$ []
    · iframe #
    iapply HΦ
    itrivial
  isplitr
  · -- `Stop`
    iintro !> %Φ !> Hrun HΦ
    wp_apply wp_Stop γ.nl γ.node.cl srvClusterN γ.id $$ [Hrun] as #Hst
    · iframe #; iframe Hrun
    iapply HΦ
    iexact Hst
  isplitr
  rotate_left
  · iexact Hnode0
  · -- `ReadIndex`
    iintro !> %ctx %cd %sl %id %n %Qr %Φ !> ⟨#Hctx, #Hsl, #Hcal, #Hau, Hfresh⟩ HΦ
    imod committedAtLeast_log s E.γr n ⊤ CoPset.subseteq_top $$ Hcinv Hcal with ⟨%L, #HL, %HnL⟩
    ihave #HL0 : isCommittedLogLb E.γr.raft.raft.cl (srvLE E.γr.raft L) $$ []
    · iunfold srvRLogLb at HL; icases HL with ⟨#H, -⟩; iexact H
    imod srvReadCtx_commit E.γr.raft issued (beBytes id) Qr (srvLE E.γr.raft L) ⊤
        (fun _ _ => CoPset.mem_full) $$ Hinv Hci Hfresh Hau HL0 with ⟨#Hrc, #Haft⟩
    ihave #Hnctx : nodeCtx ctx cd $$ []
    · iunfold nodeCtx
      iright
      iexact Hctx
    ihave #Hrc' : isReadCtx γ.node.cl srvClusterN (beBytes id) (srvReadQ E.γr.raft Qr) $$ []
    · rw [← Hraft]; iexact Hrc
    wp_apply wp_ReadIndex γ.nl γ.node.cl srvClusterN γ.id sl (beBytes id)
      (srvReadQ E.γr.raft Qr) ctx cd $$ [] as %err #Herr
    · iframe #
    iapply HΦ
    isplitr
    · ihave #Herr' := nodeErrS_nodeErr _ _ _ cd err $$ Herr
      iapply applyErrIs_of_nodeErr cd err $$ Hpkg Herr'
    · iintro %_
      rw [HRQ]
      iunfold srvRQ
      iintro !>
      iexists srvLE E.γr.raft L
      iframe Hrc Haft
      ipureintro
      rw [srvLE_length, Hpre]
      omega

/-- **The node meets `rnStepIfc`** (D21 M2; 2026-10-27: the node API's `node.Step`,
`ReportUnreachable`, `ReportSnapshot`). -/
theorem rnStepIfc_of_isNode (γ : RNNames)
    (wp_Step : letI := srvStor (GF := GF) γ.node; node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : letI := srvStor (GF := GF) γ.node;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : letI := srvStor (GF := GF) γ.node;
      node.ReportSnapshot.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ rnIsNode γ ⊢
      rnStepIfc γ (rnNodeIface γ) := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨#Hpkg, #Hnode⟩
  iunfold rnIsNode at Hnode
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold rnStepIfc
  iexists ⟨go.GoType.PointerType node.ty, #γ.nl⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %ml %Φ !> ⟨#Hctx, Hst⟩ HΦ
    wp_apply wp_Step γ.nl γ.node.cl srvClusterN γ.id ml ctx cd $$ [Hst] as %err #Herr
    · iframe #; iframe Hst
    iapply HΦ
    iapply nodeErrS_nodeErr $$ Herr
  isplitr
  · iintro !> %x %Φ !> - HΦ
    wp_apply wp_ReportUnreachable γ.nl γ.node.cl srvClusterN γ.id x $$ []
    · iframe #
    iapply HΦ
    itrivial
  · iintro !> %x %st %Φ !> - HΦ
    wp_apply wp_ReportSnapshot γ.nl γ.node.cl srvClusterN γ.id x st $$ []
    · iframe #
    iapply HΦ
    itrivial

end bridge

end EtcdGrove
end Perennial
