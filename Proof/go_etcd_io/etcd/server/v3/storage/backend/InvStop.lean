/-
The backend's stop protocol (`backend.go`'s `run` and `Close`): the channels `stopc` and `donec`
as broadcast channels (Perennial's `Chan/Idioms/Broadcast`, stated at `HasLC.hasLC`, so this
lives beside `isBackend` rather than in it: `isStopChans`). Lean-first (no Rocq counterpart).

- `Close`, with the clients' whole open token `bOpen γ 1` (the opn half and the close right
  `γ.cls`), takes from the stop invariant the right to close `stopc` (`Pending`, with `γ.sdn`
  at `false`), deposits the close right and the clients' opn half, marks `γ.sdn` as `true`
  (persistent: `stopQ`, what `stopc`'s closing broadcasts), and closes `stopc`. A second `Close`
  has no close right (all of `γ.cls` is in the invariant).
- `run`, having received from the closed `stopc` (`stopQ`: the invariant left `Pending`), swaps
  its exclusive `runTok` for the clients' half, which with its own quarter and the batch lock's
  makes the whole open token for `CommitAndStop`; it then closes `donec` (broadcasting
  nothing), on which `Close` waits.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- What closing `stopc` broadcasts: the stop invariant left its first state. -/
def stopQ (γ : BNames) : IProp GF := dghostVar γ.sdn DFrac.discard true

instance stopQ_persistent (γ : BNames) : Persistent (stopQ (GF := GF) γ) := by
  unfold stopQ; infer_instance

/-- The `run` goroutine's token, exchanged for the clients' half of the open token. -/
def runTok (γ : BNames) : IProp GF := ghostVar γ.stk 1 ()

instance runTok_timeless (γ : BNames) : Timeless (runTok (GF := GF) γ) := by
  unfold runTok; infer_instance

/-- The stop invariant: before `Close`, the right to close `stopc`; after, the close right and
the clients' half of the open token, until `run` takes the half (leaving its token). -/
def stopInv (γ : BNames) (sc : GoChan) (γsc : ChanNames) : IProp GF :=
  iprop(inv (bN.@"stop")
    iprop((ownBroadcastChan sc γsc (stopQ γ) .Pending ∗ dghostVar γ.sdn (DFrac.own 1) false) ∨
     (ghostVar γ.cls 1 () ∗ (dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∨ runTok γ))))

instance stopInv_persistent (γ : BNames) (sc : GoChan) (γsc : ChanNames) :
    Persistent (stopInv (GF := GF) γ sc γsc) := by
  unfold stopInv; infer_instance

/-- The stop channels of the backend `b`, with their ghost names. -/
def isStopChansAt (γ : BNames) (b : Loc) (sc dc : GoChan) (γsc γdc : ChanNames) : IProp GF :=
  iprop(bF go!"stopc" b ↦□ sc ∗ bF go!"donec" b ↦□ dc ∗
    ownBroadcastChan sc γsc (stopQ γ) .Unknown ∗ ownBroadcastChan dc γdc iprop(True) .Unknown ∗
    stopInv γ sc γsc)

instance isStopChansAt_persistent (γ : BNames) (b : Loc) (sc dc : GoChan) (γsc γdc : ChanNames) :
    Persistent (isStopChansAt (GF := GF) γ b sc dc γsc γdc) := by
  unfold isStopChansAt stopInv; infer_instance

/-- The stop channels of the backend `b` (persistent; `New` gives it with `isBackend`). -/
def isStopChans (γ : BNames) (b : Loc) : IProp GF :=
  iprop(∃ (sc dc : GoChan) (γsc γdc : ChanNames), isStopChansAt γ b sc dc γsc γdc)

instance isStopChans_persistent (γ : BNames) (b : Loc) :
    Persistent (isStopChans (GF := GF) γ b) := by
  unfold isStopChans; infer_instance

/-- `Close`'s step: the right to close `stopc`, for the clients' whole open token. -/
theorem stop_take (γ : BNames) (sc : GoChan) (γsc : ChanNames) :
    stopInv (GF := GF) γ sc γsc ∗ bOpen γ 1 ⊢
      |={⊤}=> ▷ ownBroadcastChan sc γsc (stopQ γ) .Pending ∗ stopQ γ := by
  iintro ⟨#Hinv, Ho⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  unfold stopInv
  iinv Hinv with Hi Hclose
  icases Hi with (⟨Hpend, >Hsdn⟩ | ⟨>Hcls', -⟩)
  · imod dghostVar_update true γ.sdn false $$ Hsdn with Hsdn
    imod dghostVar_persist γ.sdn 1 true $$ Hsdn with #Hsdn
    imod Hclose $$ [Hcls Ho] with -
    · inext
      iright
      iframe Hcls
      ileft
      iexact Ho
    imodintro
    iframe Hpend
    unfold stopQ
    iexact Hsdn
  · icombine Hcls Hcls' gives % ⟨Hv, -⟩
    exfalso
    revert Hv
    grind

/-- `run`'s step: once `stopc` closed, the clients' half of the open token for its token. -/
theorem stop_get (γ : BNames) (sc : GoChan) (γsc : ChanNames) :
    stopInv (GF := GF) γ sc γsc ∗ stopQ γ ∗ runTok γ ⊢
      |={⊤}=> dghostVar γ.opn (DFrac.own (1 : Qp).half) false := by
  iintro ⟨#Hinv, #Hq, Ht⟩
  unfold stopInv
  iinv Hinv with Hi Hclose
  icases Hi with (⟨-, >Hsdn⟩ | ⟨>Hcls, (>Ho | >Ht')⟩)
  · unfold stopQ
    icombine Hsdn Hq gives %Hc
    exact absurd Hc.2 (by decide)
  · imod Hclose $$ [Hcls Ht] with -
    · inext
      iright
      iframe Hcls
      iright
      iexact Ht
    imodintro
    iexact Ho
  · unfold runTok
    icombine Ht Ht' gives % ⟨Hv, -⟩
    exfalso
    revert Hv
    grind

end preds

end backend
end EtcdGrove
end Perennial
