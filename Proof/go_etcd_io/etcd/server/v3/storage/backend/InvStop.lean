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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
     (ghostVar γ.cls (1 : Qp).half () ∗ (dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∨ runTok γ))))

instance stopInv_persistent (γ : BNames) (sc : GoChan) (γsc : ChanNames) :
    Persistent (stopInv (GF := GF) γ sc γsc) := by
  unfold stopInv; infer_instance

/-- (2026-11-04, R2b-3c) **What closing `donec` announces: the stop's escrow** (persistent; until then
`True`): bbolt's database as the stopped batch transaction left it, with the lock's ghost shares
and client resources `W ∗ Pk` (`bDBOut`, R2b-3c part 2), or `Close`'s half of the close right once
it took them. `run` allocates it as it closes `donec`. -/
def bDoneEsc (γ : BNames) (P : BParams) (W Pk : IProp GF) : IProp GF :=
  inv (bN.@"dbesc") iprop(bDBOut γ P W Pk ∨ ghostVar γ.cls (1 : Qp).half ())

instance bDoneEsc_persistent (γ : BNames) (P : BParams) (W Pk : IProp GF) :
    Persistent (bDoneEsc (GF := GF) γ P W Pk) := by
  unfold bDoneEsc; infer_instance

/-- The stop channels of the backend `b`, with their ghost names (R2b-3c part 2: at the parameters
and the batch lock's client resources of `isBackend`, which `donec`'s escrow returns). -/
def isStopChansAt (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (sc dc : GoChan)
    (γsc γdc : ChanNames) : IProp GF :=
  iprop(bF go!"stopc" b ↦□ sc ∗ bF go!"donec" b ↦□ dc ∗
    ownBroadcastChan sc γsc (stopQ γ) .Unknown ∗ ownBroadcastChan dc γdc (bDoneEsc γ P W Pk) .Unknown ∗
    stopInv γ sc γsc)

instance isStopChansAt_persistent (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc)
    (sc dc : GoChan) (γsc γdc : ChanNames) :
    Persistent (isStopChansAt (GF := GF) γ P W Pk b sc dc γsc γdc) := by
  unfold isStopChansAt stopInv; infer_instance

/-- The stop channels of the backend `b` (persistent; `New` gives it with `isBackend γ P W Pk b`). -/
def isStopChans (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(∃ (sc dc : GoChan) (γsc γdc : ChanNames), isStopChansAt γ P W Pk b sc dc γsc γdc)

instance isStopChans_persistent (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    Persistent (isStopChans (GF := GF) γ P W Pk b) := by
  unfold isStopChans; infer_instance

/-- (2026-11-04, R2b-3c part 2) **The backend `b` with its stop channels, at some client resources**
(persistent): what `Close` takes besides the open token, the batch lock's resources `W ∗ Pk`
hidden. A client that only closes the backend (the snapshot path's old backend) keeps this; one that
needs what `Close` gives back (`bStopView`) keeps its own `W`, `Pk`. -/
def isStopChansE (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ W Pk : IProp GF, isBackend γ P W Pk b ∗ isStopChans γ P W Pk b)

instance isStopChansE_persistent (γ : BNames) (P : BParams) (b : Loc) :
    Persistent (isStopChansE (GF := GF) γ P b) := by
  unfold isStopChansE; infer_instance

/-- `isStopChansE` from a backend and its stop channels. -/
theorem isStopChansE_intro (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isBackend (GF := GF) γ P W Pk b ∗ isStopChans γ P W Pk b ⊢ isStopChansE γ P b := by
  unfold isStopChansE
  iintro ⟨#Hb, #Hs⟩
  iexists W, Pk
  iframe #

/-- (2026-11-04, R2b-3c part 2) **What `Close` hands back of the stopped batch lock, at the file's data
`D`**: its client resources `W ∗ Pk`, and its ghost shares at `D` -- the readers' view quarter
(`viewAt`) and the lock's halves of the non-hook buckets' physical view (`pvHalf`), the hook's own
keys (`hkOwn`), the tracked buckets (`rbOwn`) and the compaction keys' values (`ckHalf`): what
`backend.Snapshot.spec`'s observation takes, so that a client's own halves (by agreement) and its
observation of `W ∗ Pk` tell what `D` holds. -/
def bStopView (γ : BNames) (P : BParams) (W Pk : IProp GF) (D : Data) : IProp GF :=
  iprop(W ∗ Pk ∗ viewAt γ (sData P D) ∗ pvHalf γ (sData P D) ∗ hkOwn γ (hkData P D) ∗
    rbOwn γ (rbData P D) ∗ ckHalf γ (fkVals D))

/-- The stopped lock's ghost shares at `C` are `bStopView`'s. -/
theorem bStopG_view (γ : BNames) (P : BParams) (W Pk : IProp GF) (C : Data) :
    bStopG (GF := GF) γ P C ∗ W ∗ Pk ⊢ bStopView γ P W Pk C := by
  unfold bStopG trkHalf bStopView viewAt pvHalf hkOwn ckHalf
  iintro ⟨⟨Hv, Hhk, Hrb, Hpv, Hck⟩, HW, HPk⟩
  ihave Hrb := rbSide_rbOwn γ P _ $$ Hrb
  iframe

/-- `Close`'s step: the right to close `stopc`, for the clients' whole open token. -/
theorem stop_take (γ : BNames) (sc : GoChan) (γsc : ChanNames) :
    stopInv (GF := GF) γ sc γsc ∗ bOpen γ 1 ⊢
      |={⊤}=> ▷ ownBroadcastChan sc γsc (stopQ γ) .Pending ∗ stopQ γ ∗
        -- (2026-11-04, R2b-3c) half the close right, `Close`'s claim on `donec`'s escrow
        ghostVar γ.cls (1 : Qp).half () := by
  iintro ⟨#Hinv, Ho⟩
  unfold bOpen
  icases Ho with ⟨Ho, Hcls⟩
  unfold stopInv
  iinv Hinv with Hi Hclose
  icases Hi with (⟨Hpend, >Hsdn⟩ | ⟨>Hcls', -⟩)
  · imod dghostVar_update true γ.sdn false $$ Hsdn with Hsdn
    imod dghostVar_persist γ.sdn 1 true $$ Hsdn with #Hsdn
    ihave ⟨Hcls, Hclaim⟩ : iprop(ghostVar γ.cls (1 : Qp).half () ∗ ghostVar γ.cls (1 : Qp).half ())
      $$ [Hcls]
    · iapply ghostVar_split γ.cls () (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half]; iexact Hcls
    imod Hclose $$ [Hcls Ho] with -
    · inext
      iright
      iframe Hcls
      ileft
      iexact Ho
    imodintro
    iframe Hpend Hclaim
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

/-- (2026-11-04, R2b-3c) **`Close` takes bbolt's database out of `donec`'s escrow**, with its half
of the close right (`stop_take`'s): the other alternative would make three halves, the stop
invariant keeping one once `stopc` closed (`stopQ`). -/
theorem bDoneEsc_take (γ : BNames) (P : BParams) (W Pk : IProp GF) (sc : GoChan) (γsc : ChanNames) :
    ⊢ bDoneEsc (GF := GF) γ P W Pk -∗ stopInv γ sc γsc -∗ stopQ γ -∗ ghostVar γ.cls (1 : Qp).half () -∗
      £ 1 -∗ £ 1 ={⊤}=∗ bDBOut γ P W Pk := by
  iintro #Hesc #Hinv #Hq Hclaim Hlc1 Hlc2
  iunfold bDoneEsc at Hesc
  iinv Hesc with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑(bN.@"dbesc")) $$ Hlc1 Hi with Hi
  icases Hi with (Hout | Hcl2)
  rotate_left
  · unfold stopInv
    iinv Hinv with Hs Hsclose
    imod lc_fupd_elim_later (E := (⊤ \ ↑(bN.@"dbesc")) \ ↑(bN.@"stop")) $$ Hlc2 Hs with Hs
    icases Hs with (⟨-, Hsdn⟩ | ⟨Hcl3, -⟩)
    · iexfalso
      unfold stopQ
      icombine Hsdn Hq gives %Hc
      exact absurd Hc.2 (by decide)
    · iexfalso
      icombine Hclaim Hcl2 as H12
      icombine H12 Hcl3 gives % ⟨Hv, -⟩
      exfalso; revert Hv; grind
  imod Hclose $$ [Hclaim] with -
  · inext; iright; iexact Hclaim
  imodintro
  iexact Hout

end preds

end backend
end EtcdGrove
end Perennial
