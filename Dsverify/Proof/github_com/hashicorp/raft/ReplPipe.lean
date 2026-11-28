/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/ReplPipe.lean (241f27e).
-/
/-
Pipeline mode's channels (stage 2, `pipelineReplicate`/`pipelineDecode`).

* `finChan γf ch R`: `finishCh`, an unbuffered `chan struct{}` on which nothing is sent, closed once
  by the decoder (`finCloser`, giving `R`: the writer's half of `nextIndex`), received by
  `pipelineReplicate` any number of times: the first receive with the token `finTok` takes `R`
  and a persistent "closed" witness `finDone`; a receive with `finDone` completes at once.
* `fin_alloc`, `fin_close_au`, `fin_rcv_tok_au`, `fin_rcv_done_au`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def finN : Namespace := raftN.@"finish"

/-- The ghost names of a finish channel. -/
structure FinNames where
  ch : ChanNames
  done : GName
  tok : GName

/-- The receiver's token before it has received the close (exclusive). -/
def finTok (γf : FinNames) : IProp GF := dghostVar γf.tok (.own 1) false

/-- The closer's right (the decoder's). -/
def finCloser (γf : FinNames) : IProp GF := dghostVar γf.done (.own (1 : Qp).half) false

/-- The channel was closed (persistent). -/
def finDone (γf : FinNames) : IProp GF := dghostVar γf.done .discard true

instance finDone_persistent γf : Persistent (finDone (GF := GF) γf) := by
  unfold finDone; infer_instance

/-- The finish channel's invariant: open (and idle or with a waiting receiver), or closed with
`R` until the receiver takes it (leaving its token). -/
def finInv (γf : FinNames) (R : IProp GF) : IProp GF :=
  iprop(∃ st : ChanState Unit, ownChan γf.ch Unit st ∗
    (match st with
      | .Idle | .RcvPending => dghostVar γf.done (.own (1 : Qp).half) false
      | .Closed [] => finDone γf ∗ (R ∨ finTok γf)
      | _ => iprop(False)))

/-- **A finish channel** (persistent). -/
def finChan (γf : FinNames) (ch : Loc) (R : IProp GF) : IProp GF :=
  iprop(isChan ch γf.ch Unit ∗ inv finN (finInv γf R))

instance finChan_persistent γf ch R : Persistent (finChan (GF := GF) γf ch R) := by
  unfold finChan; infer_instance

theorem finTok_excl (γf : FinNames) : finTok (GF := GF) γf ∗ finTok γf ⊢ False := by
  unfold finTok
  iintro ⟨H1, H2⟩
  ihave ⟨%Hv, -⟩ := dghostVar_valid_2 _ _ _ _ _ $$ H1 H2
  exact absurd (DFrac.valid_own_op Hv) (by have : (1 : Qp).val = 1 := rfl; grind)

theorem finDone_closer (γf : FinNames) : finDone (GF := GF) γf ∗ finCloser γf ⊢ False := by
  unfold finDone finCloser
  iintro ⟨H1, H2⟩
  ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ H1 H2
  cases Hbad

/-- Allocation from a fresh unbuffered channel. -/
theorem fin_alloc (ch : Loc) (γc : ChanNames) (R : IProp GF) :
    ⊢ isChan ch γc Unit -∗ ownChan γc Unit .Idle ={⊤}=∗
      ∃ γf : FinNames, ⌜γf.ch = γc⌝ ∗ finChan γf ch R ∗ finCloser γf ∗ finTok γf := by
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%γd, Hd⟩
  icases dghostVar_halves _ _ $$ Hd with ⟨HdA, HdB⟩
  imod dghostVar_alloc false with ⟨%γt, Ht⟩
  iexists ⟨γc, γd, γt⟩
  unfold finChan finCloser finTok
  imod inv_alloc finN ⊤ (finInv ⟨γc, γd, γt⟩ R) $$ [Hoc HdA] with #Hinv
  · inext
    unfold finInv
    iexists .Idle
    dsimp only
    iframe
  imodintro
  isplitr; · ipureintro; rfl
  iframe; iframe #

/-- The decoder's close: gives `R`. -/
theorem fin_close_au (γf : FinNames) (ch : Loc) (R : IProp GF) (Φ : IProp GF) :
    ⊢ finChan γf ch R -∗ £ 1 -∗ finCloser γf -∗ R -∗ ▷ Φ -∗ closeAu γf.ch Unit Φ := by
  unfold finChan closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc Hown HR HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑finN) $$ Hlc Hi with Hi
  unfold finInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    unfold finCloser
    imod dghostVar_update_halves true _ _ _ $$ Hown Hs with ⟨Hown, -⟩
    imod dghostVar_persist _ _ _ $$ Hown with #Hown
    imod Hclose $$ [Hch HR] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      unfold finDone
      iframe #
      ileft; iexact HR
    imodintro
    iexact HΦ
  case Closed.nil =>
    icases Hs with ⟨#Hs, -⟩
    iexfalso
    iapply finDone_closer $$ [Hs Hown]
    iframe; iframe #
  all_goals first | itrivial | (iexfalso; iexact Hs)

set_option maxHeartbeats 800000 in
/-- The receiver's first receive (it holds the token): it completes only at the close and takes
`R` and the closed witness. -/
theorem fin_rcv_tok_au (γf : FinNames) (ch : Loc) (R : IProp GF) (Φ : Unit → Bool → IProp GF) :
    ⊢ finChan γf ch R -∗ finTok γf -∗
      ▷ (∀ v : Unit, R -∗ finDone γf -∗ Φ v false) -∗ recvAu γf.ch Unit Φ := by
  unfold finChan recvAu
  iintro ⟨#Hchan, #Hinv⟩ Htok HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold finInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .RcvPending; dsimp only; iframe
    imodintro
    unfold recvNestedAu
    iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%st, Hch, Hs⟩
    iexists st
    iframe Hch
    rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case Closed.nil =>
      iintro Hch
      icases Hs with ⟨#Hd, (HR | Htok2)⟩
      · imod Hmask with -
        imod Hclose $$ [Hch Htok] with -
        · inext; iexists .Closed []; dsimp only; iframe Hch; iframe #; iright; iexact Htok
        imodintro
        iapply HΦ $$ HR Hd
      · iexfalso; iapply finTok_excl $$ [Htok Htok2]; iframe
    all_goals first | itrivial | (iexfalso; iexact Hs)
  case Closed.nil =>
    iintro Hch
    icases Hs with ⟨#Hd, (HR | Htok2)⟩
    · imod Hmask with -
      imod Hclose $$ [Hch Htok] with -
      · inext; iexists .Closed []; dsimp only; iframe Hch; iframe #; iright; iexact Htok
      imodintro
      iapply HΦ $$ HR Hd
    · iexfalso; iapply finTok_excl $$ [Htok Htok2]; iframe
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- A receive after the close (the receiver holds the closed witness): it completes at once. -/
theorem fin_rcv_done_au (γf : FinNames) (ch : Loc) (R : IProp GF) (Φ : Unit → Bool → IProp GF) :
    ⊢ finChan γf ch R -∗ finDone γf -∗ ▷ (∀ v : Unit, Φ v false) -∗ recvAu γf.ch Unit Φ := by
  unfold finChan recvAu
  iintro ⟨#Hchan, #Hinv⟩ #Hd HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold finInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iexfalso; iapply finDone_closer $$ [Hs]; unfold finCloser; iframe; iframe #
  case RcvPending =>
    iexfalso; iapply finDone_closer $$ [Hs]; unfold finCloser; iframe; iframe #
  case Closed.nil =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .Closed []; dsimp only; iframe
    imodintro
    iapply HΦ
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- The decoder's `close(finishCh)`. -/
theorem wp_fin_close (γf : FinNames) (ch : Loc) (R : IProp GF) {ct : go.GoType} {dir : go.ChanDir}
    [ct ↓u go.ChannelType dir (go.GoType.StructType [])] :
    {{ finChan γf ch R ∗ finCloser γf ∗ R }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hfin, Hcl, HR⟩ HΦ
  ihave #Hch : isChan ch γf.ch Unit $$ [Hfin]
  · unfold finChan; icases Hfin with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γf.ch $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply fin_close_au γf ch R (Φ #()) $$ Hfin Hlc1 Hcl HR
  inext
  iapply HΦ
  itrivial

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- A valid request's body (the pipeline's futures carry `aeReq`; `updateLastAppended` takes
`aeBody`). -/
theorem aeBody_of_aeReq (γ : GNames) (rq : AppendEntriesRequest) (snd : SID) (T prev pt : Nat)
    (ents : RLog) (lci : Nat) (ss : Snap) :
    aeReq (GF := GF) γ rq snd T prev pt ents lci ss ⊢ aeBody rq snd T prev pt ents lci := by
  unfold aeReq aeBody entPtrs
  iintro ⟨%h, #Hh, #Hl, #He, -, -⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  isplitr
  · ipureintro
    refine ⟨?_, h2, h3, h4⟩
    rw [← h1]; simp
  iframe #

end lemmas

end github_com.hashicorp.raft

end Perennial
