/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2b/Chan.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2b: `len(ch)` of a channel whose logical state one owns

Perennial's `wp_Len` returns a length bounded by the capacity only (the channel may be shared).
`handlePropose` reads `len(ProposeChan)` holding the channel's `ownChan` (`proposeOwn`: the lock's
holder is its only user): the length is the buffer's.
-/
module

public import Perennial.Golang.Theory.Chan.AuSpec.ChanAuSend
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.unusedSectionVars false

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial.gryff.replica2.h2b


open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model
open github_com.goose_lang.primitive (Mutex.wp_Lock Mutex.wp_Unlock)

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true

set_option maxHeartbeats 800000 in
/-- `ch.Len()` with the channel's logical state owned (buffered, contents `vs`). -/
theorem wp_Len_own (ch : Loc) (γ : ChanNames) (vs : List V) :
    {{ isChan (GF := GF) ch γ V ∗ ownChan γ V (.Buffered vs) }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel.ty t) @!! go!"Len")) (Val #()))
    {{ RET #(W64 vs.length); ownChan γ V (.Buffered vs) }} := by
  wp_start as ⟨#His, Hown⟩
  wp_auto
  ihave %Hnn := isChan_not_null _ _ _ $$ His
  rw [isChan_unseal]
  iNamed His
  wp_if_destruct
  · exact absurd rfl Hnn
  rw [isLock_eq_is_Mutex] at *
  wp_apply Mutex.wp_Lock $$ [$lock] as ⟨Hlock, Hchan⟩
  iNamed Hchan
  cases s with
  | Buffered buffer =>
    iNamed phys
    simp only [chanLogical]
    ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hown
    injection Heq with Heq
    subst Heq
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ slice
    ihave %Hsz := ownChan_buffer_size _ _ _ $$ offer
    wp_apply Mutex.wp_Unlock $$ [$lock $Hlock state buffer slice slice_cap offer]
    · iapply chanInvInner_intro _ _ _ (ChanPhysState.Buffered buffer)
      simp only [chanPhys, chanLogical]
      iframe
    have : W64 (buffer.length : Int) = slice_val.len := by
      rw [Hlen.1]; have := Hlen.2; simp only [sint.nat]; word
    rw [this]
    iapply HΦ
    iframe
  | Idle =>
    simp only [chanLogical]
    icases offer with ⟨%_, -, -, Ho⟩
    ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
    cases Heq
  | SndWait v =>
    simp only [chanLogical]
    icases offer with ⟨%_, %_, %_, -, -, -, -, Ho⟩
    ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
    cases Heq
  | RcvWait =>
    simp only [chanLogical]
    icases offer with ⟨%_, %_, -, -, -, -, Ho⟩
    ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
    cases Heq
  | SndDone v =>
    simp only [chanLogical]
    icases offer with ⟨%_, %_, -, -, -, Ho⟩
    ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
    cases Heq
  | RcvDone =>
    simp only [chanLogical]
    icases offer with ⟨%_, %_, %_, %_, -, -, -, Ho⟩
    ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
    cases Heq
  | Closed buffer =>
    cases buffer with
    | nil =>
      simp only [chanLogical]
      icases offer with ⟨Ho, -⟩
      ihave %Heq := ownChan_agree _ _ _ _ $$ Ho Hown
      cases Heq
    | cons x rest =>
      simp only [chanLogical]
      ihave %Heq := ownChan_agree _ _ _ _ $$ offer Hown
      cases Heq

/-- `<-ch` with the channel's logical state owned (buffered, `v` first). -/
theorem wp_receive_own (ch : Loc) (γ : ChanNames) (v : V) (rest : List V) :
    {{ isChan (GF := GF) ch γ V ∗ ownChan γ V (.Buffered (v :: rest)) }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #v #true); ownChan γ V (.Buffered rest) }} := by
  iintro %Φ ⟨#Hch, Hown⟩ HΦ
  iapply chan.wp_receive ch γ $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  unfold recvAu
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered (v :: rest)
  iframe Hown
  dsimp only
  iintro Hoc
  imod Hmask with -
  imodintro
  iapply HΦ $$ Hoc

end

end Perennial.gryff.replica2.h2b
