/-
An unbuffered channel used close-only (U10e of `notes/bbolt-proof-plan.md`; `DB.freepages`'
`ech`): nothing is ever sent, one receiver loops until the close, and the closer hands a resource
`R` (fixed at `make`) to the receiver. Perennial's channel specs (`isChan`, `chan.wp_receive`,
`chan.wp_close`) are stated for `HasLC.hasLC` only (their saved-prop offers need later credits),
and bbolt's specs are over any `hlc`; this is the pattern proved directly from the channel model
(`goose/model/channel`: a mutex over the state, the buffer and the offered value), with a lock
invariant of its own (no saved props): the state is idle, a pending receive (the receiver's
ghost flag set), or closed with the closer's token and `R` (or the receiver's token, once it took
`R`). A local stand-in for hlc-generic channel specs (a Perennial proposal).
-/
module

public import Perennial.Golang.Theory.Chan
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model
open github_com.goose_lang.primitive (isMutex isMutex_unseal isMutexDef ownMutex ownMutex_unseal
  ownMutexDef Mutex.wp_Lock Mutex.wp_Unlock)

/-- The ghost names of a close-only channel: the receiver's pending flag, the closer's token, the
receiver's token. -/
structure CCNames where
  p : GName
  c : GName
  r : GName

section cc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The lock invariant of a close-only channel. -/
def ccInv (ch : Loc) (γ : CCNames) (R : IProp GF) : IProp GF :=
  iprop(∃ s : ChanPhysState V, chanPhys ch V s ∗
    match s with
    | .Idle => ghostVar γ.p (1 : Qp).half false
    | .RcvWait => ghostVar γ.p (1 : Qp).half true
    | .Closed [] => ghostVar γ.p (1 : Qp).half false ∗ ghostVar γ.c 1 () ∗
        (R ∨ ghostVar γ.r 1 ())
    | _ => False)

/-- **A close-only channel** (persistent). -/
def isCC (ch : Loc) (γ : CCNames) (R : IProp GF) : IProp GF :=
  iprop(∃ mu : Loc, ch.[channel.Channel V, go!"mu"] ↦□ mu ∗ isMutex mu (ccInv (V := V) ch γ R) ∗
    ⌜ch ≠ chan.nil⌝)

instance isCC_persistent (ch : Loc) (γ : CCNames) (R : IProp GF) :
    Persistent (isCC (V := V) ch γ R) := by
  unfold isCC; infer_instance

/-- The receiver's token. -/
def ccRecv (γ : CCNames) : IProp GF :=
  iprop(ghostVar γ.p (1 : Qp).half false ∗ ghostVar γ.r 1 ())

/-- The closer's token. -/
def ccClose (γ : CCNames) : IProp GF := ghostVar γ.c 1 ()

set_option goose.wp.extras true

set_option maxHeartbeats 800000 in
theorem cc_wp_TryReceive (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccRecv γ }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel.ty t) @!! go!"TryReceive"))
        (Val #true))
    {{ (r : val), RET r; (⌜r = PairV (PairV #false #(zero_val V)) #true⌝ ∗ ccRecv γ) ∨
        (⌜r = PairV (PairV #true #(zero_val V)) #false⌝ ∗ R) }} := by
  wp_start as ⟨#Hcc, Hrv⟩
  unfold isCC
  icases Hcc with ⟨%mu, #Hmu, #Hlock, %Hnn⟩
  unfold ccRecv
  icases Hrv with ⟨Hp, Hr⟩
  chan_unfold_consts
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold ccInv at Hinv
  icases Hinv with ⟨%s, Hphys, Hs⟩
  cases s with
  | Idle =>
    iNamed Hphys
    wp_auto
    imod ghostVar_update_halves true γ.p false false $$ Hp Hs with ⟨Hp, Hs⟩
    wp_apply Mutex.wp_Unlock $$ [$Hlock $Hown state v slice slice_cap buffer Hs]
    · iunfold ccInv
      iexists ChanPhysState.RcvWait
      simp only [chanPhys]
      iframe
    wp_apply Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, Hinv⟩
    iunfold ccInv at Hinv
    icases Hinv with ⟨%s, Hphys, Hs⟩
    cases s with
    | RcvWait =>
      iNamed Hphys
      wp_auto
      imod ghostVar_update_halves false γ.p true true $$ Hp Hs with ⟨Hp, Hs⟩
      wp_apply Mutex.wp_Unlock $$ [$Hlock $Hown state v slice slice_cap buffer Hs]
      · iunfold ccInv
        iexists ChanPhysState.Idle
        simp only [chanPhys]
        iframe
      iapply HΦ
      ileft
      iframe
      ipureintro; rfl
    | Idle =>
      icombine Hp Hs gives %h
      exact absurd h.2 (by decide)
    | Closed b =>
      cases b with
      | nil =>
        icases Hs with ⟨Hs, -⟩
        icombine Hp Hs gives %h
        exact absurd h.2 (by decide)
      | cons x xs => iexfalso; iexact Hs
    | _ => iexfalso; iexact Hs
  | RcvWait =>
    icombine Hp Hs gives %h
    exact absurd h.2 (by decide)
  | Closed b =>
    cases b with
    | nil =>
      iNamed Hphys
      ihave %Hlen := ownSlice_len _ _ _ $$ slice
      icases Hs with ⟨Hs, Hc, HR⟩
      wp_auto
      wp_if_destruct
      · exfalso; simp at Hlen; revert Hif Hlen; word
      icases HR with (HR | Hr2)
      · wp_apply Mutex.wp_Unlock $$ [$Hlock $Hown state slice slice_cap buffer Hs Hc Hr]
        · iunfold ccInv
          iexists ChanPhysState.Closed []
          simp only [chanPhys]
          iframe
        iapply HΦ
        iright
        iframe
        ipureintro; rfl
      · icombine Hr Hr2 gives %h
        exfalso
        have h1 : ((1 : Qp) + 1).val ≤ 1 := h.1
        simp at h1
        grind
    | cons x xs => iexfalso; iexact Hs
  | _ => iexfalso; iexact Hs

/-- `c.Receive()` of a close-only channel: it sees the close, and `R`. -/
theorem cc_wp_Receive (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccRecv γ }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel.ty t) @!! go!"Receive")) (Val #()))
    {{ RET (PairV #(zero_val V) #false); R }} := by
  wp_start as ⟨#Hcc, Hrv⟩
  ihave %Hnn : ⌜ch ≠ chan.nil⌝ $$ [Hcc]
  · unfold isCC; icases Hcc with ⟨%mu, -, -, %H⟩; ipureintro; exact H
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave IH : (ccRecv (GF := GF) γ) $$ [Hrv]
  · iexact Hrv
  wp_for IH
  wp_apply cc_wp_TryReceive ch γ R $$ [Hcc IH] as %r H
  · unfold ccRecv; iframe; iframe #
  icases H with (⟨%Hr, Hrv⟩ | ⟨%Hr, HR⟩)
  · subst Hr
    wp_auto
    wp_for_post
    unfold ccRecv
    iframe
  · subst Hr
    wp_auto
    wp_for_post
    iapply HΦ $$ HR

/-- **The receive of a close-only channel** (`<-ch`, `chan.receive`): it sees the close, and
`R`. -/
theorem cc_wp_receive (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccRecv γ }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #(zero_val V) #false); R }} := by
  wp_start as ⟨#Hcc, Hrv⟩
  unfold chan.receive
  wp_call
  wp_apply cc_wp_Receive ch γ R $$ [Hcc Hrv] as HR
  · iframe; iframe #
  iapply HΦ $$ HR

set_option maxHeartbeats 800000 in
theorem cc_wp_tryClose (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccClose γ ∗ R }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel.ty t) @!! go!"tryClose"))
        (Val #()))
    {{ (b : Bool), RET #b; if b then True else ccClose γ ∗ R }} := by
  wp_start as ⟨#Hcc, Hc, HR⟩
  unfold isCC
  icases Hcc with ⟨%mu, #Hmu, #Hlock, %Hnn⟩
  unfold ccClose
  chan_unfold_consts
  wp_auto
  wp_apply Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold ccInv at Hinv
  icases Hinv with ⟨%s, Hphys, Hs⟩
  cases s with
  | Idle =>
    iNamed Hphys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$Hlock $Hown state slice slice_cap buffer Hs Hc HR]
    · iunfold ccInv
      iexists ChanPhysState.Closed []
      simp only [chanPhys]
      iframe
    iapply HΦ
    simp only [↓reduceIte]
    itrivial
  | RcvWait =>
    iNamed Hphys
    wp_auto
    wp_apply Mutex.wp_Unlock $$ [$Hlock $Hown state v slice slice_cap buffer Hs]
    · iunfold ccInv
      iexists ChanPhysState.RcvWait
      simp only [chanPhys]
      iframe
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  | Closed b =>
    cases b with
    | nil =>
      icases Hs with ⟨-, Hc2, -⟩
      icombine Hc Hc2 gives %h
      exfalso
      have h1 : ((1 : Qp) + 1).val ≤ 1 := h.1
      simp at h1
      grind
    | cons x xs => iexfalso; iexact Hs
  | _ => iexfalso; iexact Hs

/-- `c.Close()` of a close-only channel, by its closer: `R` goes to the receiver. -/
theorem cc_wp_Close (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccClose γ ∗ R }}
      (App (Val (ch @!! go.GoType.PointerType (channel.Channel.ty t) @!! go!"Close")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcc, Hc, HR⟩
  ihave %Hnn : ⌜ch ≠ chan.nil⌝ $$ [Hcc]
  · unfold isCC; icases Hcc with ⟨%mu, -, -, %H⟩; ipureintro; exact H
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave IH : (ccClose (GF := GF) γ ∗ R) $$ [Hc HR]
  · iframe
  wp_for IH
  icases IH with ⟨Hc, HR⟩
  wp_apply cc_wp_tryClose ch γ R $$ [Hcc Hc HR] as %b H
  · iframe; iframe #
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    simp only [val_bool_eq, Bool.not_false, Bool.not_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe
  · try wp_auto
    simp only [val_bool_eq, Bool.not_false, Bool.not_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    itrivial

/-- **`close(ch)` of a close-only channel**, by its closer: `R` goes to the receiver. -/
theorem cc_wp_close {ct : go.GoType} {dir : go.ChanDir} [ct ↓u go.ChannelType dir t]
    (ch : Loc) (γ : CCNames) (R : IProp GF) :
    {{ isCC (V := V) ch γ R ∗ ccClose γ ∗ R }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcc, Hc, HR⟩
  wp_apply cc_wp_Close ch γ R $$ [Hcc Hc HR]
  · iframe; iframe #
  iapply HΦ
  itrivial

set_option maxHeartbeats 800000 in
/-- **`make(chan T)` as a close-only channel** handing `R` from its closer to its receiver. -/
theorem cc_wp_NewChannel (R : IProp GF) :
    {{ (True : IProp GF) }}
      (App (Val #(functions channel.NewChannel [t])) (Val #(W64 0)))
    {{ (ch : Loc) (γ : CCNames), RET #ch; isCC (V := V) ch γ R ∗ ccRecv γ ∗ ccClose γ }} := by
  wp_start
  wp_auto
  try simp only [channel.idle, channel.buffered]
  try wp_auto
  iapply wp_fupd
  wp_apply wp_slice_make2 (V := V) $$ [] as %sl ⟨Hsl, Hslcap⟩
  · ipureintro; decide
  irename «$r0» => Hch
  generalize «$r0_ptr» = ch at *
  ihave %Hnot_null := typedPointsto_not_null _ _ _ $$ Hch
  iStructNamed Hch
  imod ghostVar_alloc false with ⟨%gp, Hp⟩
  icases ghostVar_halves _ _ $$ Hp with ⟨Hp1, Hp2⟩
  imod ghostVar_alloc () with ⟨%gc, Hc⟩
  imod ghostVar_alloc () with ⟨%gr, Hr⟩
  ipersist mu
  imod init_lock (ccInv (V := V) ch ⟨gp, gc, gr⟩ R) ⊤ «$v1_ptr» $$ «$v1» [Hsl Hslcap state buffer v Hp1]
    with #Hlock
  · inext
    unfold ccInv
    iexists (ChanPhysState.Idle (V := V))
    simp only [chanPhys]
    isplitl [Hsl Hslcap state buffer v]
    · iexists _, sl
      iframe
    · iexact Hp1
  imodintro
  iapply HΦ $$ %ch %(CCNames.mk gp gc gr)
  unfold isCC ccRecv ccClose
  iframe
  iexists «$v1_ptr»
  rw [isMutex_unseal]
  unfold isMutexDef
  iframe #
  ipureintro
  exact Hnot_null

/-- **`make(chan T)` as a close-only channel** handing `R` from its closer to its receiver. -/
theorem cc_wp_make1 {ct : go.GoType} {dir : go.ChanDir} [ct ↓u go.ChannelType dir t]
    (R : IProp GF) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [ct])) (Val #()))
    {{ (ch : Loc) (γ : CCNames), RET #ch; isCC (V := V) ch γ R ∗ ccRecv γ ∗ ccClose γ }} := by
  wp_start
  wp_func_call
  wp_apply cc_wp_NewChannel (V := V) R as %ch %γ H
  iapply HΦ $$ H

end cc

end bbolt
end EtcdGrove
end Perennial
