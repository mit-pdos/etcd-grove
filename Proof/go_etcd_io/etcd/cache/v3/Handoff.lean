/-
A channel idiom (generic, in the style of Perennial's `Chan/Idioms`): a **handoff**, a buffered
channel on which the producer sends at most one value and then closes it, handing over a resource
at the first of the two. `Cache.watch`'s `applyErr`: the store-applying goroutine sends its error,
if any, and closes the channel; the watch loop receives from it in `watchEvents`'s `select` and
again, after `Unregister`, to wait for the goroutine, and gets the store's writer back at the
first of these receives.

The producer hands over `P v ∗ Ws` with a value `v` (the send), or `Wc` with a close that follows
no send. The consumer's first receive takes what was handed over (`P v ∗ Ws` with the value, `Wc`
with the close), however many receives the consumer makes; once it has, a receive returns only the
close (`ok = false`). Unlike Perennial's SPSC idiom (`Idioms/Spsc.lean`), whose consumer token is
consumed by the receive of the close, the consumer may receive the close again; and the resource
of a send is not split from that of the close, so receiving the value suffices to have it (the
producer need not have closed yet).

Ghost state: `sent` (a `dghostVar` of `Bool`, half the producer's, half the invariant's; the
invariant takes the producer's half when the channel is closed) and `taken` (half the consumer's,
half the invariant's).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

/-- Ghost names of a handoff channel. -/
structure HandoffNames where
  /-- the channel's -/
  chanName : ChanNames
  /-- whether the producer has sent its value -/
  sentName : GName
  /-- whether the consumer has taken the resource -/
  takenName : GName

section handoff
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The producer's token: whether it has sent its value. -/
def handoffProducer (γ : HandoffNames) (h : Bool) : IProp GF :=
  dghostVar γ.sentName (DFrac.own (1 : Qp).half) h

/-- The consumer's token: whether it has taken the resource. -/
def handoffConsumer (γ : HandoffNames) (g : Bool) : IProp GF :=
  dghostVar γ.takenName (DFrac.own (1 : Qp).half) g

/-- The state-dependent part of the invariant (`h`: sent, `g`: taken). An empty buffer: nothing
sent and nothing taken, or the sent value received. A buffered value (sent, not taken): its
resources. Closed (the producer's token parked): with the value still buffered, its resources;
otherwise taken, or nothing sent nor taken and the close's resource. -/
def handoffMatch (γ : HandoffNames) (P : V → IProp GF) (Ws Wc : IProp GF) (h g : Bool) :
    ChanState V → IProp GF
  | .Buffered [] => iprop(⌜g = h⌝)
  | .Buffered [v] => iprop(⌜h = true ∧ g = false⌝ ∗ P v ∗ Ws)
  | .Closed [] => iprop(handoffProducer γ h ∗ (⌜g = true⌝ ∨ (⌜g = false ∧ h = false⌝ ∗ Wc)))
  | .Closed [v] => iprop(handoffProducer γ h ∗ ⌜h = true ∧ g = false⌝ ∗ P v ∗ Ws)
  | _ => iprop(False)

/-- The invariant of a handoff channel. -/
def handoffInv (γ : HandoffNames) (P : V → IProp GF) (Ws Wc : IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V) (h g : Bool), ownChan γ.chanName V s ∗
    dghostVar γ.sentName (DFrac.own (1 : Qp).half) h ∗
    dghostVar γ.takenName (DFrac.own (1 : Qp).half) g ∗ handoffMatch γ P Ws Wc h g s)

/-- `ch` is a handoff channel (persistent): values `P v` and the resource `Ws` handed over with
a send, `Wc` with a close that follows no send. -/
def isHandoff (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF) : IProp GF :=
  iprop(isChan ch γ.chanName V ∗ inv nroot (handoffInv γ P Ws Wc))

instance isHandoff_persistent (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF) :
    Persistent (isHandoff γ ch P Ws Wc) := by
  unfold isHandoff; infer_instance

/-- What a receive gives the consumer, which had taken the resource (`g`) or not: once taken,
only the close; else the value and its resources, or the close and its resource. -/
def handoffGot (P : V → IProp GF) (Ws Wc : IProp GF) (g : Bool) (v : V) (ok : Bool) : IProp GF :=
  if g then iprop(⌜ok = false ∧ v = zero_val V⌝)
  else if ok then iprop(P v ∗ Ws) else iprop(⌜v = zero_val V⌝ ∗ Wc)

omit [IntoValTyped (GF := GF) V t] in
/-- A new buffered channel is a handoff, with its producer and consumer. -/
theorem start_handoff (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF) (γ : ChanNames) :
    ⊢ isChan ch γ V -∗ ownChan γ V (.Buffered []) ={⊤}=∗
      ∃ γh : HandoffNames, ⌜γh.chanName = γ⌝ ∗ isHandoff γh ch P Ws Wc ∗
        handoffProducer γh false ∗ handoffConsumer γh false := by
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%γs, Hs⟩
  icases dghostVar_halves _ _ $$ Hs with ⟨HsA, HsB⟩
  imod dghostVar_alloc false with ⟨%γg, Hg⟩
  icases dghostVar_halves _ _ $$ Hg with ⟨HgA, HgB⟩
  imod inv_alloc nroot ⊤ (handoffInv ⟨γ, γs, γg⟩ P Ws Wc) $$ [Hoc HsA HgA] with #Hinv
  · inext
    unfold handoffInv
    iexists .Buffered [], false, false
    iframe
    simp only [handoffMatch]
    itrivial
  imodintro
  iexists ⟨γ, γs, γg⟩
  unfold isHandoff handoffProducer handoffConsumer
  iframe
  iframe #
  ipureintro; rfl

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
/-- **Receiving** on a handoff channel (the atomic update, for a `select`). -/
theorem handoff_rcv_au (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (g : Bool) (Φ : V → Bool → IProp GF) :
    ⊢ isHandoff γ ch P Ws Wc -∗ £ 1 -∗ handoffConsumer γ g -∗
      ▷ (∀ (v : V) (ok : Bool), handoffConsumer γ true ∗ handoffGot P Ws Wc g v ok -∗ Φ v ok) -∗
      recvAu γ.chanName V Φ := by
  unfold isHandoff recvAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 Hcons Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold handoffInv
  icases Hi with ⟨%s, %h, %g0, Hch, Hh, Hg, Hm⟩
  unfold handoffConsumer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons Hg
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨v, _ | ⟨w, rest⟩⟩) | _ | _ | _ | _ | _ | (_ | ⟨v, _ | ⟨w, rest⟩⟩)
  · -- `Buffered []`: blocks
    itrivial
  · -- `Buffered [v]`: the value and its resources
    simp only [handoffMatch]
    icases Hm with ⟨%Hhg, HP, HWs⟩
    obtain ⟨rfl, rfl⟩ := Hhg
    iintro Hoc
    imod dghostVar_update_halves true _ _ _ $$ Hcons Hg with ⟨Hcons, Hg⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hh Hg] with -
    · inext
      iexists .Buffered [], true, true
      iframe
      simp only [handoffMatch]
      itrivial
    imodintro
    iapply Hcont
    iframe Hcons
    unfold handoffGot
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  all_goals try (simp only [handoffMatch]; iexfalso; iexact Hm)
  · -- `Closed []`: taken already, or the close's resource
    simp only [handoffMatch]
    icases Hm with ⟨Hp, (%Hg1 | ⟨%Hg1, HWc⟩)⟩
    · subst Hg1
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc Hh Hg Hp] with -
      · inext
        iexists .Closed [], h, true
        iframe
        simp only [handoffMatch]
        iframe
        ileft; itrivial
      imodintro
      iapply Hcont
      iframe Hcons
      unfold handoffGot
      simp only [↓reduceIte]
      itrivial
    · obtain ⟨rfl, rfl⟩ := Hg1
      iintro Hoc
      imod dghostVar_update_halves true _ _ _ $$ Hcons Hg with ⟨Hcons, Hg⟩
      imod Hmask with -
      imod Hclose $$ [Hoc Hh Hg Hp] with -
      · inext
        iexists .Closed [], false, true
        iframe
        simp only [handoffMatch]
        iframe
        ileft; itrivial
      imodintro
      iapply Hcont
      iframe Hcons
      unfold handoffGot
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
  · -- `Closed [v]`: the value and its resources
    simp only [handoffMatch]
    icases Hm with ⟨Hp, %Hhg, HP, HWs⟩
    obtain ⟨rfl, rfl⟩ := Hhg
    iintro Hoc
    imod dghostVar_update_halves true _ _ _ $$ Hcons Hg with ⟨Hcons, Hg⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hh Hg Hp] with -
    · inext
      iexists .Closed [], true, true
      iframe
      simp only [handoffMatch]
      iframe
      ileft; itrivial
    imodintro
    iapply Hcont
    iframe Hcons
    unfold handoffGot
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

/-- **Receiving** on a handoff channel. -/
theorem wp_handoff_receive (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (g : Bool) :
    {{ isHandoff γ ch P Ws Wc ∗ handoffConsumer γ g }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        handoffConsumer γ true ∗ handoffGot P Ws Wc g v ok }} := by
  iintro %Φ ⟨#Hh, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hh]
  · unfold isHandoff; icases Hh with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply handoff_rcv_au γ ch P Ws Wc g (fun v ok => Φ (PairV #v #ok)) $$ Hh Hlc1 Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
/-- **Sending** the value, with its resources (the producer has not sent before). -/
theorem handoff_send_au (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (v : V) (Φ : IProp GF) :
    ⊢ isHandoff γ ch P Ws Wc -∗ £ 1 -∗ handoffProducer γ false ∗ P v ∗ Ws -∗
      ▷ (handoffProducer γ true -∗ Φ) -∗ sendAu γ.chanName v Φ := by
  unfold isHandoff sendAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprod, HP, HWs⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold handoffInv
  icases Hi with ⟨%s, %h, %g, Hch, Hh, Hg, Hm⟩
  unfold handoffProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod Hh
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨v', _ | ⟨w, rest⟩⟩) | _ | _ | _ | _ | _ | (_ | ⟨v', _ | ⟨w, rest⟩⟩)
  · -- `Buffered []`: buffer the value
    simp only [handoffMatch]
    icases Hm with %Hg
    subst Hg
    iintro Hoc
    imod dghostVar_update_halves true _ _ _ $$ Hprod Hh with ⟨Hprod, Hh⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hh Hg HP HWs] with -
    · inext
      iexists .Buffered [v], true, false
      iframe
      simp only [List.nil_append]
      iframe
      ipureintro; simp
    imodintro
    iapply Hcont $$ Hprod
  · simp only [handoffMatch]
    icases Hm with ⟨%Hhg, -⟩
    cases Hhg.1
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    icases Hm with ⟨Hp2, -⟩
    iunfold handoffProducer at Hp2
    iapply dghostVar_three_halves $$ Hprod Hh Hp2
  · simp only [handoffMatch]
    icases Hm with ⟨Hp2, -⟩
    iunfold handoffProducer at Hp2
    iapply dghostVar_three_halves $$ Hprod Hh Hp2
  · simp only [handoffMatch]
    iexfalso; iexact Hm

/-- **Sending** the value, with its resources (the producer has not sent before). -/
theorem wp_handoff_send (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (v : V) :
    {{ isHandoff γ ch P Ws Wc ∗ handoffProducer γ false ∗ P v ∗ Ws }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); handoffProducer γ true }} := by
  iintro %Φ ⟨#Hh, Hprod, HP, HWs⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hh]
  · unfold isHandoff; icases Hh with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply handoff_send_au γ ch P Ws Wc v (Φ #()) $$ Hh Hlc1 [$Hprod $HP $HWs] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
/-- **Closing**: after a send, nothing more; otherwise with the close's resource. -/
theorem handoff_close_au (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (h : Bool) (Φ : IProp GF) :
    ⊢ isHandoff γ ch P Ws Wc -∗ £ 1 -∗ handoffProducer γ h ∗ (if h then iprop(True) else Wc) -∗
      ▷ Φ -∗ closeAu γ.chanName V Φ := by
  unfold isHandoff closeAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc1 ⟨Hprod, HWc⟩ Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold handoffInv
  icases Hi with ⟨%s, %h0, %g, Hch, Hh, Hg, Hm⟩
  unfold handoffProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod Hh
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨v', _ | ⟨w, rest⟩⟩) | _ | _ | _ | _ | _ | (_ | ⟨v', _ | ⟨w, rest⟩⟩)
  · -- `Buffered []`: closed
    simp only [handoffMatch]
    icases Hm with %Hg
    have Hg' := Hg.symm
    subst Hg'
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hh Hg Hprod HWc] with -
    · inext
      iexists .Closed [], h, h
      iframe Hoc Hh Hg
      simp only [handoffMatch]
      unfold handoffProducer
      iframe Hprod
      cases h
      · iright
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe HWc
        ipureintro; simp
      · ileft; itrivial
    imodintro
    iexact Hcont
  · -- `Buffered [v]`: closed with the value buffered
    simp only [handoffMatch]
    icases Hm with ⟨%Hhg, HP, HWs⟩
    obtain ⟨rfl, rfl⟩ := Hhg
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hh Hg Hprod HP HWs] with -
    · inext
      iexists .Closed [v'], true, false
      iframe Hoc Hh Hg
      simp only [handoffMatch]
      unfold handoffProducer
      iframe
      ipureintro; simp
    imodintro
    iexact Hcont
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    iexfalso; iexact Hm
  · simp only [handoffMatch]
    icases Hm with ⟨Hp2, -⟩
    iunfold handoffProducer at Hp2
    iapply dghostVar_three_halves $$ Hprod Hh Hp2
  · simp only [handoffMatch]
    icases Hm with ⟨Hp2, -⟩
    iunfold handoffProducer at Hp2
    iapply dghostVar_three_halves $$ Hprod Hh Hp2
  · simp only [handoffMatch]
    iexfalso; iexact Hm

/-- **Closing**: after a send, nothing more; otherwise with the close's resource. -/
theorem wp_handoff_close (γ : HandoffNames) (ch : Loc) (P : V → IProp GF) (Ws Wc : IProp GF)
    (h : Bool) {ct : go.GoType} {dir : go.ChanDir} [ct ↓u go.ChannelType dir t] :
    {{ isHandoff γ ch P Ws Wc ∗ handoffProducer γ h ∗ (if h then iprop(True) else Wc) }}
      (App (Val #(functions go.close [ct])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hh, Hprod, HWc⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hh]
  · unfold isHandoff; icases Hh with ⟨$, -⟩
  iapply chan.wp_close (ct := ct) ch γ.chanName $$ Hch
  iintro ⟨Hlc1, _, _, _⟩
  iapply handoff_close_au γ ch P Ws Wc h (Φ #()) $$ Hh Hlc1 [$Hprod $HWc]
  inext
  iapply HΦ
  itrivial

end handoff

end EtcdGrove
end Perennial
