module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.consume
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toWEvent
public import Perennial.Spec.time.NewTimer
public import Perennial.Spec.time.After
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open k8s_io.apimachinery.pkg.watch (Event)
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `select` on two time channels (`case <-timer.C`, `case <-time.After(d)`). -/
theorem wp_select_bag_bag (c1 : Loc) (γ1 : ChanNames) (c2 : Loc) (γ2 : ChanNames)
    (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := time.Time) γ1 c1 (fun _ => iprop(True)) -∗
      isChanBag (V := time.Time) γ2 c2 (fun _ => iprop(True)) -∗ £ 1 ∗ £ 1 -∗
      ((∀ t : time.Time, WP (App h1 (Val (PairV #t #true))) {{ Φ }}) ∧
        (∀ t : time.Time, WP (App h2 (Val (PairV #t #true))) {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase time.Time.ty (Val #c1)) h1,
         CommClause (RecvCase time.Time.ty (Val #c2)) h2]))) {{ Φ }} := by
  iintro #Hb1 #Hb2 Hlc Hh
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c1, γ1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb1
    iapply bag_recv_au $$ Hlc Hb1
    inext
    iintro %t -
    icases Hh with ⟨Hh, -⟩
    iapply Hh
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c2, γ2
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb2
    iapply bag_recv_au $$ Hlc Hb2
    inext
    iintro %t -
    icases Hh with ⟨-, Hh⟩
    iapply Hh
  · iapply BigAndL.bigAndL_nil.2
    itrivial

/-- A `select` on a time channel and an SPSC channel of watch events, of which the caller is the
consumer (`case <-timer.C`, `case ev, open := <-w.ResultChan()`). -/
theorem wp_select_bag_spsc (c1 : Loc) (γ1 : ChanNames) (γs : SpscNames) (ch : Loc)
    (P : Int → Event → IProp GF) (R : List Event → IProp GF) (recv : List Event)
    (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := time.Time) γ1 c1 (fun _ => iprop(True)) -∗ isSpsc γs ch P R -∗
      £ 1 ∗ £ 1 -∗ spscConsumer γs recv -∗
      ((spscConsumer γs recv -∗ ∀ t : time.Time, WP (App h1 (Val (PairV #t #true))) {{ Φ }}) ∧
        (∀ (v : Event) (ok : Bool),
          (if ok then iprop(P recv.length v ∗ spscConsumer γs (recv ++ [v]))
           else iprop(R recv ∗ ⌜v = zero_val Event⌝)) -∗
          WP (App h2 (Val (PairV #v #ok))) {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase time.Time.ty (Val #c1)) h1,
         CommClause (RecvCase k8s_io.apimachinery.pkg.watch.Event.ty (Val #ch)) h2]))) {{ Φ }} := by
  iintro #Hb1 #Hs ⟨Hlc1, Hlc2⟩ Hc Hh
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c1, γ1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb1
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hb1
    inext
    iintro %t -
    icases Hh with ⟨Hh, -⟩
    iapply Hh $$ Hc
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Event, inferInstance, inferInstance, inferInstance, inferInstance, ch, γs.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at Hs
      icases Hs with ⟨#Hch, -⟩
      iexact Hch
    iapply spsc_rcv_au γs ch _ _ recv _ $$ Hs [$Hlc1 $Hlc2] Hc
    inext
    iintro %v %ok Hv
    icases Hh with ⟨-, Hh⟩
    iapply Hh $$ Hv
  · iapply BigAndL.bigAndL_nil.2
    itrivial

theorem consume_forall₂_snoc {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {a : α} {b : β}, List.Forall₂ R l1 l2 → R a b →
      List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])
  | [], [], _, _, .nil, h => List.Forall₂.cons h List.Forall₂.nil
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => List.Forall₂.cons h1 (consume_forall₂_snoc h2 h)

theorem consume.wp_proof
    (wp_toWEvent : toWEvent.spec (GF := GF) (hG := hG))
    (wp_NewTimer : time.NewTimer.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG)) :
    consume.spec (GF := GF) (hG := hG) := by
  intro c wi γ cd γd sel emp inS m Q x hS hcd
  wp_start as ⟨Hw, Hdt⟩
  iunfold k8sWatch at Hw
  icases Hw with ⟨%wo, %ch, %Hwi, #HRes, #HStopW, #Hsp, Hcons, Hlive⟩
  subst Hwi
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_NewTimer as %t %tch %γt #Ht
  (try wp_auto)
  ihave #Ht' := Ht
  iunfold time.isTimer at Ht'
  icases Ht' with ⟨#HtC, -, -, #Htb⟩
  ihave #HSO : kStopOk (GoInterface.ok wo) γ $$ []
  · iunfold kStopOk
    iexists wo
    isplitr
    · ipureintro; rfl
    imodintro
    iexact HStopW
  wp_if_destruct
  · -- stalled: wait `hiccupDuration`, no events
    wp_apply (time.After.spec_pkgInit wp_After _) as %ach %γa #Ha
    wp_apply (wp_bag_receive γa ach (fun _ : time.Time => iprop(True))) $$ [$Ha] as %_ -
    (try wp_auto)
    wp_apply wp_Stop $$ [] as %_ -
    · ileft; iexists tch, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists [], []
    isplitr
    · iunfold wevsOwnM; iexists []; isplitr
      · iapply ownSlice_nil
      · ipureintro; rfl
    isplitr
    · iapply k8s_correctness.evsRO_nil
    isplitr
    · ipureintro; exact List.Forall₂.nil
    isplitr
    · iunfold kSeen; ileft; ipureintro; rfl
    iframe
    iexact HSO
  ihave HI : iprop(∃ (iD hD : Bool) (sl : GoSlice) (ws : List WEvent) (recv : List Event)
      (kes : List (KWEv DObj)) (rsl : GoSlice) (vs : List Event) (rs : List k8s_correctness.REv),
      "initialDone" ∷ initialDone_ptr ↦ iD ∗ "hiccupDone" ∷ hiccupDone_ptr ↦ hD ∗
      "evs" ∷ evs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ws ∗ "Hcap" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
      "raw" ∷ raw_ptr ↦ rsl ∗ "Hrsl" ∷ rsl ↦* vs ∗ "Hrcap" ∷ ownSliceCap Event rsl (DFrac.own 1) ∗
      "#Hvs" ∷ ([∗list] v;r ∈ vs;rs, k8s_correctness.evRep v r) ∗
      "%Hrel" ∷ ⌜List.Forall₂ kWEvRel kes (rs.map k8s_correctness.toWEvL) ∧ kes.length = recv.length ∧
        ws.map wevOf = rs.map k8s_correctness.toWEvL⌝ ∗
      "#Hidx" ∷ ([∗list] j ↦ e ∈ kes, monoListIdxOwn γ.evs j e) ∗
      "Hseen" ∷ kSeen c sel emp inS m Q kes ∗
      "Hcons" ∷ spscConsumer γ.res recv ∗ "Hlive" ∷ kLive γ ∗ "Hdt" ∷ doneTok γd)
      $$ [initialDone hiccupDone evs raw Hcons Hlive Hdt]
  · iexists _, _, slice.nil, [], [], [], slice.nil, [], []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    isplitr
    · ipureintro; exact ⟨List.Forall₂.nil, rfl, rfl⟩
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iunfold kSeen; ileft; ipureintro; rfl
  irename «in» => Hin
  simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.hiccupDuration,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.slowDelay,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.maxEvents,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WBookmark]
  wp_for HI
  wp_join (Q := fun v => iprop(∃ hD' : Bool, "hiccupDone" ∷ hiccupDone_ptr ↦ hD' ∗
      "evs" ∷ evs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ws ∗ "Hin" ∷ in_ptr ↦ x ∗ "timer" ∷ timer_ptr ↦ t ∗
      "raw" ∷ raw_ptr ↦ rsl ∗
      ((⌜v = executeVal⌝ ∗ "$res0" ∷ «$res0_ptr» ↦ zero_val GoSlice ∗
          "$res1" ∷ «$res1_ptr» ↦ zero_val GoSlice) ∨
       (⌜v = returnVal #()⌝ ∗ "$res0" ∷ «$res0_ptr» ↦ sl ∗ "$res1" ∷ «$res1_ptr» ↦ rsl))))
    at next with [hiccupDone evs Hsl Hin «$res0» «$res1» raw timer]
  · cases iD
    · wp_auto
      iexists hD
      iframe
      ileft
      iframe
      ipureintro; rfl
    wp_auto
    wp_join iprop(∃ (hD' : Bool) (d : time.Duration), hiccupDone_ptr ↦ hD' ∗
        delay_ptr ↦ d ∗ evs_ptr ↦ sl ∗ sl ↦* ws ∗ in_ptr ↦ x)
        at next with [hiccupDone delay evs Hsl Hin]
        as ⟨%hD', %d, hiccupDone, delay, evs, Hsl, Hin⟩
    · cases hD
      · wp_auto
        wp_if_destruct
        · (try wp_auto); wp_join_done
        · (try wp_auto)
          wp_if_destruct <;> ((try wp_auto); wp_join_done)
      · wp_auto
        wp_if_destruct <;> ((try wp_auto); wp_join_done)
    wp_if_destruct
    · wp_apply (lc := 2) (time.After.spec_pkgInit wp_After _) as %ach %γa #Ha
      wp_apply_core (wp_select_bag_bag tch γt ach γa) $$ Htb Ha [$Hlc1 $Hlc2]
      isplit
      · iintro %_
        wp_auto
        iexists hD'
        iframe
        iright
        iframe
        try (ipureintro; rfl)
      · iintro %_
        wp_auto
        iexists hD'
        iframe
        ileft
        iframe
        try (ipureintro; rfl)
    · iexists hD'
      iframe
      ileft
      iframe
  iintro ⟨%hD', hiccupDone, evs, Hsl, Hin, timer, raw, Hr⟩
  icases Hr with (⟨%Hv, «$res0», «$res1»⟩ | ⟨%Hv, «$res0», «$res1»⟩) <;> subst Hv
  rotate_left
  · -- the timer fired during the delay: return
    wp_auto
    wp_for_post
    imod ownSlice_persist rsl _ _ $$ Hrsl with #Hrsl
    wp_apply wp_Stop $$ [] as %_ -
    · ileft; iexists tch, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists rs, kes
    isplitl [Hsl]
    · iunfold wevsOwnM; iexists ws; iframe; ipureintro; exact Hrel.2.2
    isplitr
    · iunfold k8s_correctness.evsRO; iexists vs; iframe #
    isplitr
    · ipureintro; exact Hrel.1
    iframe
    iexact HSO
  wp_auto
  wp_apply (lc := 2) HRes
  wp_apply_core (wp_select_bag_spsc tch γt γ.res ch _ _ recv) $$ Htb Hsp [$Hlc1 $Hlc2] Hcons
  isplit
  · -- the timer fired: return
    iintro Hcons %_
    wp_auto
    wp_for_post
    imod ownSlice_persist rsl _ _ $$ Hrsl with #Hrsl
    wp_apply wp_Stop $$ [] as %_ -
    · ileft; iexists tch, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists rs, kes
    isplitl [Hsl]
    · iunfold wevsOwnM; iexists ws; iframe; ipureintro; exact Hrel.2.2
    isplitr
    · iunfold k8s_correctness.evsRO; iexists vs; iframe #
    isplitr
    · ipureintro; exact Hrel.1
    iframe
    iexact HSO
  iintro %v %ok
  cases ok
  · -- the channel closed: return
    rw [ite_eq_right Bool.false_ne_true]
    iintro Hv
    icases Hv with ⟨-, %Hv0⟩
    wp_auto
    wp_for_post
    imod ownSlice_persist rsl _ _ $$ Hrsl with #Hrsl
    wp_apply wp_Stop $$ [] as %_ -
    · ileft; iexists tch, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists rs, kes
    isplitl [Hsl]
    · iunfold wevsOwnM; iexists ws; iframe; ipureintro; exact Hrel.2.2
    isplitr
    · iunfold k8s_correctness.evsRO; iexists vs; iframe #
    isplitr
    · ipureintro; exact Hrel.1
    iframe
    iexact HSO
  rw [ite_eq_left rfl]
  iintro ⟨Hel, Hcons⟩
  iunfold kResElem at Hel
  icases Hel with ⟨%e, %kes', Hwev, %Hlen, #Hidx', Hdisj⟩
  -- the element's prefix is what was received
  ihave #Hp := BigSepL.bigSepL_snoc.1 $$ Hidx'
  icases Hp with ⟨#Hp, -⟩
  ihave %Hk := monoList_idxs_agree γ.evs kes kes' (by omega) $$ Hidx Hp
  subst Hk
  -- its cancellation branch is refuted
  ihave H3 : iprop(kSeen c sel emp inS m Q (kes ++ [e]) ∗ kLive γ ∗ doneTok γd)
      $$ [Hdisj Hlive Hdt]
  · iunfold kSeen
    icases Hdisj with (%Hne | ⟨%lb, %lb0, %st, %σ, %σ0, #HQ, #HQ0, %Hst, %Hsub, Hok⟩)
    · iframe; ileft; ipureintro; exact Hne
    icases Hok with (%Hok | #Hc)
    · iframe; iright; iexists lb, lb0, st, σ, σ0
      isplitr
      · iexact HQ
      isplitr
      · iexact HQ0
      ipureintro; exact ⟨Hst, Hok⟩
    · iexfalso; iapply kCancelled_refute γ cd γd hcd $$ [$Hlive $Hdt $Hc]
  icases H3 with ⟨Hseen', Hlive, Hdt⟩
  iclear Hseen
  rw [hS] at *
  wp_auto
  wp_apply wp_toWEvent $$ [$Hwev] as %we ⟨%r, %Hwe, #Hr⟩
  wp_apply wp_slice_literal (V := WEvent) [we]
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %s1 ⟨Hs1, Hc1, -⟩
  wp_apply wp_slice_literal (V := Event) [v]
  isplitr
  · ipureintro; rfl
  iintro %rlit ⟨Hrlit, -⟩
  wp_apply wp_slice_append $$ [$Hrsl $Hrcap $Hrlit] as %rs1 ⟨Hrs1, Hrc1, -⟩
  ihave #Hvs' : ([∗list] v;r ∈ vs ++ [v];rs ++ [r], k8s_correctness.evRep v r : IProp GF) $$ []
  · iapply BigSepL2.bigSepL2_snoc.2; iframe #
  have Hrel' : List.Forall₂ kWEvRel (kes ++ [e]) ((rs ++ [r]).map k8s_correctness.toWEvL) ∧
      (kes ++ [e]).length = (recv ++ [v]).length ∧
      (ws ++ [we]).map wevOf = (rs ++ [r]).map k8s_correctness.toWEvL := by
    refine ⟨?_, by simp [Hrel.2.1], by simp [List.map_append, Hrel.2.2, Hwe.2]⟩
    rw [List.map_append, List.map_singleton, ← Hwe.2]; exact consume_forall₂_snoc Hrel.1 Hwe.1
  wp_join iprop(∃ iD' : Bool, initialDone_ptr ↦ iD') with [initialDone] as ⟨%iD', initialDone⟩
  all_goals (try (iexists _; iframe; done))
  wp_if_destruct
  · -- `maxEvents` events: return
    wp_for_post
    imod ownSlice_persist rs1 _ _ $$ Hrs1 with #Hrs1
    wp_apply wp_Stop $$ [] as %_ -
    · ileft; iexists tch, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists rs ++ [r], kes ++ [e]
    isplitl [Hs1]
    · iunfold wevsOwnM; iexists ws ++ [we]; iframe; ipureintro; exact Hrel'.2.2
    isplitr
    · iunfold k8s_correctness.evsRO; iexists vs ++ [v]; iframe #
    isplitr
    · ipureintro; exact Hrel'.1
    iframe
    iexact HSO
  · -- again
    wp_for_post
    iframe
    iexists iD', hD', s1, ws ++ [we], recv ++ [v], kes ++ [e], rs1, vs ++ [v], rs ++ [r]
    iframe
    iframe #
    isplitr
    · ipureintro; exact Hrel'
    ihave ⟨-, #Hl⟩ := BigSepL.bigSepL_append.1 $$ Hidx'
    iexact Hl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
