/-
The client's side of the watchable store (unit 3c): the receive on a stream's channel
(`wp_watch_receive`, a lemma about the Go receive `v, ok := <-ch`, as the cache's
`wp_watcher_receive`: not a Go function of the package) and the watch guarantee. Lean-first;
`notes/decisions.md`, "The watchable store's concurrency (unit 3)".

**What a client knows per watcher** (`watchRecvOk`, persistent): the responses it received for a
watcher are a prefix of the watcher's deliveries (the channel invariant's `chanWatcher`), cut at
a revision (`delivsCut`): their events, concatenated, are the deliveries' kept events, each
delivery's events filtered by predicates the watcher's filters implement, and the deliveries'
events, concatenated, are the watcher's range's events of the revisions `[lo, d)` of a log the
index's history has (`watchEvents`, `lo` its first revision).

**The guarantee** (`watchRecvOk_cert`, `watchGuarantee_unfiltered`, `watchRecvOk_revs`): against
any certified log long enough (`idxCert`), the client received, for each watcher, exactly the
changes of the keys in its range from its first revision on, in revision order, once each,
filtered only by its own filters, up to some revision; each response's revision is at or above
its events', and a response with events carries the watcher's id.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## A prefix of the deliveries (pure) -/

/-- A prefix of the kept events of the sent deliveries is that of a prefix of the deliveries. -/
theorem delivs_prefix_cut : ∀ (D : List Deliv) (rs : List (List EvM)),
    rs <+: (D.filter Deliv.sent).map Prod.snd →
    ∃ k, k ≤ D.length ∧ rs = ((D.take k).filter Deliv.sent).map Prod.snd
  | [], rs, h => ⟨0, Nat.le_refl _, by simpa using h⟩
  | dl :: D, rs, h => by
    rcases rs with _ | ⟨x, rs'⟩
    · exact ⟨0, Nat.zero_le _, by simp⟩
    by_cases hs : Deliv.sent dl = true
    · simp only [List.filter_cons, hs, ↓reduceIte, List.map_cons, List.cons_prefix_cons] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨k, hk, e⟩ := delivs_prefix_cut D rs' h'
      exact ⟨k + 1, by simp; omega, by simp [hs, e]⟩
    · have h' : x :: rs' <+: (D.filter Deliv.sent).map Prod.snd := by
        simpa [List.filter_cons, hs] using h
      obtain ⟨k, hk, e⟩ := delivs_prefix_cut D (x :: rs') h'
      exact ⟨k + 1, by simp; omega, by simp [hs, e]⟩

theorem prefix_drop_cons' {α : Type} {sent recv rs : List α} {r : α} (hp : recv <+: sent)
    (hd : sent.drop recv.length = r :: rs) :
    recv ++ [r] <+: sent ∧ sent.drop (recv ++ [r]).length = rs := by
  obtain ⟨t, rfl⟩ := hp
  simp only [List.drop_left] at hd
  subst hd
  exact ⟨⟨rs, by simp⟩, by simp⟩

theorem prefix_drop_nil' {α : Type} {sent recv : List α} (hp : recv <+: sent)
    (hd : sent.drop recv.length = []) : recv = sent := by
  obtain ⟨t, rfl⟩ := hp
  simp only [List.drop_left] at hd
  simp [hd]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## What a client knows per watcher -/

/-- **What a client knows of the watcher `w`** after receiving the responses `rs` for it (their
models, in order; persistent): `w`'s names (its first revision `γw.lo`), its fixed fields (range
`r`, filters `fcs`), and deliveries `D`: the received responses' events are the kept events of
the sent deliveries, each delivery's kept events are its events filtered by predicates `fcs`
implements, and the deliveries' events, concatenated, are the range's events of the revisions
`[γw.lo, d)` of a log `L` the index's history has (`d` past `L` only for an empty range); and
what each response says (`respOk`). -/
def watchRecvOk (γ : WsNames) (w : Loc) (rs : List RespM) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (L : Log) (D : List Deliv) (d : Nat),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ monoListLbOwn γ.st.idx.hist (histOf L) ∗
    ⌜rs.map RespM.evs = (D.filter Deliv.sent).map Prod.snd ∧
      (D.map Prod.fst).flatten = watchEvents L r γw.lo d ∧ (d ≤ L.length ∨ d ≤ γw.lo) ∧
      ∀ x ∈ rs, x.w = w⌝ ∗
    □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ∗
    □ (∀ x : RespM, ⌜x ∈ rs⌝ -∗ respOk x))

instance watchRecvOk_persistent (γ : WsNames) (w : Loc) (rs : List RespM) :
    Persistent (watchRecvOk (GF := GF) γ w rs) := by
  unfold watchRecvOk; infer_instance

/-- A registered watcher's entry gives what a client knows of any prefix of the responses sent
for it. -/
theorem chanWatcher_recvOk (γ : WsNames) (γc : WatchChanNames) (closed : Bool)
    (sent : List RespM) (w : Loc) (rs : List RespM)
    (hrs : rs <+: sent.filter (fun x => decide (x.w = w))) :
    chanWatcher (GF := GF) γ γc closed sent w ∗ □ ([∗list] x ∈ sent, respOk x) ⊢
      chanWatcher γ γc closed sent w ∗ watchRecvOk γ w rs := by
  iintro ⟨Hc, #Hok⟩
  iunfold chanWatcher at Hc
  icases Hc with ⟨%γw, %r, %fcs, %evsw, %D, %d, #Hm, %Hwc, #Hf, Ha, %HD, #HDf, #Hwf, Hlc⟩
  icases HDf with ⟨#HDs, #HDc⟩
  obtain ⟨k, hk, hke⟩ := delivs_prefix_cut D (rs.map RespM.evs) (by
    rw [← HD.2]; exact hrs.map _)
  ihave #HDc2 := HDc
  iunfold delivsCut at HDc2
  icases HDc2 $$ %k %hk with ⟨%d', #Hwf'⟩
  iunfold evsWf at Hwf'
  icases Hwf' with ⟨%L, #Hlb, %HL⟩
  isplitl [Ha Hlc]
  · iunfold chanWatcher
    iexists γw, r, fcs, evsw, D, d
    iframe Hm Hf Ha Hwf Hlc HDs HDc
    ipureintro; exact ⟨Hwc, HD⟩
  iunfold watchRecvOk
  iexists γw, r, fcs, L, D.take k, d'
  iframe Hm Hf Hlb
  isplitr
  · ipureintro
    refine ⟨hke, HL.1, HL.2, fun x hx => ?_⟩
    have := (List.mem_filter.1 (hrs.subset hx)).2
    simpa using this
  isplitr
  · iintro !> %dl %hdl
    icases BigSepL.bigSepL_mem_acc (List.mem_of_mem_take hdl) $$ HDs with ⟨H, -⟩
    iexact H
  · iintro !> %x %hx
    icases BigSepL.bigSepL_mem_acc (List.mem_filter.1 (hrs.subset hx)).1 $$ Hok with ⟨H, -⟩
    iexact H

/-! ## The receive -/

/-- What the consumer gets from `v, ok := <-ch` with `received` received so far: on `ok`, the
next response sent (`respIs v r`, `respOk r`), its consumer's view grown, and what it knows of
`r`'s watcher from the responses received for it; on `!ok` (the channel closed and drained), its
view unchanged. -/
def watchRecvResult (γ : WsNames) (γc : WatchChanNames) (received : List RespM)
    (v : WatchResponse) (ok : Bool) : IProp GF :=
  if ok then iprop(∃ r : RespM, watchConsumer γc (received ++ [r]) ∗ respIs v r ∗ respOk r ∗
    watchRecvOk γ r.w ((received ++ [r]).filter (fun x => decide (x.w = r.w))))
  else watchConsumer γc received

theorem respsIs_cons (v : WatchResponse) (rest : List WatchResponse) (rs : List RespM) :
    respsIs (GF := GF) (v :: rest) rs ⊢
      ∃ (r : RespM) (rs' : List RespM), ⌜rs = r :: rs'⌝ ∗ respIs v r ∗ respsIs rest rs' := by
  unfold respsIs
  iintro ⟨%Hlen, #H⟩
  rcases rs with _ | ⟨r, rs'⟩
  · simp at Hlen
  iexists r, rs'
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply H $$ %0 %v %r %rfl %rfl
  isplitr
  · ipureintro; simpa using Hlen
  iintro !> %i %v' %r' %h1 %h2
  iapply H $$ %(i + 1) %v' %r' %(by simpa using h1) %(by simpa using h2)

/-- Taking the first in-flight response `v`: the consumer's view grows by its model `r`, which
is the next response sent, and what the client knows of its watcher. -/
theorem watch_take (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (received sent : List RespM)
    (L : List Loc) (v : WatchResponse) (rest : List WatchResponse) (hpre : received <+: sent)
    (hsw : ∀ x ∈ sent, x.w ∈ L) :
    ghostVar (GF := GF) γc.recv (1 : Qp).half received ∗ ghostVar γc.recv (1 : Qp).half received ∗
      respsIs (v :: rest) (sent.drop received.length) ∗ □ ([∗list] x ∈ sent, respOk x) ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ⊢
    |==> ∃ r : RespM, ghostVar γc.recv (1 : Qp).half (received ++ [r]) ∗
      ghostVar γc.recv (1 : Qp).half (received ++ [r]) ∗
      respsIs rest (sent.drop (received ++ [r]).length) ∗ ⌜received ++ [r] <+: sent⌝ ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ∗ respIs v r ∗ respOk r ∗
      watchRecvOk γ r.w ((received ++ [r]).filter (fun x => decide (x.w = r.w))) := by
  iintro ⟨H1, H2, #Hvs, #Hok, Hws⟩
  icases respsIs_cons _ _ _ $$ Hvs with ⟨%r, %rs', %Hd, #Hr, #Hrest⟩
  obtain ⟨Hp', Hd'⟩ := prefix_drop_cons' hpre Hd
  have hr : r ∈ sent := Hp'.subset (by simp)
  icases BigSepL.bigSepL_mem_acc (hsw r hr) $$ Hws with ⟨Hw, Hback⟩
  ihave ⟨Hw, #Hrok⟩ := chanWatcher_recvOk γ γc closed sent r.w
    ((received ++ [r]).filter (fun x => decide (x.w = r.w))) (Hp'.filter _) $$ [$Hw $Hok]
  ihave Hws := Hback $$ Hw
  icases BigSepL.bigSepL_mem_acc hr $$ Hok with ⟨#Hro, -⟩
  imod ghostVar_update_halves (received ++ [r]) γc.recv _ _ $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iexists r
  iframe H1 H2 Hws Hr Hro Hrok
  rw [Hd']
  iframe Hrest
  ipureintro; exact Hp'

/-- The consumer's receive on the stream's channel, as the atomic update of Perennial's channel
specs (`recvAu`, for `chan.wp_receive` or a blocking `select` case): the next response sent
after `received` (`ok`), or, once the channel is closed and drained, `!ok`. -/
theorem watch_recv_au (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (received : List RespM)
    (Φ : WatchResponse → Bool → IProp GF) :
    ⊢ inv watchN (watchChanInv γ ch γc) -∗ watchConsumer γc received -∗
      (∀ (v : WatchResponse) (ok : Bool), watchRecvResult γ γc received v ok -∗ Φ v ok) -∗
      recvAu γc.ch WatchResponse Φ := by
  iintro #Hinv Hcons HΦ
  unfold recvAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold watchChanInv at Hi
  iNamed Hi
  unfold watchConsumer
  ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hcons Hrecv
  subst Heq
  iexists s
  iframe Hch
  rcases s with (_ | ⟨v, rest⟩) | _ | _ | _ | _ | _ | (_ | ⟨v, rest⟩)
  all_goals dsimp only
  case Buffered.nil => itrivial
  case SndPending => simp [chanInflight] at Hinfl
  case RcvPending => itrivial
  case SndCommit => itrivial
  case RcvCommit => itrivial
  case Buffered.cons =>
    iintro Hch
    irevert Hcl Hws; simp only [chanIsClosed, Bool.false_eq_true, ↓reduceIte]; iintro Hcl Hws
    simp only [chanInflight, Option.some.injEq] at Hinfl
    subst Hinfl
    imod watch_take γ γc _ received sent L v rest Hpre Hnd.2 $$ [$Hcons $Hrecv $Hvs $Hok $Hws]
      with ⟨%r, Hcons, Hrecv, #Hrest, %Hpre', Hws, #Hr, #Hro, #Hrok⟩
    imod Hmask with -
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold watchChanInv
      iexists ChanState.Buffered rest, sent, received ++ [r], rest, L
      simp only [named, chanIsClosed, Bool.false_eq_true, ↓reduceIte]
      iframe Hch Hrecv Hregl Hcl Hreg Hws
      iframe #
      ipureintro
      exact ⟨Hpre', rfl, Hnd⟩
    imodintro
    iapply HΦ
    unfold watchRecvResult
    simp only [↓reduceIte]
    iexists r
    unfold watchConsumer
    iframe Hcons
    iframe #
  case Closed.cons =>
    iintro Hch
    irevert Hcl Hws; simp only [chanIsClosed, ↓reduceIte]; iintro Hcl Hws
    simp only [chanInflight, Option.some.injEq] at Hinfl
    subst Hinfl
    imod watch_take γ γc _ received sent L v rest Hpre Hnd.2 $$ [$Hcons $Hrecv $Hvs $Hok $Hws]
      with ⟨%r, Hcons, Hrecv, #Hrest, %Hpre', Hws, #Hr, #Hro, #Hrok⟩
    imod Hmask with -
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold watchChanInv
      iexists ChanState.Closed rest, sent, received ++ [r], rest, L
      simp only [named, chanIsClosed, ↓reduceIte]
      iframe Hch Hrecv Hregl Hcl Hreg Hws
      iframe #
      ipureintro
      exact ⟨Hpre', rfl, Hnd⟩
    imodintro
    iapply HΦ
    unfold watchRecvResult
    simp only [↓reduceIte]
    iexists r
    unfold watchConsumer
    iframe Hcons
    iframe #
  case Closed.nil =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold watchChanInv
      iexists ChanState.Closed [], sent, received, vs, L
      simp only [named, chanIsClosed, ↓reduceIte]
      iframe Hch Hrecv Hregl Hcl Hreg Hws
      iframe #
      ipureintro
      exact ⟨Hpre, Hinfl, Hnd⟩
    imodintro
    iapply HΦ
    unfold watchRecvResult watchConsumer
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hcons
  case Idle =>
    -- wait for an unbuffered send
    iintro Hch
    irevert Hcl Hws; simp only [chanIsClosed, Bool.false_eq_true, ↓reduceIte]; iintro Hcl Hws
    imod Hmask with -
    imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
    · inext
      iunfold watchChanInv
      iexists ChanState.RcvPending, sent, received, vs, L
      simp only [named, chanIsClosed, Bool.false_eq_true, ↓reduceIte]
      iframe Hch Hrecv Hregl Hcl Hreg Hws
      iframe #
      ipureintro
      exact ⟨Hpre, by simpa [chanInflight] using Hinfl, Hnd⟩
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    all_goals first | (solve_ndisj; done) | skip
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iunfold watchChanInv at Hi
    iNamed Hi
    ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hcons Hrecv
    subst Heq
    iexists s
    iframe Hch
    rcases s with (_ | ⟨v', rest'⟩) | _ | _ | _ | ⟨v'⟩ | _ | (_ | ⟨v', rest'⟩)
    all_goals dsimp only
    all_goals first | itrivial | skip
    case SndCommit =>
      iintro Hch
      irevert Hcl Hws; simp only [chanIsClosed, Bool.false_eq_true, ↓reduceIte]; iintro Hcl Hws
      simp only [chanInflight, Option.some.injEq] at Hinfl
      subst Hinfl
      imod watch_take γ γc _ received sent L v' [] Hpre Hnd.2 $$ [$Hcons $Hrecv $Hvs $Hok $Hws]
        with ⟨%r, Hcons, Hrecv, #Hrest, %Hpre', Hws, #Hr, #Hro, #Hrok⟩
      imod Hmask with -
      imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
      · inext
        iunfold watchChanInv
        iexists ChanState.Idle, sent, received ++ [r], [], L
        simp only [named, chanIsClosed, Bool.false_eq_true, ↓reduceIte]
        iframe Hch Hrecv Hregl Hcl Hreg Hws
        iframe #
        ipureintro
        exact ⟨Hpre', rfl, Hnd⟩
      imodintro
      iapply HΦ
      unfold watchRecvResult
      simp only [↓reduceIte]
      iexists r
      unfold watchConsumer
      iframe Hcons
      iframe #
    case Closed.nil =>
      iintro Hch
      imod Hmask with -
      imod Hclose $$ [Hch Hrecv Hregl Hcl Hreg Hws] with -
      · inext
        iunfold watchChanInv
        iexists ChanState.Closed [], sent, received, vs, L
        simp only [named, chanIsClosed, ↓reduceIte]
        iframe Hch Hrecv Hregl Hcl Hreg Hws
        iframe #
        ipureintro
        exact ⟨Hpre, Hinfl, Hnd⟩
      imodintro
      iapply HΦ
      unfold watchRecvResult watchConsumer
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hcons

/-- **The client's receive** `v, ok := <-ch` on a stream's channel (`NewWatchStream` returns
the channel `ch`, its invariant and the consumer's view `watchConsumer γc []`): with `received`
received so far, either the next response sent, `ok`, with what the client knows of its
watcher from all the responses received for it (`watchRecvOk`), or `!ok` once the channel is
closed and drained (`watchRecvResult`). -/
theorem wp_watch_receive (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (received : List RespM) :
    ⊢ ∀ Φ : val → IProp GF,
      isChan ch γc.ch WatchResponse -∗ inv watchN (watchChanInv γ ch γc) -∗
      watchConsumer γc received -∗
      (∀ (v : WatchResponse) (ok : Bool),
        watchRecvResult γ γc received v ok -∗ Φ (PairV #v #ok)) -∗
      WP (App (Val (chan.receive WatchResponse.ty)) (Val #ch)) {{ Φ }} := by
  iintro %Φ #Hc #Hinv Hcons HΦ
  iapply chan.wp_receive ch γc.ch $$ Hc
  iintro -
  iapply watch_recv_au γ ch γc received (fun v ok => Φ (PairV #v #ok)) $$ Hinv Hcons HΦ

/-! ## The watch guarantee -/

/-- **The watch guarantee, against a certified log.** What a client knows of the watcher `w`
after receiving the responses `rs` for it, with a certificate of the log `log'` (`idxCert`, any
committed log): the responses' events, in order, are the kept events of deliveries `D` (each
delivery's events filtered by predicates `w`'s own filters implement, `filtersImpl`), and the
deliveries' events, concatenated, are exactly the changes of the keys of `w`'s range `r` at the
revisions from `w`'s first revision `γw.lo` up to some revision `d`, in revision order
(`watchEvents`), whenever `log'` reaches `d`. -/
theorem watchRecvOk_cert (γ : WsNames) (w : Loc) (rs : List RespM) (log' : Log) :
    watchRecvOk (GF := GF) γ w rs ∗ idxCert γ.st.idx log' ⊢
      ∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (D : List Deliv) (d : Nat),
        watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
        □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ∗
        ⌜rs.map RespM.evs = (D.filter Deliv.sent).map Prod.snd ∧
          (d ≤ log'.length → (D.map Prod.fst).flatten = watchEvents log' r γw.lo d)⌝ := by
  iintro ⟨Hok, #Hc⟩
  iunfold watchRecvOk at Hok
  icases Hok with ⟨%γw, %r, %fcs, %L, %D, %d, #Hm, #Hf, #Hlb, %HL, #HD, -⟩
  iunfold idxCert at Hc
  icases Hc with ⟨#Hlb', -, -, -⟩
  ihave %Hcmp := mono_list_lb_valid _ _ _ $$ Hlb Hlb'
  have hcmp := histOf_cmp_log Hcmp
  iexists γw, r, fcs, D, d
  iframe Hm Hf HD
  ipureintro
  refine ⟨HL.1, fun hd => ?_⟩
  rw [HL.2.1]
  exact watchEvents_cmp hcmp r HL.2.2.1 (Or.inl hd)

/-- **The watch guarantee for a watcher with no filters** (`fcs` the empty slice): the events of
the responses a client received for `w`, concatenated, are exactly the changes of the keys of
`w`'s range `r`, at the revisions from `w`'s first revision `γw.lo` up to some revision `d`, of
any certified log `log'` reaching `d`: every such change, once, in revision order. -/
theorem watchGuarantee_unfiltered (γ : WsNames) (w : Loc) (rs : List RespM) (log' : Log)
    (r : WatchRange) (fcs : GoSlice) :
    watchRecvOk (GF := GF) γ w rs ∗ idxCert γ.st.idx log' ∗ watcherFixed w r fcs ∗
      fcs ↦*□ ([] : List GoFunc) ⊢
      ∃ (γw : WatcherNames) (d : Nat), watcherMeta γ w γw ∗
        ⌜d ≤ log'.length → (rs.map RespM.evs).flatten = watchEvents log' r γw.lo d⌝ := by
  iintro ⟨#Hok, #Hc, #Hf, #Hfcs⟩
  ihave ⟨%γw, %r', %fcs', %D, %d, #Hm, #Hf', #HD, %HL⟩ :=
    watchRecvOk_cert γ w rs log' $$ [$Hok $Hc]
  ihave %Hag := watcherFixed_agree w r r' fcs fcs' $$ [$Hf $Hf']
  obtain ⟨rfl, rfl⟩ := Hag
  -- no filters: every delivery keeps its events
  ihave %Hkeep : ⌜∀ dl ∈ D, dl.2 = dl.1⌝ $$ []
  · iintro %dl %hdl
    icases HD $$ %dl %hdl with ⟨%fs, Hfi, %Hdl⟩
    iunfold filtersImpl at Hfi
    icases Hfi with ⟨%fps, #Hfps, %Hlen, -⟩
    ihave %Heq := ownSlice_agree _ _ _ _ _ $$ Hfps Hfcs
    subst Heq
    have hfs : fs = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen.symm)
    subst hfs
    ipureintro
    rw [Hdl]
    unfold filtered
    simp
  iexists γw, d
  iframe Hm
  ipureintro
  intro hd
  rw [HL.1, ← HL.2 hd]
  have hall : D.filter Deliv.sent = D := by
    rw [List.filter_eq_self]
    intro dl hdl
    simp only [Deliv.sent, Hkeep dl hdl, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases dl.1 <;> simp
  rw [hall]
  congr 1
  exact List.map_congr_left Hkeep

/-- **The responses' revisions and ids.** Every response a client received for the watcher `w`
is `w`'s, its revision is at or above its events' mod revisions, and if it has events it carries
`w`'s id. -/
theorem watchRecvOk_revs (γ : WsNames) (w : Loc) (rs : List RespM) :
    watchRecvOk (GF := GF) γ w rs ⊢
      ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs ∗
        ⌜∀ x ∈ rs, x.w = w ∧ (∀ ev ∈ x.evs, sint.Z ev.kv.modRev ≤ sint.Z x.rev) ∧
          (x.evs ≠ [] → x.id = r.id)⌝ := by
  iintro #Hok
  iunfold watchRecvOk at Hok
  icases Hok with ⟨%γw, %r, %fcs, %L, %D, %d, -, #Hf, -, %HL, -, #Hrs⟩
  iexists r, fcs
  iframe Hf
  iintro %x %hx
  icases Hrs $$ %x %hx with Hx
  iunfold respOk at Hx
  icases Hx with ⟨%Hrev, %rr, %fcs', #Hf', %Hid⟩
  have hxw := HL.2.2.2 x hx
  irevert Hf'; rw [hxw]; iintro #Hf'
  ihave %Hag := watcherFixed_agree w r rr fcs fcs' $$ [$Hf $Hf']
  obtain ⟨rfl, rfl⟩ := Hag
  ipureintro
  exact ⟨by first | rfl | exact hxw, Hrev, Hid⟩

end proof

end mvcc
end EtcdGrove
end Perennial
