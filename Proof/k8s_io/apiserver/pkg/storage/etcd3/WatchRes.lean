/-
Lean-first (no Rocq counterpart).

# The etcd3 watcher's `resultChan`: one invariant for the SPSC and its two producers (k8s 7f-5a-P)

`resultChan` has two producers that alternate under a protocol (`sendEvent` from the processing
goroutine, `sendError` from either goroutine), so the SPSC's producer token cannot be owned by a
thread: it lives in the producers' invariant `kResInv`. Perennial's `spsc_send_au` takes the token
before the send and `isSpsc`'s invariant is at `nroot`, so no other invariant can be open at the
commit (`notes/perennial-changes.md`, "The SPSC idiom has no send for a producer token kept in another
invariant"). Here:

- `spsc_send_au_inv`: a local copy of `spsc_send_au` over ONE invariant `inv nroot (spscInv γ P R ∗ X)`,
  whose token and element resource come from `X` at the commit (the accessor `Hacc`); the closed
  states are refuted by a resource `T` the sender keeps (`Hnc`: with `X`, it gives a producer token);
- `spsc_send_commit_inv`: the same, in the form `sendEvent`'s and `sendError`'s specs take (the abstract
  send commit `£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ, ▷ (Q -∗ Φ) -∗ sendAu γch v Φ`);
- `kResChan`: `resultChan`'s channel with that invariant, `X := kResInv ∨ kResClosed`; `kResChan_isSpsc`
  gives the consumer's `isSpsc` (`inv_split_l`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option maxHeartbeats 800000 in
/-- **An SPSC send whose producer token is in the invariant's other half `X`** (a copy of
Perennial's `spsc_send_au`, `Golang/Theory/Chan/Idioms/Spsc.lean`): at the commit, the accessor
`Hacc` takes the token and the element's `P` out of `X` (with the sender's `T`, which it may use to
refute a closed `X`) and, given the token one longer, gives back `X`, `T` and the sender's `Q`; after
the commit, the closed states are refuted by `T` and `X` (`Hnc`). -/
theorem spsc_send_au_inv (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (X T Q Φ : IProp GF) (v : V) :
    ⊢ isChan ch γ.chanName V -∗ inv nroot iprop(spscInv γ P R ∗ X) -∗
      □ (T -∗ X -∗ ∃ sent : List V, spscProducer γ sent) -∗
      £ 1 ∗ £ 1 ∗ £ 1 -∗ T -∗
      (T -∗ X ==∗ ∃ sent : List V, spscProducer γ sent ∗ P sent.length v ∗
        (spscProducer γ (sent ++ [v]) ==∗ X ∗ T ∗ Q)) -∗
      ▷ (T -∗ Q -∗ Φ) -∗ sendAu γ.chanName v Φ := by
  unfold sendAu
  iintro #Hchan #Hinv #Hnc ⟨Hlc1, Hlc2, Hlc3⟩ HT Hacc Hcont
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with ⟨Hi, HX⟩
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  imod Hacc $$ HT HX with ⟨%sent, Hprod, HP, Hback⟩
  unfold spscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    simp only [inflight] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves ((recv ++ buff) ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hback $$ Hprod with ⟨HX, HT, HQ⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hm HP HX] with -
    · inext
      isplitr [HX]
      · iapply spscInv_intro γ P R (.Buffered (buff ++ [v])) ((recv ++ buff) ++ [v]) recv
          (by simp [inflight]) $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        iapply spsc_push P recv buff v
        isplitl [Hm]
        · iexact Hm
        · iexact HP
      · iexact HX
    imodintro
    iapply Hcont $$ HT HQ
  | Idle =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hback $$ Hprod with ⟨HX, HT, HQ⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP HX] with -
    · inext
      isplitr [HX]
      · iapply spscInv_intro γ P R (.SndPending v) (sent ++ [v]) sent (by simp [inflight])
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        iexact HP
      · iexact HX
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc3 Hi with ⟨Hi, HX⟩
    icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent1, %recv1, Hch, HsentI, HrecvI, %Hrel, Hm⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | RcvCommit =>
      dsimp only
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI HX] with -
      · inext
        isplitr [HX]
        · iapply spscInv_intro γ P R .Idle sent1 recv1 (by simpa [inflight] using Hrel)
            $$ Hoc HsentI HrecvI
          simp only [spscInvMatch]
          itrivial
        · iexact HX
      imodintro
      iapply Hcont $$ HT HQ
    | Closed d =>
      dsimp only
      icases Hnc $$ HT HX with ⟨%sent2, Hp3⟩
      cases d with
      | nil =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨Hp2, -⟩
        iapply dghostVar_three_halves $$ Hp3 HsentI Hp2
      | cons _ _ =>
        simp only [spscInvMatch, spscProducer]
        icases Hm with ⟨-, Hp2, -⟩
        iapply dghostVar_three_halves $$ Hp3 HsentI Hp2
    | _ => itrivial
  | RcvPending =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hback $$ Hprod with ⟨HX, HT, HQ⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP HX] with -
    · inext
      isplitr [HX]
      · iapply spscInv_intro γ P R (.SndCommit v) (sent ++ [v]) sent (by simp [inflight])
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        iexact HP
      · iexact HX
    imodintro
    iapply Hcont $$ HT HQ
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

/-- **The abstract send commit** (`sendEvent`'s and `sendError`'s `Hsend`) from the shared invariant:
`T` comes back with `Q`. -/
theorem spsc_send_commit_inv (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (X T Q : IProp GF) (v : V) :
    ⊢ isChan ch γ.chanName V -∗ inv nroot iprop(spscInv γ P R ∗ X) -∗
      □ (T -∗ X -∗ ∃ sent : List V, spscProducer γ sent) -∗ T -∗
      (T -∗ X ==∗ ∃ sent : List V, spscProducer γ sent ∗ P sent.length v ∗
        (spscProducer γ (sent ++ [v]) ==∗ X ∗ T ∗ Q)) -∗
      (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (T ∗ Q -∗ Φ) -∗ sendAu γ.chanName v Φ) := by
  iintro #Hchan #Hinv #Hnc HT Hacc Hlc %Φ Hcont
  iapply spsc_send_au_inv γ ch P R X T Q Φ v $$ Hchan Hinv Hnc Hlc HT Hacc
  inext
  iintro HT HQ
  iapply Hcont
  isplitl [HT]
  · iexact HT
  · iexact HQ

end send

section chan
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj]

/-- **A producer of `resultChan` is still running** (`alive`'s fraction `q`, value `false`): each of
the two goroutines that may send holds one until it exits; `run`, after `resultChanWG.Wait()`, holds
them all and closes the channel. -/
def kResAlive (alive : GName) (q : Qp) : IProp GF := dghostVar alive (DFrac.own q) false

/-- **`resultChan` is closed** (`run`'s, after both producers exited): the full `alive`, value `true`;
the producer token is then parked in the SPSC invariant. -/
def kResClosed (alive : GName) : IProp GF := dghostVar alive (DFrac.own 1) true

/-- **`resultChan`**: the channel, and ONE invariant holding the SPSC's state with the consumer's
element `kResElem`, and the producers' `kResInv` (or, once closed, `kResClosed`). The consumer's
`isSpsc` is its first half (`kResChan_isSpsc`); the producers send through `spsc_send_commit_inv`. -/
def kResChan (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ch : Loc) : IProp GF :=
  iprop(isChan ch γ.res.chanName k8s_io.apimachinery.pkg.watch.Event ∗
    inv nroot iprop(spscInv γ.res (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True)) ∗
      (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive)))

instance kResChan_persistent (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ch : Loc) :
    Persistent (kResChan c W γ cd sel emp inS m Q procd alive ch) := by
  unfold kResChan; infer_instance

/-- The consumer's view of `resultChan`. -/
theorem kResChan_isSpsc (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ch : Loc) :
    kResChan c W γ cd sel emp inS m Q procd alive ch ⊢
      isSpsc γ.res ch (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True)) := by
  unfold kResChan isSpsc
  iintro ⟨#Hch, #Hinv⟩
  isplitl
  · iexact Hch
  · iapply inv_split_l $$ Hinv

/-- A running producer and a closed channel exclude each other. -/
theorem kResAlive_closed (alive : GName) (q : Qp) :
    kResAlive (GF := GF) alive q ∗ kResClosed alive ⊢ False := by
  unfold kResAlive kResClosed
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hv
  exfalso
  obtain ⟨Hv, -⟩ := Hv
  revert Hv
  simp only [CMRA.Valid, DFrac.op_own]
  intro h
  have h1 : (q : Rat) + 1 ≤ 1 := h
  have h2 : (0 : Rat) < q := q.2
  grind

/-- **The closed states are refuted by a running producer** (`spsc_send_au_inv`'s `Hnc`). -/
theorem kResChan_nc (c : StoreCfg GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (q : Qp) :
    ⊢ □ (kResAlive alive q -∗ (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) -∗
      ∃ sent : List k8s_io.apimachinery.pkg.watch.Event, spscProducer γ.res sent) := by
  iintro !> HT (HI | HC)
  · unfold kResInv
    icases HI with ⟨%sent, %evs, %raws, %σ, Hp, -⟩
    iexists sent
    iexact Hp
  · iexfalso
    iapply kResAlive_closed $$ [$HT $HC]

end chan

/-! ## `kResInv`'s ghost steps -/

section steps
variable [GooseExts]
variable {Obj : Type}

/-- The events sent have types at most 4: the non-error ones are transforms (`kRawToEv_t`). -/
theorem kEvs_types (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState)
    (evs : List (KWEv Obj)) (raws : List KRaw)
    (h : kNonErr evs = raws.filterMap (kRawToEv dec sel emp z σ)) : ∀ e ∈ evs, e.t ≤ 4 := by
  intro e he
  by_cases ht : e.t = 4
  · omega
  · have hm : e ∈ kNonErr evs := by unfold kNonErr; simp [List.mem_filter, he, ht]
    rw [h, List.mem_filterMap] at hm
    obtain ⟨r, -, hr⟩ := hm
    have := kRawToEv_t dec sel emp z σ r e hr
    omega

/-- An Error event leaves the non-error part unchanged. -/
theorem kNonErr_append_err (evs : List (KWEv Obj)) (e : KWEv Obj) (h : e.t = 4) :
    kNonErr (evs ++ [e]) = kNonErr evs := by
  unfold kNonErr; simp [List.filter_append, h]

/-- A transform is not an Error event: appending it appends to the non-error part. -/
theorem kNonErr_append_ev (evs : List (KWEv Obj)) (e : KWEv Obj) (h : e.t ≤ 3) :
    kNonErr (evs ++ [e]) = kNonErr evs ++ [e] := by
  unfold kNonErr; simp [List.filter_append]; omega

/-- **The processing goroutine's step, pure part**: `kResInv`'s equation at `σ` for the raw events
taken so far, and the next raw event `r` received with the facts of `raws ++ [r]` at its state `σr`
(one history), give the equation for `raws ++ [r]` and the events sent so far with `r`'s transform
appended (`oe`: `none` when filtered out), at the later of the two states, with the element's facts
carried there. -/
theorem kRes_step_pure (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj)
    (inS : GoString → Bool) (m : KWatchMode) (σ σr : KVState) (h : kvSameHist σ σr)
    (evs : List (KWEv Obj)) (raws : List KRaw) (r : KRaw) (st : Nat) (oe : Option (KWEv Obj))
    (Heq : kNonErr evs = raws.filterMap (kRawToEv dec sel emp z σ))
    (Hraws : raws = [] ∨ ∀ x ∈ raws, kRawRevOk σ x)
    (Hsub : kRawStreamSub inS m σr st (raws ++ [r]))
    (hoe : kRawToEv dec sel emp z σr r = oe) :
    ∃ σ', (σ' = σ ∨ σ' = σr) ∧
      kNonErr (evs ++ oe.toList) = (raws ++ [r]).filterMap (kRawToEv dec sel emp z σ') ∧
      kRawStreamSub inS m σ' st (raws ++ [r]) ∧
      (kRawStreamOk inS m σr st (raws ++ [r]) → kRawStreamOk inS m σ' st (raws ++ [r])) := by
  have hrev := kRawStreamSub_revOk Hsub
  have hne : kNonErr (evs ++ oe.toList) = kNonErr evs ++ oe.toList := by
    cases oe with
    | none => simp
    | some e =>
      simp only [Option.toList_some]
      exact kNonErr_append_ev evs e (kRawToEv_t dec sel emp z σr r e hoe)
  by_cases hle : σ.rev ≤ σr.rev
  · refine ⟨σr, Or.inr rfl, ?_, Hsub, id⟩
    rw [hne, Heq, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, hoe]
    congr 1
    · rcases Hraws with rfl | hx
      · rfl
      · exact kRawToEv_filterMap_hist dec sel emp z σ σr h hle raws hx
  · have hle' : σr.rev ≤ σ.rev := by omega
    have h' := kvSameHist_symm h
    refine ⟨σ, Or.inl rfl, ?_, kRawStreamRel_hist h' hle' Hsub,
      fun hok => kRawStreamRel_hist h' hle' hok⟩
    rw [hne, Heq, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      ← kRawToEv_hist dec sel emp z σr σ h' hle' r (hrev r (by simp)), hoe]
    cases oe <;> rfl

end steps

section stepsI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj]

/-- A lower bound of a mono list gives each of its elements at its index. -/
theorem monoList_lb_idx_all {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListLbOwn (GF := GF) γ l ⊢ [∗list] j ↦ a ∈ l, monoListIdxOwn γ j a :=
  by
    iintro #H
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %x %h
    iapply monoListIdxOwn_get k x h $$ H

/-- Elements at every index of `L` below a lower bound `l` at least as long: `L` is a prefix of `l`. -/
theorem monoList_idx_prefix {A : Type} [Pos.Countable A] (γ : GName) (l : List A) (L : List A) :
    L.length ≤ l.length →
      monoListLbOwn (GF := GF) γ l ⊢ ([∗list] j ↦ x ∈ L, monoListIdxOwn γ j x) -∗ ⌜L <+: l⌝ := by
  induction hn : L.length generalizing L with
  | zero =>
    intro _
    rw [List.length_eq_zero_iff.1 hn]
    iintro _ _; ipureintro; exact List.nil_prefix
  | succ n ih =>
    intro hlen
    have hne : L ≠ [] := by intro h; subst h; simp at hn
    rw [← List.dropLast_concat_getLast hne]
    generalize L.getLast hne = a
    have hn' : L.dropLast.length = n := by simp [List.length_dropLast, hn]
    generalize L.dropLast = L' at hn' ⊢
    iintro #Hlb Hbig
    icases BigSepL.bigSepL_snoc.1 $$ Hbig with ⟨Hbig, Ha⟩
    ihave %Hp := ih L' hn' (by omega) $$ Hlb Hbig
    ihave %Hg := mono_list_lb_idx_lookup γ l L'.length a (by omega) $$ Hlb Ha
    ipureintro
    rw [List.prefix_iff_eq_take] at Hp ⊢
    rw [List.length_append, List.length_singleton, List.take_add_one, ← Hp, Hg]
    rfl

/-- **A received element's raw events and `kResInv`'s**: a lower bound `raws` of the same length as
the element's `raws'` (the processing goroutine's count, `procd`) is `raws'`, and the element's
indices give the lower bound `raws' ++ [r]`. -/
theorem monoList_idx_lb_snoc {A : Type} [Pos.Countable A] (γ : GName) (raws raws' : List A) (r : A)
    (hlen : raws.length = raws'.length) :
    monoListLbOwn (GF := GF) γ raws ⊢ ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ j x) -∗
      ⌜raws = raws'⌝ ∗ monoListLbOwn γ (raws' ++ [r]) := by
  iintro #Hlb #Hbig
  ihave Hr : monoListIdxOwn γ raws'.length r $$ [Hbig]
  · icases BigSepL.bigSepL_snoc.1 $$ Hbig with ⟨-, Ha⟩
    iexact Ha
  iunfold monoListIdxOwn at Hr
  icases Hr with ⟨%l, %Hl, #Hl⟩
  have hll : (raws' ++ [r]).length ≤ l.length := by
    have := (List.getElem?_eq_some_iff.1 Hl).1
    simp; omega
  ihave %Hp := monoList_idx_prefix γ l (raws' ++ [r]) hll $$ Hl Hbig
  ihave #Hlb' := monoListLbOwn_le (raws' ++ [r]) Hp $$ Hl
  ihave %Hc := mono_list_lb_valid γ raws (raws' ++ [r]) $$ Hlb Hlb'
  isplitr
  · ipureintro
    rcases Hc with Hc | Hc
    · rw [List.prefix_iff_eq_take] at Hc
      rw [Hc, hlen]; simp
    · have := Hc.length_le; simp at this; omega
  · iexact Hlb'

/-- **The ghost step of an Error event** (`sendError`, from either goroutine): a running producer
(`kResAlive`) sends an Error event `v` (type `ERROR`, a failure status): the element is `kResElem`'s
at the next index (its model `⟨4, z, 0, false⟩`; the stream facts are the raw events' so far, the
Error event adding nothing to the non-error part), and `kResInv` takes the event. -/
theorem kResInv_err_acc (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (q : Qp)
    (v : k8s_io.apimachinery.pkg.watch.Event) (hv : v.Type' = go!"ERROR") :
    ⊢ statusFailureAt v.Object' -∗ kResAlive alive q -∗
      (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ==∗
      ∃ sent : List k8s_io.apimachinery.pkg.watch.Event, spscProducer γ.res sent ∗
        kResElem c W γ cd sel emp inS m Q (sent.length : Int) v ∗
        (spscProducer γ.res (sent ++ [v]) ==∗
          (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ∗ kResAlive alive q ∗ emp) := by
  iintro Hst HT HX
  unfold kResInv
  icases HX with (HI | HC)
  · icases HI with ⟨%sent, %evs, %raws, %σ, Hp, Hauth, %Hlen, Hprocd, #Hlb, %Heq, #Hf⟩
    let e : KWEv Obj := ⟨4, c.S.zero, 0, false⟩
    have he4 : e.t = 4 := rfl
    have Heq' : kNonErr (evs ++ [e]) = raws.filterMap (kRawToEv c.S.dec sel emp c.S.zero σ) := by
      rw [kNonErr_append_err evs e he4, Heq]
    have Hty : ∀ x ∈ evs ++ [e], x.t ≤ 4 := kEvs_types _ _ _ _ _ _ _ Heq'
    imod monoListAuthOwn_update_app [e] $$ Hauth with ⟨Hauth, #Hlb'⟩
    imodintro
    iexists sent
    isplitl [Hp]
    · iexact Hp
    isplitr [Hauth Hprocd HT]
    · unfold kResElem
      iexists e, evs
      isplitl [Hst]
      · unfold wevAt
        simp only [he4, ↓reduceIte]
        isplitr
        · ipureintro; exact hv
        · iexact Hst
      isplitr
      · ipureintro; simp [Hlen]
      isplitr
      · iapply monoList_lb_idx_all $$ Hlb'
      icases Hf with (%Hnil | ⟨%lb, %lb0, %st, %σ0, #HQ, #HQ0, %Hst0, %Hsub, #Hok⟩)
      · ileft; ipureintro
        rw [Heq', Hnil]; rfl
      · iright
        iexists lb, lb0, st, σ, σ0
        isplitr; · iexact HQ
        isplitr; · iexact HQ0
        isplitr; · ipureintro; exact Hst0
        isplitr
        · ipureintro
          exact kStreamSub_of_raw _ _ _ _ _ _ _ _ _ _ Hsub Heq' Hty
        icases Hok with (%Hok | #Hc)
        · ileft; ipureintro
          exact kStreamOk_of_raw _ _ _ _ _ _ _ _ _ _ Hok Heq' Hty
        · iright; iexact Hc
    · iintro Hp
      imodintro
      isplitl [Hp Hauth Hprocd]
      · ileft
        iexists sent ++ [v], evs ++ [e], raws, σ
        isplitl [Hp]; · iexact Hp
        isplitl [Hauth]; · iexact Hauth
        isplitr; · ipureintro; simp [Hlen]
        isplitl [Hprocd]; · iexact Hprocd
        isplitr; · iexact Hlb
        isplitr; · ipureintro; exact Heq'
        iexact Hf
      isplitl [HT]
      · iexact HT
      · iempintro

  · iexfalso
    iapply kResAlive_closed $$ [$HT $HC]

/-- The processing goroutine, still running (`procEx`'s fraction at `false`), refutes `kProcExited`
in a received element's no-gap fact. -/
theorem kProcExited_refute (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (q : Qp)
    (P : Prop) :
    ⊢ dghostVar (GF := GF) γ.procEx (DFrac.own q) false -∗ (⌜P⌝ ∨ kCancelled γ cd ∨ kProcExited γ) -∗
      dghostVar γ.procEx (DFrac.own q) false ∗ (⌜P⌝ ∨ kCancelled γ cd) := by
  iintro Hd Hor
  icases Hor with (%HP | #Hc | #He)
  · isplitl [Hd]; · iexact Hd
    ileft; ipureintro; exact HP
  · isplitl [Hd]; · iexact Hd
    iright; iexact Hc
  · unfold kProcExited
    ihave %Hab := dghostVar_agree _ _ _ _ _ $$ Hd He
    exact absurd Hab (by decide)

theorem kvSameHist_refl (σ : KVState) : kvSameHist σ σ := ⟨rfl, rfl, Or.inl (List.prefix_refl _)⟩

/-- **The processing goroutine's step on a received raw event** (pure and ghost part, inside
`kResChan`'s invariant): the goroutine's half of `procd` at `n`, the received element's facts (its
raw events `raws' ++ [r]` with `raws'.length = n`, read at `σr`, `□ Q lbr σr`, the start point, the
subsequence and, `kProcExited` refuted, the prefix-or-cancelled fact), and `oe`, the raw event's
transform at `σr`. With `kResInv` (a closed channel is refuted by `kResAlive`), `procd` agrees: the
raw events taken so far are `raws'`; the sent events' non-error part, with `oe` appended, is the
transform of `raws' ++ [r]` at the later of `kResInv`'s state and `σr` (one history, by `Hhist`).
Gives that state `σ'` with its `□ Q`, the new lower bound of the raw events, and the updated
`kResInv` once the events `evs ++ oe.toList` are recorded: the caller chooses to send (`oe = some e`,
`kResInv_send_acc`) or not (`kResInv_filter`). -/
theorem kResInv_step (c : StoreCfg GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd : GName) (n : Nat)
    (r : KRaw) (raws' : List KRaw) (lbr lb0 st : Nat) (σr σ0 : KVState) (oe : Option (KWEv Obj))
    (hlen : raws'.length = n)
    (hsub : kRawStreamSub inS m σr st (raws' ++ [r]))
    (hoe : kRawToEv c.S.dec sel emp c.S.zero σr r = oe) :
    ⊢ □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) -∗
      dghostVar procd (DFrac.own (1 : Qp).half) n -∗
      ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ.raws j x) -∗
      □ Q lbr σr -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σr st (raws' ++ [r])⌝ ∨ kCancelled γ cd) -∗
      kResInv c γ cd sel emp inS m Q procd ==∗
      ∃ (sent : List k8s_io.apimachinery.pkg.watch.Event) (evs : List (KWEv Obj)) (σ' : KVState)
        (lb' : Nat),
        spscProducer γ.res sent ∗ monoListAuthOwn γ.evs (1 : Qp) evs ∗ ⌜sent.length = evs.length⌝ ∗
        dghostVar procd (DFrac.own (1 : Qp).half) (n + 1) ∗
        dghostVar procd (DFrac.own (1 : Qp).half) (n + 1) ∗
        monoListLbOwn γ.raws (raws' ++ [r]) ∗ □ Q lb' σ' ∗
        ⌜kNonErr (evs ++ oe.toList) = (raws' ++ [r]).filterMap
          (kRawToEv c.S.dec sel emp c.S.zero σ')⌝ ∗
        ⌜kRawStreamSub inS m σ' st (raws' ++ [r])⌝ ∗
        (⌜kRawStreamOk inS m σ' st (raws' ++ [r])⌝ ∨ kCancelled γ cd) := by
  iintro #Hhist Hd #Hbig #HQr #HQ0 Hok HI
  unfold kResInv
  icases HI with ⟨%sent, %evs, %raws, %σ, Hp, Hauth, %Hlen, Hprocd, #Hlb, %Heq, #Hf⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hprocd Hd
  ihave ⟨%Hr, #Hlb'⟩ := monoList_idx_lb_snoc γ.raws raws raws' r (by omega) $$ Hlb Hbig
  subst Hr
  imod dghostVar_update_halves (n + 1) procd _ _ $$ Hprocd Hd with ⟨Hd1, Hd2⟩
  -- the state before: kResInv's when it holds raw events, else `σr` itself
  ihave Hb : ∃ (σb : KVState) (lbb : Nat), □ Q lbb σb ∗
      ⌜kvSameHist σb σr⌝ ∗
      ⌜kNonErr evs = raws.filterMap (kRawToEv c.S.dec sel emp c.S.zero σb)⌝ ∗
      ⌜raws = [] ∨ ∀ x ∈ raws, kRawRevOk σb x⌝ $$ []
  · icases Hf with (%Hnil | ⟨%lb, %lb0', %st', %σ0', #HQ, #HQ0', %Hst', %Hsub', #Hok'⟩)
    · iexists σr, lbr
      isplitr; · iexact HQr
      ipureintro
      refine ⟨kvSameHist_refl σr, ?_, Or.inl Hnil⟩
      rw [Heq, Hnil]; rfl
    · iexists σ, lb
      isplitr; · iexact HQ
      ihave %Hh := Hhist $$ HQ HQr
      ipureintro
      exact ⟨Hh, Heq, Or.inr (kRawStreamSub_revOk Hsub')⟩
  icases Hb with ⟨%σb, %lbb, #HQb, %Hhb, %Heqb, %Hrawsb⟩
  obtain ⟨σ', hσ', Heq', Hsub', Hok'⟩ :=
    kRes_step_pure c.S.dec sel emp c.S.zero inS m σb σr Hhb evs raws r st oe Heqb Hrawsb hsub hoe
  imodintro
  iexists sent, evs, σ'
  ihave HQ'' : ∃ lb' : Nat, □ Q lb' σ' $$ []
  · rcases hσ' with rfl | rfl
    · iexists lbb; iexact HQb
    · iexists lbr; iexact HQr
  icases HQ'' with ⟨%lb', #HQ'⟩
  iexists lb'
  isplitl [Hp]; · iexact Hp
  isplitl [Hauth]; · iexact Hauth
  isplitr; · ipureintro; exact Hlen
  isplitl [Hd1]; · iexact Hd1
  isplitl [Hd2]; · iexact Hd2
  isplitr; · iexact Hlb'
  isplitr; · iexact HQ'
  isplitr; · ipureintro; exact Heq'
  isplitr; · ipureintro; exact Hsub'
  icases Hok with (%Hok | #Hc)
  · ileft; ipureintro; exact Hok' Hok
  · iright; iexact Hc


/-- **The processing goroutine's send** (`sendEvent`'s commit, `spsc_send_commit_inv`'s accessor with
`T := kResAlive alive q`): the received element's facts (`kResInv_step`'s), its transform `e` at
`σr`, and the event `v` holding it (`wevAt`): the element sent is `kResElem`'s at the next index, and
after the send `kResInv` holds `raws' ++ [r]` and `evs ++ [e]`, the goroutine's half of `procd` at
`n + 1`. -/
theorem kResInv_send_acc (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (q : Qp) (n : Nat)
    (r : KRaw) (raws' : List KRaw) (lbr lb0 st : Nat) (σr σ0 : KVState) (e : KWEv Obj)
    (v : k8s_io.apimachinery.pkg.watch.Event)
    (hlen : raws'.length = n) (hst : kStartOk m σ0 st)
    (hsub : kRawStreamSub inS m σr st (raws' ++ [r]))
    (he : kRawToEv c.S.dec sel emp c.S.zero σr r = some e) :
    ⊢ □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) -∗
      dghostVar procd (DFrac.own (1 : Qp).half) n -∗
      ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ.raws j x) -∗
      □ Q lbr σr -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σr st (raws' ++ [r])⌝ ∨ kCancelled γ cd) -∗
      wevAt c.S W v e -∗
      kResAlive alive q -∗ (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ==∗
      ∃ sent : List k8s_io.apimachinery.pkg.watch.Event, spscProducer γ.res sent ∗
        kResElem c W γ cd sel emp inS m Q (sent.length : Int) v ∗
        (spscProducer γ.res (sent ++ [v]) ==∗
          (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ∗ kResAlive alive q ∗
            dghostVar procd (DFrac.own (1 : Qp).half) (n + 1)) := by
  iintro #Hhist Hd #Hbig #HQr #HQ0 Hok Hw HT HX
  icases HX with (HI | HC)
  · imod kResInv_step c γ cd sel emp inS m Q procd n r raws' lbr lb0 st σr σ0 (some e) hlen
      hsub he $$ Hhist Hd Hbig HQr HQ0 Hok HI
      with ⟨%sent, %evs, %σ', %lb', Hp, Hauth, %Hlen, Hd1, Hd2, #Hlb', #HQ', %Heq', %Hsub', #Hok'⟩
    simp only [Option.toList_some] at Heq'
    have Hty : ∀ x ∈ evs ++ [e], x.t ≤ 4 := kEvs_types _ _ _ _ _ _ _ Heq'
    imod monoListAuthOwn_update_app [e] $$ Hauth with ⟨Hauth, #Hevs⟩
    imodintro
    iexists sent
    isplitl [Hp]; · iexact Hp
    isplitl [Hw]
    · unfold kResElem
      iexists e, evs
      isplitl [Hw]; · iexact Hw
      isplitr; · ipureintro; simp [Hlen]
      isplitr; · iapply monoList_lb_idx_all $$ Hevs
      iright
      iexists lb', lb0, st, σ', σ0
      isplitr; · iexact HQ'
      isplitr; · iexact HQ0
      isplitr; · ipureintro; exact hst
      isplitr
      · ipureintro; exact kStreamSub_of_raw _ _ _ _ _ _ _ _ _ _ Hsub' Heq' Hty
      icases Hok' with (%Hok' | #Hc)
      · ileft; ipureintro; exact kStreamOk_of_raw _ _ _ _ _ _ _ _ _ _ Hok' Heq' Hty
      · iright; iexact Hc
    · iintro Hp
      imodintro
      isplitl [Hp Hauth Hd1]
      · ileft
        unfold kResInv
        iexists sent ++ [v], evs ++ [e], raws' ++ [r], σ'
        isplitl [Hp]; · iexact Hp
        isplitl [Hauth]; · iexact Hauth
        isplitr; · ipureintro; simp [Hlen]
        isplitl [Hd1]; · simp only [List.length_append, List.length_singleton, hlen]; iexact Hd1
        isplitr; · iexact Hlb'
        isplitr; · ipureintro; exact Heq'
        iright
        iexists lb', lb0, st, σ0
        isplitr; · iexact HQ'
        isplitr; · iexact HQ0
        isplitr; · ipureintro; exact hst
        isplitr; · ipureintro; exact Hsub'
        iexact Hok'
      isplitl [HT]; · iexact HT
      iexact Hd2
  · iexfalso
    iapply kResAlive_closed $$ [$HT $HC]

/-- **The processing goroutine's filtered raw event** (no send: `transform` gave `nil`): a ghost step
inside `kResChan`'s invariant, `kResInv` taking `raws' ++ [r]` with the events unchanged, the
goroutine's half of `procd` at `n + 1`. -/
theorem kResInv_filter (c : StoreCfg GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (q : Qp) (n : Nat)
    (r : KRaw) (raws' : List KRaw) (lbr lb0 st : Nat) (σr σ0 : KVState)
    (hlen : raws'.length = n) (hst : kStartOk m σ0 st)
    (hsub : kRawStreamSub inS m σr st (raws' ++ [r]))
    (hnone : kRawToEv c.S.dec sel emp c.S.zero σr r = none) :
    ⊢ □ (∀ (l l' : Nat) (s s' : KVState), Q l s -∗ Q l' s' -∗ ⌜kvSameHist s s'⌝) -∗
      dghostVar procd (DFrac.own (1 : Qp).half) n -∗
      ([∗list] j ↦ x ∈ raws' ++ [r], monoListIdxOwn γ.raws j x) -∗
      □ Q lbr σr -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σr st (raws' ++ [r])⌝ ∨ kCancelled γ cd) -∗
      kResAlive alive q -∗ (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ==∗
      (kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) ∗ kResAlive alive q ∗
        dghostVar procd (DFrac.own (1 : Qp).half) (n + 1) := by
  iintro #Hhist Hd #Hbig #HQr #HQ0 Hok HT HX
  icases HX with (HI | HC)
  · imod kResInv_step c γ cd sel emp inS m Q procd n r raws' lbr lb0 st σr σ0 none hlen
      hsub hnone $$ Hhist Hd Hbig HQr HQ0 Hok HI
      with ⟨%sent, %evs, %σ', %lb', Hp, Hauth, %Hlen, Hd1, Hd2, #Hlb', #HQ', %Heq', %Hsub', #Hok'⟩
    simp only [Option.toList_none, List.append_nil] at Heq'
    imodintro
    isplitl [Hp Hauth Hd1]
    · ileft
      unfold kResInv
      iexists sent, evs, raws' ++ [r], σ'
      isplitl [Hp]; · iexact Hp
      isplitl [Hauth]; · iexact Hauth
      isplitr; · ipureintro; exact Hlen
      isplitl [Hd1]; · simp only [List.length_append, List.length_singleton, hlen]; iexact Hd1
      isplitr; · iexact Hlb'
      isplitr; · ipureintro; exact Heq'
      iright
      iexists lb', lb0, st, σ0
      isplitr; · iexact HQ'
      isplitr; · iexact HQ0
      isplitr; · ipureintro; exact hst
      isplitr; · ipureintro; exact Hsub'
      iexact Hok'
    isplitl [HT]; · iexact HT
    iexact Hd2
  · iexfalso
    iapply kResAlive_closed $$ [$HT $HC]

end stepsI

end k8s
end EtcdGrove
end Perennial
