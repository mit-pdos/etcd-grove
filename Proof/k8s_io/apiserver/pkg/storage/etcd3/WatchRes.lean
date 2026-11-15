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
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj] [Pos.Countable KRaw]

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

end k8s
end EtcdGrove
end Perennial
