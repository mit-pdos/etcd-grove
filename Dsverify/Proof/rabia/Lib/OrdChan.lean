/-
An ordered multi-producer, single-consumer channel idiom (interface, stage 1b; a library in the
style of Perennial's `Spsc.lean`): `np` producers, each sending in order; the consumer learns,
for each value it receives, which producer sent it and its index among that producer's values
(a Go channel is FIFO, so each producer's values arrive in its order). The values' predicate
`P i n v` is producer `i`'s `n`-th value's. The channel is never closed.

Used where Rabia needs per-sender order through a channel with several senders: the network
layer's `RecvChan` (the receive routines of the three peers' connections) and each `SendChan[j]`
(the serializer's broadcasts, in their order, and the router's replies).

(dsv-rabia, notes/dsv-rabia.md: the lab's `Proof/Lib/OrdChan.lean` at proof `2a8c0fc`; changed: the
channel idioms' atomic updates are crash-aware fancy updates at Perennial `9c3b81f3`, so each proof of a
`sendAu`/`recvAu`/nested update starts with `ncfupd_of_fupd`.)
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- The ghost names of an ordered channel. -/
structure OrdNames where
  chanName : ChanNames
  prod : GName
  cons : GName

/-! ### The pure part of the invariant (internal) -/

/-- The values in flight in channel state `s` (the channel is never closed). -/
def ordInflight {V : Type} (s : ChanState V) : List V :=
  match s with
  | .Buffered b => b
  | .SndPending v | .SndCommit v => [v]
  | _ => []

/-- The channel is not closed. -/
def ordStateOk {V : Type} (s : ChanState V) : Prop :=
  match s with
  | .Closed _ => False
  | _ => True

/-- The tags in flight `(producer, index)`, starting from the consumer's counts `f`: each
producer's tags are consecutive from its count. -/
def ordConsec : List Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | f, (i, n) :: r => n = f.getD i 0 ∧ i < f.length ∧ ordConsec (f.set i (f.getD i 0 + 1)) r

/-- The counts after the tags in flight are received. -/
def ordFin : List Nat → List (Nat × Nat) → List Nat
  | f, [] => f
  | f, (i, _) :: r => ordFin (f.set i (f.getD i 0 + 1)) r

theorem ordFin_length (f : List Nat) (tags : List (Nat × Nat)) :
    (ordFin f tags).length = f.length := by
  induction tags generalizing f with
  | nil => rfl
  | cons t r ih => obtain ⟨i, n⟩ := t; simp [ordFin, ih]

theorem ordFin_snoc (f : List Nat) (tags : List (Nat × Nat)) (i n : Nat) :
    ordFin f (tags ++ [(i, n)]) = (ordFin f tags).set i ((ordFin f tags).getD i 0 + 1) := by
  induction tags generalizing f with
  | nil => rfl
  | cons t r ih => obtain ⟨j, k⟩ := t; simp [ordFin, ih]

theorem ordConsec_snoc (f : List Nat) (tags : List (Nat × Nat)) (i n : Nat) :
    ordConsec f (tags ++ [(i, n)]) ↔
      ordConsec f tags ∧ n = (ordFin f tags).getD i 0 ∧ i < (ordFin f tags).length := by
  induction tags generalizing f with
  | nil => simp [ordConsec, ordFin]
  | cons t r ih => obtain ⟨j, k⟩ := t; simp only [List.cons_append, ordConsec, ordFin, ih, and_assoc]

/-- The pure part of the invariant: state `s`, consumer counts `f`, producer counts `m`,
tags in flight `tags`. -/
def ordOk {V : Type} (np : Nat) (s : ChanState V) (f : List Nat) (m : GMap Nat Nat)
    (tags : List (Nat × Nat)) : Prop :=
  ordStateOk s ∧ f.length = np ∧ tags.length = (ordInflight s).length ∧ ordConsec f tags ∧
    ∀ i, m.lookup i = if i < np then some ((ordFin f tags).getD i 0) else none

theorem ordOk_pop {V : Type} {np : Nat} {s s' : ChanState V} {f : List Nat} {m : GMap Nat Nat}
    {tags : List (Nat × Nat)} {v : V} (h : ordOk np s f m tags)
    (hs : ordInflight s = v :: ordInflight s') (hs' : ordStateOk s') :
    ∃ i n tr, tags = (i, n) :: tr ∧ i < np ∧ n = f.getD i 0 ∧
      ordOk np s' (f.set i (f.getD i 0 + 1)) m tr := by
  obtain ⟨-, hf, hl, hc, hm⟩ := h
  rw [hs] at hl
  match tags, hl, hc, hm with
  | (i, n) :: tr, hl, hc, hm =>
    obtain ⟨hn, hi, hc⟩ := hc
    refine ⟨i, n, tr, rfl, hf ▸ hi, hn, hs', by simpa using hf, by simpa using hl, hc, ?_⟩
    simpa [ordFin] using hm

theorem ordOk_push {V : Type} {np : Nat} {s s' : ChanState V} {f : List Nat} {m : GMap Nat Nat}
    {tags : List (Nat × Nat)} {v : V} {i n : Nat} (h : ordOk np s f m tags)
    (hmi : m.lookup i = some n)
    (hs : ordInflight s' = ordInflight s ++ [v]) (hs' : ordStateOk s') :
    i < np ∧ ordOk np s' f (m.insert i (n + 1)) (tags ++ [(i, n)]) := by
  obtain ⟨-, hf, hl, hc, hm⟩ := h
  have hmi' := hm i
  rw [hmi] at hmi'
  have hi : i < np := by
    by_cases hc' : i < np
    · exact hc'
    · simp [hc'] at hmi'
  simp only [hi, ite_true, Option.some.injEq] at hmi'
  have hlen : i < (ordFin f tags).length := by rw [ordFin_length]; omega
  refine ⟨hi, hs', hf, by simp [hs, hl], (ordConsec_snoc f tags i n).2 ⟨hc, hmi', hlen⟩, ?_⟩
  intro j
  rw [ordFin_snoc]
  by_cases hij : i = j
  · subst hij
    simp [GMap.insert, hi, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
    simp [List.getD_eq_getElem?_getD] at hmi'
    exact hmi'
  · have := hm j
    simp [GMap.insert, hij, this, List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

section ord
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- Producer `i` has sent `n` values (exclusive). -/
def ordProd (γ : OrdNames) (i n : Nat) : IProp GF := (i ↪[γ.prod] n : IProp GF)
/-- The consumer has received `f[i]` values from each producer `i` (exclusive). -/
def ordCons (γ : OrdNames) (f : List Nat) : IProp GF :=
  dghostVar γ.cons (DFrac.own (1 : Qp).half) f

/-- The invariant (internal): the channel's state `s`, the consumer's counts `f` (the other half
of `ordCons`), the producers' counts `m` (the authority over `ordProd`), and the tags
`(producer, index)` of the values in flight, which carry `P`. -/
@[irreducible] def ordInv (γ : OrdNames) (np : Nat) (P : Nat → Nat → V → IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V) (f : List Nat) (m : GMap Nat Nat) (tags : List (Nat × Nat)),
    ownChan γ.chanName V s ∗ dghostVar γ.cons (DFrac.own (1 : Qp).half) f ∗
    ghostMapAuth γ.prod 1 m ∗ ⌜ordOk np s f m tags⌝ ∗
    [∗list] p ∈ tags.zip (ordInflight s), P p.1.1 p.1.2 p.2)

/-- The channel `ch` with `np` producers and the values' predicate `P` (persistent). -/
def isOrdChan (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF) : IProp GF :=
  iprop(isChan ch γ.chanName V ∗ inv nroot (ordInv γ np P))

instance isOrdChan_persistent (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF) :
    Persistent (isOrdChan γ ch np P) := by
  unfold isOrdChan; infer_instance

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem ordInv_intro (γ : OrdNames) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (s : ChanState V) (f : List Nat) (m : GMap Nat Nat) (tags : List (Nat × Nat))
    (h : ordOk np s f m tags) :
    ⊢ ownChan γ.chanName V s -∗ dghostVar γ.cons (DFrac.own (1 : Qp).half) f -∗
      ghostMapAuth γ.prod 1 m -∗ ([∗list] p ∈ tags.zip (ordInflight s), P p.1.1 p.1.2 p.2) -∗
      ordInv γ np P := by
  iintro H1 H2 H3 H4
  unfold ordInv
  iexists s, f, m, tags
  iframe
  ipureintro; exact h

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- A step that moves no value. -/
theorem ordOk_same {np : Nat} {s s' : ChanState V} {f : List Nat} {m : GMap Nat Nat}
    {tags : List (Nat × Nat)} (h : ordOk np s f m tags) (hs : ordInflight s' = ordInflight s)
    (hs' : ordStateOk s') : ordOk np s' f m tags := by
  obtain ⟨-, a, b, c, d⟩ := h
  exact ⟨hs', a, hs ▸ b, c, d⟩

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Closing the invariant after a step that moves no value (from state `s0` to `s`). -/
theorem ordInv_intro_same (γ : OrdNames) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (s s0 : ChanState V) (f : List Nat) (m : GMap Nat Nat) (tags : List (Nat × Nat))
    (h : ordOk np s0 f m tags) (hs : ordInflight s = ordInflight s0) (hs' : ordStateOk s) :
    ⊢ ownChan γ.chanName V s -∗ dghostVar γ.cons (DFrac.own (1 : Qp).half) f -∗
      ghostMapAuth γ.prod 1 m -∗ ([∗list] p ∈ tags.zip (ordInflight s0), P p.1.1 p.1.2 p.2) -∗
      ordInv γ np P := by
  rw [← hs]
  exact ordInv_intro γ np P s f m tags (ordOk_same h hs hs')

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem ordInv_elim (γ : OrdNames) (np : Nat) (P : Nat → Nat → V → IProp GF) :
    ordInv γ np P ⊢ ∃ (s : ChanState V) (f : List Nat) (m : GMap Nat Nat)
      (tags : List (Nat × Nat)),
      ownChan γ.chanName V s ∗ dghostVar γ.cons (DFrac.own (1 : Qp).half) f ∗
      ghostMapAuth γ.prod 1 m ∗ ⌜ordOk np s f m tags⌝ ∗
      [∗list] p ∈ tags.zip (ordInflight s), P p.1.1 p.1.2 p.2 := by
  unfold ordInv; exact .rfl

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Receiving the first value in flight. -/
theorem ord_pop_res (np : Nat) (P : Nat → Nat → V → IProp GF) {s s' : ChanState V}
    {f : List Nat} {m : GMap Nat Nat} {tags : List (Nat × Nat)} {v : V}
    (h : ordOk np s f m tags) (hs : ordInflight s = v :: ordInflight s') (hs' : ordStateOk s') :
    ([∗list] p ∈ tags.zip (ordInflight s), P p.1.1 p.1.2 p.2) ⊢
      ∃ i tr, ⌜i < np ∧ ordOk np s' (f.set i (f.getD i 0 + 1)) m tr⌝ ∗ P i (f.getD i 0) v ∗
        [∗list] p ∈ tr.zip (ordInflight s'), P p.1.1 p.1.2 p.2 := by
  obtain ⟨i, n, tr, rfl, hi, rfl, hok⟩ := ordOk_pop h hs hs'
  rw [hs, List.zip_cons_cons]
  refine BigSepL.bigSepL_cons.1.trans ?_
  iintro ⟨HP, Hr⟩
  iexists i, tr
  iframe
  ipureintro; exact ⟨hi, hok⟩

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Sending a value: producer `i`'s `n`-th. -/
theorem ord_push_res (np : Nat) (P : Nat → Nat → V → IProp GF) {s s' : ChanState V}
    {f : List Nat} {m : GMap Nat Nat} {tags : List (Nat × Nat)} {v : V} {i n : Nat}
    (h : ordOk np s f m tags) (hmi : m.lookup i = some n)
    (hs : ordInflight s' = ordInflight s ++ [v]) (hs' : ordStateOk s') :
    ([∗list] p ∈ tags.zip (ordInflight s), P p.1.1 p.1.2 p.2) ∗ P i n v ⊢
      ⌜ordOk np s' f (m.insert i (n + 1)) (tags ++ [(i, n)])⌝ ∗
        [∗list] p ∈ (tags ++ [(i, n)]).zip (ordInflight s'), P p.1.1 p.1.2 p.2 := by
  have hok := (ordOk_push h hmi hs hs').2
  have hl : tags.length = (ordInflight s).length := h.2.2.1
  rw [hs, List.zip_append hl]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  iintro ⟨Hm, HP⟩
  isplitr
  · ipureintro; exact hok
  · iapply BigSepL.bigSepL_snoc.2
    isplitl [Hm]
    · iexact Hm
    · iexact HP

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
theorem ord_dghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own 1) a ⊢
      dghostVar γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) a := by
  have h := dghostVar_split (GF := GF) γ a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact wand_entails h

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- Producers `0 .. k-1`'s counts, all `0`. -/
theorem ord_alloc_prods (γp : GName) (k : Nat) :
    ⊢ (ghostMapAuth γp 1 (∅ : GMap Nat Nat) : IProp GF) ==∗ ∃ m : GMap Nat Nat,
      ⌜∀ i, m.lookup i = if i < k then some 0 else none⌝ ∗ ghostMapAuth γp 1 m ∗
      [∗list] i ∈ List.range k, (i ↪[γp] (0 : Nat) : IProp GF) := by
  induction k with
  | zero =>
    iintro H
    imodintro
    iexists ∅
    isplitr
    · ipureintro; intro i; rfl
    · isplitl [H]
      · iexact H
      · simp only [List.range_zero]
        iapply BigSepL.bigSepL_nil.2
        iempintro
  | succ k ih =>
    iintro H
    imod ih $$ H with ⟨%m, %hm, H, Hs⟩
    have hk : m.lookup k = none := by rw [hm k]; simp
    imod ghost_map_insert k (0 : Nat) hk $$ H with ⟨H, Hk⟩
    imodintro
    iexists m.insert k 0
    isplitr
    · ipureintro
      intro i
      by_cases hik : k = i
      · subst hik; simp [GMap.insert]
      · have := hm i
        simp only [GMap.insert, hik, ite_false]
        rw [this]
        by_cases hi : i < k
        · simp [hi, show i < k + 1 by omega]
        · simp [hi, show ¬ i < k + 1 by omega]
    · isplitl [H]
      · iexact H
      · rw [List.range_succ]
        iapply BigSepL.bigSepL_snoc.2
        isplitl [Hs]
        · iexact Hs
        · iexact Hk

omit [IntoValTyped (GF := GF) V t] in
/-- A fresh channel (`make`) becomes an ordered channel. -/
theorem start_ord (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF) (γc : ChanNames) :
    ⊢ isChan ch γc V -∗ (ownChan γc V .Idle ∨ ownChan γc V (.Buffered [])) ={⊤}=∗
      ∃ γ, ⌜γ.chanName = γc⌝ ∗ isOrdChan γ ch np P ∗ ordCons γ (List.replicate np 0) ∗
        [∗list] i ∈ List.range np, ordProd γ i 0 := by
  iintro #Hch Hoc
  imod dghostVar_alloc (List.replicate np 0) with ⟨%γcons, Hc⟩
  icases ord_dghostVar_halves _ _ $$ Hc with ⟨HcA, HcF⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Nat) with ⟨%γprod, Ha⟩
  imod ord_alloc_prods γprod np $$ Ha with ⟨%m, %hm, Ha, Hs⟩
  iexists ⟨γc, γprod, γcons⟩
  have hok : ∀ s : ChanState V, ordInflight s = [] → ordStateOk s →
      ordOk np s (List.replicate np 0) m [] := by
    intro s hs hs'
    refine ⟨hs', by simp, by simp [hs], trivial, ?_⟩
    intro i
    rw [hm i]
    by_cases hi : i < np
    · simp [hi, ordFin, List.getD_eq_getElem?_getD]
    · simp [hi]
  unfold isOrdChan ordCons ordProd
  imod inv_alloc nroot ⊤ (ordInv ⟨γc, γprod, γcons⟩ np P) $$ [Hoc HcA Ha] with #Hinv
  · inext
    icases Hoc with (Hoc | Hoc)
    · iapply ordInv_intro ⟨γc, γprod, γcons⟩ np P .Idle _ m [] (hok _ rfl trivial) $$ Hoc HcA Ha
      simp only [List.zip_nil_left]
      iapply BigSepL.bigSepL_nil.2
      iempintro
    · iapply ordInv_intro ⟨γc, γprod, γcons⟩ np P (.Buffered []) _ m [] (hok _ rfl trivial) $$ Hoc HcA Ha
      simp only [List.zip_nil_left]
      iapply BigSepL.bigSepL_nil.2
      iempintro
  imodintro
  isplitr
  · ipureintro; rfl
  isplitr
  · isplitr
    · iexact Hch
    · iexact Hinv
  isplitl [HcF]
  · iexact HcF
  · iexact Hs

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
/-- Producer `i`'s send as an atomic update (`sendAu`). -/
theorem ord_send_au (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (i n : Nat) (v : V) (Φ : IProp GF) :
    ⊢ isOrdChan γ ch np P -∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ ordProd γ i n ∗ P i n v -∗
      ▷ (ordProd γ i (n + 1) -∗ Φ) -∗ sendAu γ.chanName v Φ := by
  unfold isOrdChan sendAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2, Hlc3⟩ ⟨Hprod, HP⟩ Hcont
  iapply ncfupd_of_fupd
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
  icases ordInv_elim _ _ _ $$ Hi with ⟨%s, %f, %m, %tags, Hch, HconsI, Hauth, %Hok, Hm⟩
  unfold ordProd
  ihave %Hmi := ghost_map_lookup $$ Hauth Hprod
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    iintro Hoc
    imod ghost_map_update (n + 1) $$ Hauth Hprod with ⟨Hauth, Hprod⟩
    icases ord_push_res np P (s' := .Buffered (buff ++ [v])) Hok Hmi rfl trivial $$ [$Hm $HP]
      with ⟨%Hok', Hm⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HconsI Hauth Hm] with -
    · inext
      iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
    imodintro
    iapply Hcont $$ Hprod
  | Idle =>
    dsimp only
    iintro Hoc
    imod ghost_map_update (n + 1) $$ Hauth Hprod with ⟨Hauth, Hprod⟩
    icases ord_push_res np P (s' := .SndPending v) Hok Hmi rfl trivial $$ [$Hm $HP]
      with ⟨%Hok', Hm⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HconsI Hauth Hm] with -
    · inext
      iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
    imodintro
    unfold sendNestedAu
    iapply ncfupd_of_fupd
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc3 Hi with Hi
    icases ordInv_elim _ _ _ $$ Hi with ⟨%s, %f1, %m1, %tags1, Hch, HconsI, Hauth, %Hok1, Hm⟩
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
      imod Hclose $$ [Hoc HconsI Hauth Hm] with -
      · inext
        iapply ordInv_intro_same γ np P .Idle _ _ _ _ Hok1 rfl trivial $$ Hoc HconsI Hauth Hm
      imodintro
      iapply Hcont $$ Hprod
    | Closed d => exact absurd Hok1.1 id
    | _ => itrivial
  | RcvPending =>
    dsimp only
    iintro Hoc
    imod ghost_map_update (n + 1) $$ Hauth Hprod with ⟨Hauth, Hprod⟩
    icases ord_push_res np P (s' := .SndCommit v) Hok Hmi rfl trivial $$ [$Hm $HP]
      with ⟨%Hok', Hm⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HconsI Hauth Hm] with -
    · inext
      iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
    imodintro
    iapply Hcont $$ Hprod
  | Closed d => exact absurd Hok.1 id
  | _ => itrivial

/-- Producer `i` sends its `n`-th value. -/
theorem wp_ord_send (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (i n : Nat) (v : V) :
    {{ isOrdChan γ ch np P ∗ ordProd γ i n ∗ P i n v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); ordProd γ i (n + 1) }} := by
  iintro %Φ ⟨#Hord, Hprod, HP⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hord]
  · unfold isOrdChan; icases Hord with ⟨$, -⟩
  iapply chan.wp_send ch v γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply ord_send_au γ ch np P i n v (Φ #()) $$ Hord [$Hlc1 $Hlc2 $Hlc3] [$Hprod $HP] HΦ

omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
/-- The consumer's receive as a `select` clause (`recvAu`). -/
theorem ord_rcv_au (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (f : List Nat) (Φ : V → Bool → IProp GF) :
    ⊢ isOrdChan γ ch np P -∗ £ 1 ∗ £ 1 -∗ ordCons γ f -∗
      ▷ (∀ (v : V) (ok : Bool), ⌜ok = true⌝ -∗ (∃ i, ⌜i < np⌝ ∗ P i (f.getD i 0) v ∗
          ordCons γ (f.set i (f.getD i 0 + 1))) -∗ Φ v ok) -∗
      recvAu γ.chanName V Φ := by
  unfold isOrdChan recvAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases ordInv_elim _ _ _ $$ Hi with ⟨%s, %f0, %m, %tags, Hch, HconsI, Hauth, %Hok, Hm⟩
  unfold ordCons
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HconsI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered b =>
    cases b with
    | nil => itrivial
    | cons v rest =>
      dsimp only
      iintro Hoc
      icases ord_pop_res np P (s' := .Buffered rest) Hok rfl trivial $$ Hm
        with ⟨%i, %tr, ⟨%Hi, %Hok'⟩, HP, Hm⟩
      imod dghostVar_update_halves (f.set i (f.getD i 0 + 1)) _ _ _ $$ Hcons HconsI
        with ⟨Hcons, HconsI⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HconsI Hauth Hm] with -
      · inext
        iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
      imodintro
      iapply Hcont $$ %v %true %rfl
      iexists i
      iframe
      ipureintro; exact Hi
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HconsI Hauth Hm] with -
    · inext
      iapply ordInv_intro_same γ np P .RcvPending .Idle _ _ _ Hok rfl trivial $$ Hoc HconsI Hauth Hm
    imodintro
    unfold recvNestedAu
    iapply ncfupd_of_fupd
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases ordInv_elim _ _ _ $$ Hi with ⟨%s, %f1, %m1, %tags1, Hch, HconsI, Hauth, %Hok1, Hm⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HconsI
    subst Heq
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | SndCommit v =>
      dsimp only
      iintro Hoc
      icases ord_pop_res np P (s' := .Idle) Hok1 rfl trivial $$ Hm
        with ⟨%i, %tr, ⟨%Hi, %Hok'⟩, HP, Hm⟩
      imod dghostVar_update_halves (f.set i (f.getD i 0 + 1)) _ _ _ $$ Hcons HconsI
        with ⟨Hcons, HconsI⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HconsI Hauth Hm] with -
      · inext
        iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
      imodintro
      iapply Hcont $$ %v %true %rfl
      iexists i
      iframe
      ipureintro; exact Hi
    | Closed d => exact absurd Hok1.1 id
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    icases ord_pop_res np P (s' := .RcvCommit) Hok rfl trivial $$ Hm
      with ⟨%i, %tr, ⟨%Hi, %Hok'⟩, HP, Hm⟩
    imod dghostVar_update_halves (f.set i (f.getD i 0 + 1)) _ _ _ $$ Hcons HconsI
      with ⟨Hcons, HconsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HconsI Hauth Hm] with -
    · inext
      iapply ordInv_intro γ np P _ _ _ _ Hok' $$ Hoc HconsI Hauth Hm
    imodintro
    iapply Hcont $$ %v %true %rfl
    iexists i
    iframe
    ipureintro; exact Hi
  | Closed d => exact absurd Hok.1 id
  | _ => itrivial

/-- The consumer receives the next value of some producer. -/
theorem wp_ord_receive (γ : OrdNames) (ch : Loc) (np : Nat) (P : Nat → Nat → V → IProp GF)
    (f : List Nat) :
    {{ isOrdChan γ ch np P ∗ ordCons γ f }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok); ⌜ok = true⌝ ∗ ∃ i, ⌜i < np⌝ ∗
        P i (f.getD i 0) v ∗ ordCons γ (f.set i (f.getD i 0 + 1)) }} := by
  iintro %Φ ⟨#Hord, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hord]
  · unfold isOrdChan; icases Hord with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply ord_rcv_au γ ch np P f (fun v ok => Φ (PairV #v #ok)) $$ Hord [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok %Hok H
  iapply HΦ $$ %v %ok
  isplitr
  · ipureintro; exact Hok
  · iexact H

end ord

end Perennial
