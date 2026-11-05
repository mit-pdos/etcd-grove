/-
**The page pool's `New` in `Open`** (U11i, U11j, `notes/bbolt-proof-plan.md`; Perennial `pool-new-later`:
`isPool p f R P`, `New` may assume the `R` its `Get` caller lends it).

`Open` sets `db.pagePool = sync.Pool{New: func() any { return make([]byte, db.pageSize) }}`: the
closure reads `Open`'s named result `db` (the cell `dp`), which every `return` of `Open` writes
(goose aliases `$res0` to it), non-atomically. A `Get` caller lends `New` a `poolR γbq N P`
(`Inv/Bolt`): every caller is inside a `Commit`, whose update over `boltState` holds the whole
validity token `γbq` (`B.bq`). The protocol `dpInv` (a tag `γs`, half here, half with `Open`):
- `0`, before `Open`'s last write: the cell's other half is here, and a reader borrows a fraction
  of it for its whole read (`dp_borrow`, `dp_return`), depositing its lease `P` as collateral
  (saved under a name `γp`, the borrow recorded in a ghost map `γm`);
- `1`, during it: `Open` has the whole cell (`dp_lock` collects every fraction, refuting a borrow
  still out by its lease and the whole token `γbq`), and that token is here, which no lender
  can hold too (`poolR` excludes it);
- `2`, after it (on success): the cell is persistent.
On an error exit `Open` leaves the protocol at `1` for good (no `isBolt` is returned).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section poolnew
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [sync.Assumptions]

/-- The protocol's namespace (inside the database's). -/
def dpN (N : Namespace) : Namespace := N.@"pagePoolNew"

theorem dpN_sub (N : Namespace) : (↑(dpN N) : CoPset) ⊆ ↑N := by
  unfold dpN; exact nclose_subseteq _ _

/-- A lease's refutation (at `⊤ ∖ N`) runs inside `dpInv`. -/
theorem dp_mask_dp (N : Namespace) : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(dpN N) := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff] at hp ⊢
  exact ⟨hp.1, fun h => hp.2 (dpN_sub N p h)⟩

/-- The fractions of `Open`'s other half of the cell: `dyad c = 2^-(c+1)`. After `c` borrows the
protocol holds `dyad c` and borrow `i < c` was lent `dyad (i + 1)`; they add up to `1/2`. -/
def dyad : Nat → Qp
  | 0 => (1 : Qp).half
  | c + 1 => (dyad c).half

theorem dyad_zero : dyad 0 = (1 : Qp).half := rfl

theorem dyad_split (dp db : Loc) (c : Nat) :
    dp ↦{DFrac.own (dyad c)} db ⊣⊢
      (dp ↦{DFrac.own (dyad (c + 1))} db ∗ dp ↦{DFrac.own (dyad (c + 1))} db : IProp GF) :=
  typedPointsto_half_split dp db (dyad c)

/-- The records of the first `c` borrows (`S i` the record of borrow `i`). -/
def dpSlots (S : Nat → IProp GF) : Nat → IProp GF
  | 0 => iprop(True)
  | c + 1 => iprop(dpSlots S c ∗ S c)

theorem dpSlots_succ (S : Nat → IProp GF) (c : Nat) :
    dpSlots S (c + 1) = iprop(dpSlots S c ∗ S c) := rfl

/-- Borrow `i`'s record, taken out and put back. -/
theorem dpSlots_acc (S : Nat → IProp GF) (i c : Nat) (h : i < c) :
    dpSlots S c ⊢ S i ∗ (S i -∗ dpSlots S c) := by
  induction c with
  | zero => omega
  | succ c ih =>
    rw [dpSlots_succ]
    by_cases hi : i = c
    · subst hi
      iintro ⟨Hs, Hi⟩
      iframe Hi
      iintro Hi
      iframe
    · iintro ⟨Hs, Hc⟩
      icases (ih (by omega)) $$ Hs with ⟨Hi, Hback⟩
      iframe Hi
      iintro Hi
      iframe Hc
      iapply Hback $$ Hi

/-- **Borrow `i`'s record while `Open` has not collected** (state `0`): its names in `γm` (`γk`
the borrower's token, `γp` its lease saved), and either the borrower has come back (its token
here, with its fraction `dyad (i + 1)`), or its lease `P` is deposited here, with `P`'s
refutation against the whole token `γbq`. -/
def dpSlot0 (N : Namespace) (γbq γm : GName) (dp db : Loc) (i : Nat) : IProp GF :=
  iprop(∃ γk γp : GName, i ↪[γm]□ ((γk, γp) : GName × GName) ∗
    ((ghostVar γk 1 () ∗ dp ↦{DFrac.own (dyad (i + 1))} db) ∨
      (∃ P : IProp GF, savedPropOwn γp DFrac.discard P ∗ P ∗
        □ (P ∗ ghostVar γbq 1 () ={⊤ \ ↑N}=∗ False))))

/-- **Borrow `i`'s record once collected** (states `1`, `2`): the borrower has come back. -/
def dpSlot1 (γm : GName) (i : Nat) : IProp GF :=
  iprop(∃ γk γp : GName, i ↪[γm]□ ((γk, γp) : GName × GName) ∗ ghostVar γk 1 ())

/-- **The protocol of `Open`'s cell `dp` (holding `db`) and the page pool's `New`.** States:
- `0`, before `Open`'s last write: the cell's other half here, less the fractions lent to the
  `c` borrows so far (`dyad c` left), each recorded with the borrower's lease as collateral;
- `1`, during it: `Open` has the whole cell (`dp_lock` collected every fraction, a borrow still
  out being refuted by its lease), and the whole token `γbq` is here;
- `2`, after it (on success): the cell is persistent.
`γm` names the borrows (`c` of them). -/
def dpInv (N : Namespace) (γs γbq γm : GName) (dp db : Loc) : IProp GF :=
  iprop(∃ s c : Nat, ∃ m : GMap Nat (GName × GName), ghostVar γs (1 : Qp).half s ∗
    ghostMapAuth γm 1 m ∗ ⌜∀ k, c ≤ k → m.lookup k = none⌝ ∗
    ((⌜s = 0⌝ ∗ dp ↦{DFrac.own (dyad c)} db ∗ dpSlots (dpSlot0 N γbq γm dp db) c) ∨
      (⌜s = 1⌝ ∗ ghostVar γbq 1 () ∗ dpSlots (dpSlot1 γm) c) ∨
      (⌜s = 2⌝ ∗ dp ↦□ db ∗ dpSlots (dpSlot1 γm) c)))

/-- **The protocol** (persistent): `dpInv` for some name of its borrows. -/
def dpProt (N : Namespace) (γs γbq : GName) (dp db : Loc) : IProp GF :=
  iprop(∃ γm : GName, inv (dpN N) (dpInv N γs γbq γm dp db))

instance dpProt_persistent (N : Namespace) (γs γbq : GName) (dp db : Loc) :
    Persistent (dpProt (GF := GF) N γs γbq dp db) := by
  unfold dpProt; infer_instance

/-- **A loan of the fraction `q` of the cell** (borrow `i`), against the lease `P`. -/
def dpLoan (N : Namespace) (γs γbq : GName) (dp db : Loc) (P : IProp GF) (q : Qp) :
    IProp GF :=
  iprop(∃ γm i γk γp, inv (dpN N) (dpInv N γs γbq γm dp db) ∗ ⌜q = dyad (i + 1)⌝ ∗
    i ↪[γm]□ ((γk, γp) : GName × GName) ∗ ghostVar γk 1 () ∗ savedPropOwn γp DFrac.discard P)

/-- **The protocol begins** (state `0`, no borrow), with `Open`'s other half of the cell. -/
theorem dp_init (E : CoPset) (N : Namespace) (γs γbq : GName) (dp db : Loc) :
    ghostVar (GF := GF) γs (1 : Qp).half 0 ∗ dp ↦{DFrac.own (1 : Qp).half} db ⊢
      |={E}=> dpProt N γs γbq dp db := by
  iintro ⟨Hs, Hdp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GName × GName) with ⟨%γm, Hm⟩
  unfold dpProt
  iexists γm
  iapply inv_alloc
  inext
  unfold dpInv
  iexists 0, 0, ∅
  iframe Hs Hm
  isplitr
  · ipureintro; intro k _; rfl
  ileft
  isplitr
  · ipureintro; rfl
  rw [dyad_zero]
  iframe Hdp
  unfold dpSlots
  itrivial

/-- **`New`'s read of `db` begins**: with its lease `P` (and `P`'s refutation), either the cell
is persistent (state `2`: `P` back at once), or (state `0`) the reader is lent a fraction `q` of
the cell, `P` deposited as collateral (`dp_return` gives both back). State `1` (`Open` holds the
whole token) is refuted by `P`. -/
theorem dp_borrow (N : Namespace) (γs γbq : GName) (dp db : Loc) (P : IProp GF) :
    dpProt N γs γbq dp db ∗ P ∗ □ (P ∗ ghostVar γbq 1 () ={⊤ \ ↑N}=∗ False) ⊢
    |={⊤}=> (dp ↦□ db ∗ P) ∨ (∃ q : Qp, dp ↦{DFrac.own q} db ∗ dpLoan N γs γbq dp db P q) := by
  unfold dpProt
  iintro ⟨⟨%γm, #Hinv⟩, HP, #Href⟩
  iinv Hinv with Hi Hclose
  unfold dpInv
  icases Hi with ⟨%s, %c, %m, >Hs', >Hm, >%Hfr, Hc⟩
  icases Hc with (⟨>%h, >Hdp, Hsl⟩ | ⟨>%h, >Hbq, -⟩ | ⟨>%h, >#Hdp, Hsl⟩)
  · subst h
    icases (dyad_split dp db c).1 $$ Hdp with ⟨Hdp, Hdp'⟩
    imod ghostVar_alloc (GF := GF) () with ⟨%γk, Hk⟩
    imod saved_prop_alloc (GF := GF) P DFrac.discard DFrac.valid_discard with ⟨%γp, #Hsp⟩
    imod ghost_map_insert_persist c ((γk, γp) : GName × GName) (Hfr c (Nat.le_refl c)) $$ Hm
      with ⟨Hm, #Hel⟩
    imod Hclose $$ [Hs' Hm Hdp Hsl HP] with -
    · inext
      iexists 0, c + 1, _
      iframe Hs' Hm
      isplitr
      · ipureintro
        intro k hk
        rw [GMap.lookup_insert_ne _ _ (by omega)]
        exact Hfr k (by omega)
      ileft
      isplitr
      · ipureintro; rfl
      iframe Hdp
      rw [dpSlots_succ]
      iframe Hsl
      unfold dpSlot0
      iexists γk, γp
      isplitr
      · iexact Hel
      iright
      iexists P
      iframe HP; iframe #
    imodintro
    iright
    iexists dyad (c + 1)
    iframe Hdp'
    unfold dpLoan
    iexists γm, c, γk, γp
    isplitr
    · unfold dpInv; iexact Hinv
    isplitr
    · ipureintro; rfl
    iframe Hk; iframe #
  · ihave Hf := Href $$ [HP Hbq]
    · iframe
    imod (fupd_mask_mono (P := iprop(False)) (dp_mask_dp N)) $$ Hf with Hf
    iexfalso; iexact Hf
  · imod Hclose $$ [Hs' Hm Hsl] with -
    · inext
      iexists s, c, m
      iframe Hs' Hm
      isplitr
      · ipureintro; exact Hfr
      iright; iright
      iframe Hsl; iframe #
      ipureintro; exact h
    imodintro
    ileft
    iframe HP; iframe #

/-- **`New`'s read of `db` done**: the fraction back, and the lease `P` back under two laters
(the deposit was under the protocol's later, and its saved name agrees with `P` under one more).
The borrow cannot have come back already, nor (states `1`, `2`) been collected: the reader holds
its token `γk`. -/
theorem dp_return (N : Namespace) (γs γbq : GName) (dp db : Loc) (P : IProp GF) (q : Qp) :
    dp ↦{DFrac.own q} db ∗ dpLoan N γs γbq dp db P q ⊢ |={⊤}=> ▷ ▷ P := by
  unfold dpLoan
  iintro ⟨Hdp, %γm, %i, %γk, %γp, #Hinv, %hq, #Hel, Hk, #Hsp⟩
  subst hq
  iinv Hinv with Hi Hclose
  unfold dpInv
  icases Hi with ⟨%s, %c, %m, >Hs', >Hm, >%Hfr, Hc⟩
  ihave %Hlk := ghost_map_lookup $$ Hm Hel
  have hic : i < c := by
    rcases Nat.lt_or_ge i c with h | h
    · exact h
    · rw [Hfr i h] at Hlk; cases Hlk
  icases Hc with (⟨>%h, >Hdp0, Hsl⟩ | ⟨>%h, >Hbq, Hsl⟩ | ⟨>%h, >#Hdp2, Hsl⟩)
  · ihave ⟨Hsi, Hback⟩ := (later_mono (dpSlots_acc _ i c hic)) $$ Hsl
    unfold dpSlot0
    icases Hsi with ⟨%γk', %γp', >#Hel', Hor⟩
    ihave %Hag := ghostMapElem_agree i γm _ _ _ _ $$ Hel Hel'
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    icases Hor with (⟨>Hk', -⟩ | HB)
    · ihave %h := ghostVar_valid_2 γk () 1 () 1 $$ Hk Hk'
      exfalso
      have h1 := h.1
      rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
      grind
    imod Hclose $$ [Hs' Hm Hdp0 Hback Hk Hdp] with -
    · inext
      iexists s, c, m
      iframe Hs' Hm
      isplitr
      · ipureintro; exact Hfr
      ileft
      iframe Hdp0
      isplitr
      · ipureintro; exact h
      iapply Hback
      iexists γk, γp
      iframe Hel
      ileft
      iframe
    imodintro
    inext
    icases HB with ⟨%P', Hsp', HP', -⟩
    ihave Heq := saved_prop_agree γp _ _ P P' $$ Hsp Hsp'
    inext
    iapply internal_eq_rewrite_wand $$ Heq HP'
  all_goals
    ihave ⟨Hsi, -⟩ := (later_mono (dpSlots_acc _ i c hic)) $$ Hsl
    unfold dpSlot1
    icases Hsi with ⟨%γk', %γp', >#Hel', >Hk'⟩
    ihave %Hag := ghostMapElem_agree i γm _ _ _ _ $$ Hel Hel'
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    ihave %h := ghostVar_valid_2 γk () 1 () 1 $$ Hk Hk'
    exfalso
    have h1 := h.1
    rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
    grind

/-- **`dp_lock`'s collection**: every borrow's fraction back (its record collected), or the borrow
still out, its lease refuted by the whole token `γbq`. -/
theorem dp_collect (N : Namespace) (γbq γm : GName) (dp db : Loc) (c : Nat) :
    ghostVar (GF := GF) γbq 1 () ∗ dpSlots (dpSlot0 N γbq γm dp db) c ∗
        dp ↦{DFrac.own (dyad c)} db ⊢
      |={⊤ \ ↑(dpN N)}=> ghostVar γbq 1 () ∗ dp ↦{DFrac.own (1 : Qp).half} db ∗
        dpSlots (dpSlot1 γm) c := by
  induction c with
  | zero =>
    rw [dyad_zero]
    iintro ⟨Hbq, -, Hdp⟩
    imodintro
    iframe Hbq Hdp
    unfold dpSlots
    itrivial
  | succ c ih =>
    rw [dpSlots_succ, dpSlots_succ, dpSlot0]
    iintro ⟨Hbq, ⟨Hsl, %γk, %γp, #Hel, Hor⟩, Hdp⟩
    icases Hor with (⟨Hk, Hdp'⟩ | ⟨%P, -, HP, #Href⟩)
    · ihave Hdp := (dyad_split dp db c).2 $$ [Hdp Hdp']
      · iframe
      imod ih $$ [Hbq Hsl Hdp] with ⟨Hbq, Hdp, Hsl⟩
      · iframe
      imodintro
      iframe Hbq Hdp Hsl
      unfold dpSlot1
      iexists γk, γp
      iframe Hk; iframe #
    · ihave Hf := Href $$ [HP Hbq]
      · iframe
      imod (fupd_mask_mono (P := iprop(False)) (dp_mask_dp N)) $$ Hf with Hf
      iexfalso; iexact Hf

/-- **`New`'s read of `db` under a loan**: the load, then (`dp_return`) the fraction back and the
lease back under two laters, which the closure's next steps take off. -/
theorem wp_load_loan {t : go.GoType} [IntoValTyped (GF := GF) Loc t] (N : Namespace)
    (γs γbq : GName) (dp db : Loc) (P : IProp GF) (q : Qp) :
    {{ dp ↦{DFrac.own q} db ∗ dpLoan N γs γbq dp db P q }}
      (App (Val (GoInstruction (GoLoad t))) (Val #dp))
    {{ RET #db; ▷ ▷ P }} := by
  iintro %Φ ⟨Hdp, Hl⟩ HΦ
  iapply wp_fupd
  iapply (IntoValTyped.wp_load (t := t) dp (DFrac.own q) db) $$ Hdp
  inext
  iintro Hdp
  imod dp_return N γs γbq dp db P q $$ [Hdp Hl] with HP
  · iframe
  imodintro
  iapply HΦ $$ HP

/-- A pool's `isPool` with another `New` spec (`isPool` is `New`'s field, its spec and the pool's
invariant, which does not mention the spec). A fact about Perennial's `isPool` (to move there,
`notes/perennial-changes.md`). -/
theorem isPool_respec (p : Loc) (f : GoFunc) (R R' : IProp GF) (P : GoAny → IProp GF) :
    sync.isPool p f R P ∗ sync.newSpec f R' P ⊢ sync.isPool p f R' P := by
  rw [sync.isPool_unseal]
  unfold sync.isPoolDef named
  iintro ⟨⟨#HN, -, #Hinv⟩, #Hs⟩
  iframe #

/-- **A pool initialized for a family of `New` specs** (`init_Pool` at one, `isPool_respec` for the
others). -/
theorem init_Pool_all (p : Loc) (v : sync.Pool) (R : IProp GF → IProp GF) (P : GoAny → IProp GF)
    (E : CoPset) :
    typedPointsto (GF := GF) p v (DFrac.own 1) ∗ □ (∀ Q : IProp GF, sync.newSpec v.New' (R Q) P) ∗
      ⌜v.local' = null⌝ ⊢
      |={E}=> ∀ Q : IProp GF, sync.isPool p v.New' (R Q) P := by
  iintro ⟨Hp, #HN, %hlocal⟩
  imod sync.init_Pool p v (R iprop(True)) P E hlocal $$ [Hp] with #H0
  · iframe Hp
    iapply HN
  imodintro
  iintro %Q
  iapply isPool_respec
  iframe H0
  iapply HN

/-- **`Open`'s last write begins**, around one step of `Open`'s (so that a lease deposited under
the protocol's later can refute its borrow): the whole token in, the cell's other half out
(every borrow's fraction collected, `dp_collect`). -/
theorem dp_lock (N : Namespace) (γs γbq : GName) (dp db : Loc) :
    dpProt (GF := GF) N γs γbq dp db ∗ ghostVar γs (1 : Qp).half 0 ∗ ghostVar γbq 1 () ⊢
    |={⊤, ⊤ \ ↑(dpN N)}=> ▷ |={⊤ \ ↑(dpN N), ⊤}=>
      ghostVar γs (1 : Qp).half 1 ∗ dp ↦{DFrac.own (1 : Qp).half} db := by
  unfold dpProt
  iintro ⟨⟨%γm, #Hinv⟩, Hs, Hbq⟩
  imod inv_acc (E := ⊤) (CoPset.subseteq_top) $$ Hinv with ⟨Hi, Hclose⟩
  imodintro
  inext
  unfold dpInv
  icases Hi with ⟨%s, %c, %m, Hs', Hm, %Hfr, Hc⟩
  ihave %Hag := ghostVar_valid_2 γs (0 : Nat) _ s _ $$ Hs Hs'
  obtain ⟨-, rfl⟩ := Hag
  icases Hc with (⟨-, Hdp', Hsl⟩ | ⟨%h, -⟩ | ⟨%h, -⟩)
  rotate_left
  · cases h
  · cases h
  imod dp_collect N γbq γm dp db c $$ [Hbq Hsl Hdp'] with ⟨Hbq, Hdp', Hsl⟩
  · iframe
  ihave Hall := (ghostVar_split_half γs 1 (0 : Nat)).2 $$ [Hs Hs']
  · iframe
  imod ghostVar_update (1 : Nat) γs (0 : Nat) $$ Hall with Hall
  icases (ghostVar_split_half γs 1 (1 : Nat)).1 $$ Hall with ⟨Hs, Hs'⟩
  imod Hclose $$ [Hs' Hm Hbq Hsl] with -
  · inext
    iexists 1, c, m
    iframe Hs' Hm
    isplitr
    · ipureintro; exact Hfr
    iright; ileft
    iframe Hbq Hsl
    ipureintro; rfl
  imodintro
  iframe Hs Hdp'

/-- **`Open`'s last write done, on success**: the token back, the cell persistent. -/
theorem dp_unlock (N : Namespace) (γs γbq : GName) (dp db : Loc) :
    dpProt (GF := GF) N γs γbq dp db ∗ ghostVar γs (1 : Qp).half 1 ∗ dp ↦ db ⊢
    |={⊤}=> ghostVar γbq 1 () ∗ dp ↦□ db := by
  unfold dpProt
  iintro ⟨⟨%γm, #Hinv⟩, Hs, Hdp⟩
  ipersist Hdp
  iinv Hinv with Hi Hclose
  unfold dpInv
  icases Hi with ⟨%s, %c, %m, >Hs', >Hm, >%Hfr, Hc⟩
  ihave %Hag := ghostVar_valid_2 γs (1 : Nat) _ s _ $$ Hs Hs'
  obtain ⟨-, rfl⟩ := Hag
  icases Hc with (⟨>%h, -⟩ | ⟨-, >Hbq, Hsl⟩ | ⟨>%h, -⟩)
  · cases h
  rotate_left
  · cases h
  ihave Hall := (ghostVar_split_half γs 1 (1 : Nat)).2 $$ [Hs Hs']
  · iframe
  imod ghostVar_update (2 : Nat) γs (1 : Nat) $$ Hall with Hall
  icases (ghostVar_split_half γs 1 (2 : Nat)).1 $$ Hall with ⟨-, Hs'⟩
  imod Hclose $$ [Hs' Hm Hsl] with -
  · inext
    iexists 2, c, m
    iframe Hs' Hm
    isplitr
    · ipureintro; exact Hfr
    iright; iright
    iframe Hsl; iframe #
    ipureintro; rfl
  imodintro
  iframe Hbq
  iexact Hdp

end poolnew

end bbolt
end EtcdGrove
end Perennial
