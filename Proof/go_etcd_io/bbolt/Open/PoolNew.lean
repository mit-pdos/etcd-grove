/-
**The page pool's `New` in `Open`** (U11i, `notes/bbolt-proof-plan.md`; Perennial `pool-new-later`:
`isPool p f R P`, `New` may assume the `R` its `Get` caller lends it).

`Open` sets `db.pagePool = sync.Pool{New: func() any { return make([]byte, db.pageSize) }}`: the
closure reads `Open`'s named result `db` (the cell `dp`), which every `return` of `Open` writes
(goose aliases `$res0` to it), non-atomically. A `Get` caller lends `New` a `poolR γbq N P`
(`Inv/Bolt`): every caller is inside a `Commit`, whose update over `boltState` holds the whole
validity token `γbq` (`B.bq`). The protocol `dpInv` (a tag `γs`, half here, half with `Open`):
- `0`, before `Open`'s last write: the cell's other half is here, for `New` to read;
- `1`, during it: `Open` has the whole cell, and the whole token `γbq` is here, which no lender
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

/-- **The protocol of `Open`'s cell `dp` (holding `db`) and the page pool's `New`.** -/
def dpInv (γs γbq : GName) (dp db : Loc) : IProp GF :=
  iprop(∃ s : Nat, ghostVar γs (1 : Qp).half s ∗
    ((⌜s = 0⌝ ∗ dp ↦{DFrac.own (1 : Qp).half} db) ∨ (⌜s = 1⌝ ∗ ghostVar γbq 1 ()) ∨
      (⌜s = 2⌝ ∗ dp ↦□ db)))

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

/-- **`Open`'s last write begins**: the whole token in, the cell's other half out. -/
theorem dp_lock (E : CoPset) (N : Namespace) (γs γbq : GName) (dp db : Loc)
    (hE : (↑(dpN N) : CoPset) ⊆ E) :
    inv (dpN N) (dpInv (GF := GF) γs γbq dp db) ∗ ghostVar γs (1 : Qp).half 0 ∗
      dp ↦{DFrac.own (1 : Qp).half} db ∗ ghostVar γbq 1 () ⊢
    |={E}=> ghostVar γs (1 : Qp).half 1 ∗ dp ↦ db := by
  iintro ⟨#Hinv, Hs, Hdp, Hbq⟩
  iinv Hinv with Hi Hclose
  unfold dpInv
  icases Hi with ⟨%s, >Hs', Hc⟩
  ihave %Hag := ghostVar_valid_2 γs (0 : Nat) _ s _ $$ Hs Hs'
  obtain ⟨-, rfl⟩ := Hag
  icases Hc with (⟨-, >Hdp'⟩ | ⟨>%h, -⟩ | ⟨>%h, -⟩)
  rotate_left
  · cases h
  · cases h
  ihave Hall := (ghostVar_split_half γs 1 (0 : Nat)).2 $$ [Hs Hs']
  · iframe
  imod ghostVar_update (1 : Nat) γs (0 : Nat) $$ Hall with Hall
  icases (ghostVar_split_half γs 1 (1 : Nat)).1 $$ Hall with ⟨Hs, Hs'⟩
  imod Hclose $$ [Hs' Hbq] with -
  · inext
    iexists 1
    iframe Hs'
    iright; ileft
    iframe Hbq
    ipureintro; rfl
  imodintro
  iframe Hs
  iapply (typedPointsto_half_split dp db 1).2
  iframe

/-- **`Open`'s last write done, on success**: the token back, the cell persistent. -/
theorem dp_unlock (E : CoPset) (N : Namespace) (γs γbq : GName) (dp db : Loc)
    (hE : (↑(dpN N) : CoPset) ⊆ E) :
    inv (dpN N) (dpInv (GF := GF) γs γbq dp db) ∗ ghostVar γs (1 : Qp).half 1 ∗ dp ↦ db ⊢
    |={E}=> ghostVar γbq 1 () ∗ dp ↦□ db := by
  iintro ⟨#Hinv, Hs, Hdp⟩
  ipersist Hdp
  iinv Hinv with Hi Hclose
  unfold dpInv
  icases Hi with ⟨%s, >Hs', Hc⟩
  ihave %Hag := ghostVar_valid_2 γs (1 : Nat) _ s _ $$ Hs Hs'
  obtain ⟨-, rfl⟩ := Hag
  icases Hc with (⟨>%h, -⟩ | ⟨-, >Hbq⟩ | ⟨>%h, -⟩)
  · cases h
  rotate_left
  · cases h
  ihave Hall := (ghostVar_split_half γs 1 (1 : Nat)).2 $$ [Hs Hs']
  · iframe
  imod ghostVar_update (2 : Nat) γs (1 : Nat) $$ Hall with Hall
  icases (ghostVar_split_half γs 1 (2 : Nat)).1 $$ Hall with ⟨-, Hs'⟩
  imod Hclose $$ [Hs'] with -
  · inext
    iexists 2
    iframe Hs'
    iright; iright
    iframe #
    ipureintro; rfl
  imodintro
  iframe Hbq
  iexact Hdp

end poolnew

end bbolt
end EtcdGrove
end Perennial
