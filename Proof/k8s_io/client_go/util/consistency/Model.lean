/-
The consistency store's abstract state and its operations, as pure functions
(`k8s.io/client-go/util/consistency`, `consistency.go`). Lean-first; phase 2 of the DaemonSet plan
(`notes/k8s-daemonset-plan.md`).

**The abstract state** `M : GMap Owner Rec`: per owner (a `types.NamespacedName`) its record, the
owner's UID and the newest resource version written per `GroupResource` (`Rec.vs`). The
operations are `wroteAtM` (`WroteAt`: the record is replaced by an empty one for a different UID,
then the version raised, `wroteAtVs`; a version that is not well formed, `""` or `"0"` among them,
is ignored, but the record is still created or replaced), `clearM` (`Clear`), and `GMap.delete o M`
(`EnsureReady` when it succeeds).

**Pending writes** (`absVsOk`). A `WroteAt` takes effect, abstractly, when it finds the owner's
record, and its write to the record follows, under the record's lock; in between, the write is
pending. The abstract versions of a record are the maximum (by `decVal`) of its physical versions
and its pending writes, key by key (`candOf`, `absVsOk`): `absVsOk_add` (a write becomes pending),
`absVsOk_withdraw` (a pending write lands), `absVsOk_nil` (no write pending: the abstract versions
are the physical ones).
-/
module

public import Proof.k8s_io.client_go.Base
public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open resourceversion

/-- An owner: the namespace and name of the object whose writes are recorded. -/
abbrev Owner [FfiSyntax] : Type := k8s_io.apimachinery.pkg.types.NamespacedName
/-- A group resource. -/
abbrev GR [FfiSyntax] : Type := k8s_io.apimachinery.pkg.runtime.schema.GroupResource
/-- A record's versions, per group resource. -/
abbrev Vs [FfiSyntax] : Type := GMap GR GoString

section keys
variable [FfiSyntax]

instance owner_decEq : DecidableEq Owner := fun a b =>
  if h : a.Namespace' = b.Namespace' ∧ a.Name' = b.Name' then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance gr_decEq : DecidableEq GR := fun a b =>
  if h : a.Group' = b.Group' ∧ a.Resource' = b.Resource' then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance owner_countable : Pos.Countable Owner :=
  .ofInjective (fun o => Pos.Countable.encode (o.Namespace', o.Name'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; rw [h.1, h.2])

instance gr_countable : Pos.Countable GR :=
  .ofInjective (fun o => Pos.Countable.encode (o.Group', o.Resource'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h; rw [h.1, h.2])

end keys

/-! ## The abstract state -/

/-- An owner's record: the owner's UID and the newest version written per group resource. -/
structure Rec [FfiSyntax] where
  uid : GoString
  vs : Vs

section ops
variable [FfiSyntax]

/-- `ownerRecord.WroteAt(gr, rv)`: `rv` becomes the version of `gr` if it is well formed and
newer (by value) than the one there, or there is none. -/
def wroteAtVs (V : Vs) (gr : GR) (rv : GoString) : Vs :=
  if wellFormed rv then
    match V !! gr with
    | none => <[gr := rv]> V
    | some old => if decVal old < decVal rv then <[gr := rv]> V else V
  else V

/-- The record `WroteAt(o, uid, ...)` writes into: the owner's if it is for `uid`, else a new
empty one. -/
def recFor (M : GMap Owner Rec) (o : Owner) (uid : GoString) : Rec :=
  match M !! o with
  | some r => if r.uid = uid then r else ⟨uid, ∅⟩
  | none => ⟨uid, ∅⟩

/-- `WroteAt(o, uid, gr, rv)`: the owner's record (a new empty one if there is none or it is for
another UID) with `wroteAtVs`. -/
def wroteAtM (M : GMap Owner Rec) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString) :
    GMap Owner Rec :=
  <[o := ⟨uid, wroteAtVs (recFor M o uid).vs gr rv⟩]> M

/-- `Clear(o, uid)`: the owner's record goes if `uid` is empty or is the record's. -/
def clearM (M : GMap Owner Rec) (o : Owner) (uid : GoString) : GMap Owner Rec :=
  match M !! o with
  | some r => if uid = [] ∨ r.uid = uid then GMap.delete o M else M
  | none => M

end ops

/-! ## Versions: the newest of the physical and the pending ones -/

section abs
variable [FfiSyntax]

/-- All the versions are well formed. -/
def vsWf (V : Vs) : Prop := ∀ gr x, V !! gr = some x → wellFormed x = true

/-- A candidate for the abstract version of `gr`: the physical one, or a pending well-formed one
(`pin gr y`: a write of `y` to `gr` is pending). -/
def candOf (V : Vs) (pin : GR → GoString → Prop) (gr : GR) (y : GoString) : Prop :=
  V !! gr = some y ∨ (pin gr y ∧ wellFormed y = true)

/-- `Va` holds, per group resource, the newest (by value) candidate, if any. -/
def absVsOk (V : Vs) (pin : GR → GoString → Prop) (Va : Vs) : Prop :=
  ∀ gr, match Va !! gr with
    | some x => candOf V pin gr x ∧ ∀ z, candOf V pin gr z → decVal z ≤ decVal x
    | none => ∀ z, ¬ candOf V pin gr z

/-- Well-formed versions are their values. -/
theorem decVal_inj {a b : GoString} (ha : wellFormed a = true) (hb : wellFormed b = true)
    (h : decVal a = decVal b) : a = b := by
  have e := lexCmp_eq_cmpNat a b ha hb
  simp only [cmpNat, h, Nat.lt_irrefl, ↓reduceIte] at e
  unfold lexCmp at e
  by_cases h1 : a.length < b.length
  · simp only [h1, ↓reduceIte] at e; exact absurd e (by decide)
  by_cases h2 : a.length > b.length
  · simp only [h1, h2, ↓reduceIte] at e; exact absurd e (by decide)
  simp only [h1, h2, ↓reduceIte, strings.compareResult] at e
  by_cases h3 : go.GoStringLt a b
  · simp only [h3, ↓reduceIte] at e; exact absurd e (by decide)
  · simp only [h3, ↓reduceIte] at e
    by_cases h4 : a = b
    · exact h4
    · simp only [h4, ↓reduceIte] at e; exact absurd e (by decide)

theorem wroteAtVs_wf (V : Vs) (gr : GR) (rv : GoString) (h : vsWf V) :
    vsWf (wroteAtVs V gr rv) := by
  intro g x hx
  unfold wroteAtVs at hx
  by_cases hw : wellFormed rv = true
  · simp only [hw, ↓reduceIte] at hx
    split at hx
    · by_cases hg : g = gr
      · subst hg; simp at hx; subst hx; exact hw
      · simp [Ne.symm hg] at hx; exact h g x hx
    · split at hx
      · by_cases hg : g = gr
        · subst hg; simp at hx; subst hx; exact hw
        · simp [Ne.symm hg] at hx; exact h g x hx
      · exact h g x hx
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hx; exact h g x hx

/-- No pending write: the abstract versions are the physical ones. -/
theorem absVsOk_nil (V Va : Vs) (pin : GR → GoString → Prop) (hpin : ∀ gr y, ¬ pin gr y)
    (h : absVsOk V pin Va) : Va = V := by
  apply GMap.ext
  intro gr
  have hg := h gr
  unfold candOf at hg
  cases hva : Va !! gr with
  | some x =>
    rw [hva] at hg
    obtain ⟨hc, -⟩ := hg
    rcases hc with hc | ⟨hp, -⟩
    · exact hc.symm
    · exact absurd hp (hpin _ _)
  | none =>
    rw [hva] at hg
    cases hv : V !! gr with
    | none => rfl
    | some y => exact absurd (Or.inl hv) (hg y)

/-- The empty record has no candidates. -/
theorem absVsOk_empty : absVsOk (∅ : Vs) (fun _ _ => False) ∅ := by
  intro gr
  simp only [GMap.lookup_empty]
  intro z hz
  rcases hz with hz | ⟨hz, -⟩
  · simp at hz
  · exact hz

/-- **A write becomes pending**: the abstract versions take it (`wroteAtVs`). -/
theorem absVsOk_add (V Va : Vs) (pin : GR → GoString → Prop) (gr0 : GR) (y0 : GoString)
    (h : absVsOk V pin Va) :
    absVsOk V (fun gr y => pin gr y ∨ (gr = gr0 ∧ y = y0)) (wroteAtVs Va gr0 y0) := by
  intro gr
  have hg := h gr
  have hcand : ∀ z, candOf V (fun gr y => pin gr y ∨ (gr = gr0 ∧ y = y0)) gr z ↔
      candOf V pin gr z ∨ (gr = gr0 ∧ z = y0 ∧ wellFormed y0 = true) := by
    intro z
    unfold candOf
    constructor
    · rintro (h1 | ⟨h1 | ⟨rfl, rfl⟩, hw⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨h1, hw⟩)
      · exact Or.inr ⟨rfl, rfl, hw⟩
    · rintro ((h1 | ⟨h1, hw⟩) | ⟨rfl, rfl, hw⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨Or.inl h1, hw⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hw⟩
  by_cases hgr : gr = gr0
  · subst hgr
    by_cases hw : wellFormed y0 = true
    · unfold wroteAtVs
      simp only [hw, ↓reduceIte]
      cases hva : Va !! gr with
      | none =>
        rw [hva] at hg
        simp only [GMap.lookup_insert_eq]
        refine ⟨(hcand y0).2 (Or.inr ⟨rfl, rfl, hw⟩), fun z hz => ?_⟩
        rcases (hcand z).1 hz with hz | ⟨-, rfl, -⟩
        · exact absurd hz (hg z)
        · exact Nat.le_refl _
      | some old =>
        rw [hva] at hg
        obtain ⟨hc, hub⟩ := hg
        by_cases hlt : decVal old < decVal y0
        · simp only [hlt, ↓reduceIte, GMap.lookup_insert_eq]
          refine ⟨(hcand y0).2 (Or.inr ⟨rfl, rfl, hw⟩), fun z hz => ?_⟩
          rcases (hcand z).1 hz with hz | ⟨-, rfl, -⟩
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hub z hz) hlt)
          · exact Nat.le_refl _
        · simp only [hlt, ↓reduceIte, hva]
          refine ⟨(hcand old).2 (Or.inl hc), fun z hz => ?_⟩
          rcases (hcand z).1 hz with hz | ⟨-, rfl, -⟩
          · exact hub z hz
          · exact Nat.le_of_not_lt hlt
    · have hwf : wroteAtVs Va gr y0 = Va := by
        unfold wroteAtVs; simp only [hw, Bool.false_eq_true, ↓reduceIte]
      rw [hwf]
      cases hva : Va !! gr with
      | none =>
        rw [hva] at hg
        intro z hz
        rcases (hcand z).1 hz with hz | ⟨-, -, hw'⟩
        · exact hg z hz
        · exact hw hw'
      | some x =>
        rw [hva] at hg
        obtain ⟨hc, hub⟩ := hg
        refine ⟨(hcand x).2 (Or.inl hc), fun z hz => ?_⟩
        rcases (hcand z).1 hz with hz | ⟨-, -, hw'⟩
        · exact hub z hz
        · exact absurd hw' hw
  · have hlk : (wroteAtVs Va gr0 y0) !! gr = Va !! gr := by
      unfold wroteAtVs
      split
      · split
        · simp [Ne.symm hgr, hgr]
        · split
          · simp [Ne.symm hgr]
          · rfl
      · rfl
    rw [hlk]
    have hc' : ∀ z, candOf V (fun gr y => pin gr y ∨ (gr = gr0 ∧ y = y0)) gr z ↔
        candOf V pin gr z := by
      intro z
      rw [hcand z]
      constructor
      · rintro (h1 | ⟨h1, -⟩)
        · exact h1
        · exact absurd h1 hgr
      · exact Or.inl
    cases hva : Va !! gr with
    | none => rw [hva] at hg; intro z hz; exact hg z ((hc' z).1 hz)
    | some x =>
      rw [hva] at hg
      exact ⟨(hc' x).2 hg.1, fun z hz => hg.2 z ((hc' z).1 hz)⟩

/-- **A pending write lands**: its value moves from the pending writes (`pin` to `pin'`, which
keeps the others) into the physical versions (`wroteAtVs V gr0 y0`); the abstract versions stay. -/
theorem absVsOk_withdraw (V Va : Vs) (pin pin' : GR → GoString → Prop) (gr0 : GR) (y0 : GoString)
    (hV : vsWf V) (hin : pin gr0 y0) (hsub : ∀ gr y, pin' gr y → pin gr y)
    (hsup : ∀ gr y, pin gr y → pin' gr y ∨ (gr = gr0 ∧ y = y0)) (h : absVsOk V pin Va) :
    absVsOk (wroteAtVs V gr0 y0) pin' Va := by
  intro gr
  have hg := h gr
  -- the new candidates are among the old ones
  have hnew : ∀ z, candOf (wroteAtVs V gr0 y0) pin' gr z → candOf V pin gr z := by
    rintro z (hz | ⟨hz, hw⟩)
    · unfold wroteAtVs at hz
      by_cases hw : wellFormed y0 = true
      · simp only [hw, ↓reduceIte] at hz
        by_cases hgr : gr = gr0
        · subst hgr
          split at hz
          · simp at hz; subst hz; exact Or.inr ⟨hin, hw⟩
          · split at hz
            · simp at hz; subst hz; exact Or.inr ⟨hin, hw⟩
            · exact Or.inl hz
        · split at hz
          · simp [Ne.symm hgr] at hz; exact Or.inl hz
          · split at hz
            · simp [Ne.symm hgr] at hz; exact Or.inl hz
            · exact Or.inl hz
      · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hz; exact Or.inl hz
    · exact Or.inr ⟨hsub _ _ hz, hw⟩
  cases hva : Va !! gr with
  | none =>
    rw [hva] at hg
    intro z hz; exact hg z (hnew z hz)
  | some x =>
    rw [hva] at hg
    obtain ⟨hc, hub⟩ := hg
    refine ⟨?_, fun z hz => hub z (hnew z hz)⟩
    -- the newest candidate is still one
    rcases hc with hc | ⟨hp, hw⟩
    · -- the physical version: still there unless `y0` (at `gr0`) replaced it
      by_cases hgr : gr = gr0
      · subst hgr
        by_cases hw0 : wellFormed y0 = true
        · have hle : decVal y0 ≤ decVal x := hub y0 (Or.inr ⟨hin, hw0⟩)
          left
          unfold wroteAtVs
          simp only [hw0, ↓reduceIte, hc]
          by_cases hlt : decVal x < decVal y0
          · exact absurd hlt (Nat.not_lt_of_le hle)
          · simp only [hlt, ↓reduceIte, hc]
        · left; unfold wroteAtVs; simp only [hw0, Bool.false_eq_true, ↓reduceIte]; exact hc
      · left
        unfold wroteAtVs
        split
        · split
          · simp [Ne.symm hgr, hc]
          · split
            · simp [Ne.symm hgr, hc]
            · exact hc
        · exact hc
    · rcases hsup _ _ hp with hp' | ⟨rfl, rfl⟩
      · exact Or.inr ⟨hp', hw⟩
      · -- `x` is `y0`, the newest: it is the physical version now
        left
        unfold wroteAtVs
        simp only [hw, ↓reduceIte]
        cases hvg : V !! gr with
        | none => simp
        | some old =>
          simp only
          have hle : decVal old ≤ decVal x := hub old (Or.inl hvg)
          by_cases hlt : decVal old < decVal x
          · simp [hlt]
          · simp only [hlt, ↓reduceIte, hvg]
            congr 1
            exact decVal_inj (hV _ _ hvg) hw (by omega)

end abs

end consistency
end EtcdGrove
end Perennial
