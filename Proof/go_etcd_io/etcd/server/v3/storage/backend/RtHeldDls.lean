/-
**Probe (B3's R1): a prototype of the strengthening `rtHeldDlsLaw` needs** (`notes/mvccfull-probe-r1.md`).
Scratch: not imported by any proof.

`rtHeldDlsLaw` (`mvcc/NewCleanRead.lean`) is not provable over today's definitions: a held reader's
resource (`rtHeld`) relates its missing entries to nothing but the registration (`thinV`'s `dlIs`),
and the deleted entries' ghost `γ.dls` has only two halves, the client's (`dlsOwn`) and the batch
lock's (`fkHalf`, inside the mutex: out of reach of an entailment). The proposed strengthening:

* `dlsOwn γ X` becomes a half of a ghost *map* authority at the same name (`dlsOwnM`), so that the
  entries ever deleted leave persistent witnesses (`dlSeen`): `BSess.dl` only grows (`BSess.del` is
  its only writer), and a deleted safe-range entry is fresh (`dlsS`: missing from the writer's
  contents, while `BSess.del` inserts only a present one), so the insert never overwrites;
* the readers' resource (`rtCore`) gets a conjunct `dlCov γ P (vData P rv) L`: every safe-range
  entry of the logical view `L` missing from the readers' state is `dlSeen`.

Over them the law is `rtHeldDlsLawM_of` (from the projection law `hCov`, which the strengthened
`rtCore` gives as `rtHeld_clean` gives `thinV`), with the two steps proved here: the lookup
(`dlCov_dlsOwnM`) and the delete's update (`dlsOwnM_insert`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- (Proposed `dlsOwn`) a half of the deleted entries' map authority. -/
def dlsOwnM (γ : BNames) (X : GMap (GoString × GoString) GoString) : IProp GF :=
  ghostMapAuth γ.dls (1 : Qp).half X

/-- The entry `nk` was deleted since the open (persistent). -/
def dlSeen (γ : BNames) (nk : GoString × GoString) : IProp GF :=
  iprop(∃ v : GoString, nk ↪[γ.dls]□ v)

instance dlSeen_persistent (γ : BNames) (nk : GoString × GoString) :
    Persistent (dlSeen (GF := GF) γ nk) := by
  unfold dlSeen; infer_instance

/-- (Proposed conjunct of `rtCore`) every safe-range entry of the logical view `L` missing from the
physical view `phys` was deleted since the open. -/
def dlCov (γ : BNames) (P : BParams) (phys L : VData) : IProp GF :=
  iprop(□ ∀ nk, ⌜P.SB nk.1 = true ∧ P.HB nk.1 = false ∧ L.lookup nk ≠ none ∧
    phys.lookup nk = none⌝ -∗ dlSeen γ nk)

instance dlCov_persistent (γ : BNames) (P : BParams) (phys L : VData) :
    Persistent (dlCov (GF := GF) γ P phys L) := by
  unfold dlCov; infer_instance

/-- **The lookup**: a covered view's missing entries are in the client's half. -/
theorem dlCov_dlsOwnM (γ : BNames) (P : BParams) (phys L X : VData) :
    dlCov (GF := GF) γ P phys L ∗ dlsOwnM γ X ⊢
      dlsOwnM γ X ∗ ⌜∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → L.lookup nk ≠ none →
        phys.lookup nk = none → X.lookup nk ≠ none⌝ := by
  iintro ⟨#Hc, Hx⟩
  by_cases hφ : ∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → L.lookup nk ≠ none →
      phys.lookup nk = none → X.lookup nk ≠ none
  · iframe Hx; ipureintro; exact hφ
  · obtain ⟨nk, h1, h2, h3, h4, h5⟩ : ∃ nk, P.SB nk.1 = true ∧ P.HB nk.1 = false ∧
        L.lookup nk ≠ none ∧ phys.lookup nk = none ∧ X.lookup nk = none := by
      apply Classical.byContradiction
      intro hn
      apply hφ
      intro nk a b c d e
      exact hn ⟨nk, a, b, c, d, by simpa using e⟩
    iunfold dlCov at Hc
    have h14 := And.intro h1 (And.intro h2 (And.intro h3 h4))
    ihave Hs := Hc $$ %nk %h14
    iunfold dlSeen at Hs
    icases Hs with ⟨%v, #Hv⟩
    iunfold dlsOwnM at Hx
    icombine Hx Hv gives %hl
    rw [h5] at hl
    cases hl

/-- **The delete's update** (where `InvBatch.lean` today does `ghostVar_update_halves`): both halves,
a fresh entry inserted, its witness minted. -/
theorem dlsOwnM_insert (E : CoPset) (γ : BNames) (X : VData) (nk : GoString × GoString) (v : GoString)
    (h : X.lookup nk = none) :
    dlsOwnM (GF := GF) γ X ∗ dlsOwnM γ X ⊢
      |={E}=> dlsOwnM γ (X.insert nk v) ∗ dlsOwnM γ (X.insert nk v) ∗ dlSeen γ nk := by
  iintro ⟨H1, H2⟩
  iunfold dlsOwnM at H1 H2
  ihave H := (ghostMapAuth_halves γ.dls X).2 $$ [$H1 $H2]
  imod (ghost_map_insert_persist (GF := GF) (γ := γ.dls) nk v h) $$ H with ⟨H, #Hv⟩
  icases (ghostMapAuth_halves γ.dls (X.insert nk v)).1 $$ H with ⟨H1, H2⟩
  imodintro
  iunfold dlsOwnM
  iframe H1 H2
  iunfold dlSeen
  iexists v
  iexact Hv

/-- **`rtHeldDlsLaw` over the strengthening** (`dlsOwnM` for `dlsOwn`): from the projection law the
strengthened `rtCore` would give (`hCov`, `rtHeld_clean`'s pattern), the law. -/
theorem rtHeldDlsLawM_of
    (hCov : ∀ (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (q : Qp) (vd : VData),
      rtHeld (GF := GF) γ P b rtx rv ∗ bViewC γ q vd true ⊢
        rtHeld γ P b rtx rv ∗ bViewC γ q vd true ∗ dlCov γ P (vData P rv) vd)
    (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (q : Qp) (vd : VData) (X : VData) :
    rtHeld (GF := GF) γ P b rtx rv ∗ bViewC γ q vd true ∗ dlsOwnM γ X ⊢
      rtHeld γ P b rtx rv ∗ bViewC γ q vd true ∗ dlsOwnM γ X ∗
      ⌜∀ nk, P.SB nk.1 = true → P.HB nk.1 = false → vd.lookup nk ≠ none →
        (vData P rv).lookup nk = none → X.lookup nk ≠ none⌝ := by
  iintro ⟨Hh, Hv, Hx⟩
  icases hCov γ P b rtx rv q vd $$ [$Hh $Hv] with ⟨Hh, Hv, #Hc⟩
  icases dlCov_dlsOwnM γ P (vData P rv) vd X $$ [$Hc $Hx] with ⟨Hx, %H⟩
  iframe Hh Hv Hx
  ipureintro; exact H

end proto

end backend
end EtcdGrove
end Perennial
