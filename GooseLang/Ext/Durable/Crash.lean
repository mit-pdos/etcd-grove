/-
Crash reasoning for the durable-state extension (WAL W4a, 2026-11-11; the W4 Draft's §5): its crash
interpretation. The files survive a crash unchanged (`durable_semantics`).

**Fresh ghost names per generation** (WAL W4c, decision Q1, etcd-grove-81, 2026-11-12). The crash
allocates the new generation's ghost variable and reservation map afresh (as the abstract disk's
crash does, and Perennial's `osFs`), and `durableCrashStart old new` holds the old generation's
interpretation (its half of the files and the reservation's authority) and the new generation's
ownership: its half of the same files and the reservation's element in the **same mode** (`none`
fresh if the area was unreserved, the persistent `some r` if it was reserved). So:
* the old generation's ownership moves to the new one, in the same mode (`durableOwnM_crash`), and a
  reserved area stays reserved (`durableReserved_crash`);
* or it is **kept** (`durableOwnM_crash_keep`): the old ownership comes back unchanged with the new
  one. A crash obligation, which runs at `⊤` and cannot refute the crash, opens the old generation's
  invariant and must close it again with its contents; with the identity crash interpretation
  (until W4c) one `durableOwnM` could not be both kept there and given to the new generation.

The unreserved element `() ↪ none` is minted at the first start (`durable_local_init`) and at a
crash only for a generation whose predecessor was unreserved: the reservation's one-shot property
holds per generation, and a reserved area is reserved in every later generation.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import GooseLang.Ext.Durable.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section crash
variable {GF : BundledGFunctors}

/-- The reservation's element of the mode the authority's map `m` records, under the ghost name `γ`:
`none` (unreserved, exclusive) or the persistent `some r`; nothing if `m` has no entry. -/
def durableResvElem (hL : DurableGS GF) : Option (Option GoString) → IProp GF
  | some none => letI := hL.durableAllG; iprop(() ↪[hL.durableResvName] (none : Option GoString))
  | some (some r) => letI := hL.durableAllG; iprop(() ↪[hL.durableResvName]□ (some r))
  | none => iprop(True)

/-- **What a crash hands the next generation**: the old generation's interpretation (its half of
the files `fs` and the reservation's authority at `m`), and the new generation's half of the same
files with the reservation's element in the mode `m` records. -/
def durableCrashStart (hL hL' : DurableGS GF) : IProp GF :=
  letI := hL.durableAllG
  iprop(∃ (fs : DurableState) (m : GMap Unit (Option GoString)),
    durableVar hL (1 : Qp).half fs ∗ ghostMapAuth hL.durableResvName 1 m ∗
    durableVar hL' (1 : Qp).half fs ∗ durableResvElem hL' (m !! ()))

theorem durable_local_crash (hPre : DurableGpreS GF) (hL : DurableGS GF) (fs fs' : DurableState)
    (hc : fs' = fs) :
    ⊢@{IProp GF} durableCtx hL fs ==∗ ∃ hL' : DurableGS GF, durableCtx hL' fs' ∗
      durableCrashStart hL hL' := by
  subst hc
  letI := hPre.durablePreAllG
  unfold durableCtx durableResvAuth
  iintro ⟨Hv, ⟨%m, Ha, %hinv⟩⟩
  imod ghostVar_alloc (GF := GF) fs' with ⟨%γ, H⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option GoString) with ⟨%γr, Hr⟩
  let hL' : DurableGS GF := ⟨hPre.durablePreAllG, γ, γr⟩
  icases (ghostVar_split_half γ 1 fs').mp $$ H with ⟨H1, H2⟩
  cases hm : m !! () with
  | none =>
    imodintro
    iexists hL'
    isplitl [H1 Hr]
    · unfold durableVar
      iframe H1; iexists ∅; iframe Hr; ipureintro
      intro r hr; simp [GMap.lookup_empty] at hr
    · unfold durableCrashStart
      iexists fs', m; iframe Hv Ha
      unfold durableVar; iframe H2
      rw [hm]; simp only [durableResvElem]; itrivial
  | some o =>
    imod ghost_map_insert (GF := GF) () o (GMap.lookup_empty _) $$ Hr with ⟨Hr, He⟩
    cases o with
    | none =>
      imodintro
      iexists hL'
      isplitl [H1 Hr]
      · unfold durableVar
        iframe H1; iexists _; iframe Hr; ipureintro
        intro r hr; simp [GMap.lookup_insert_eq_iff] at hr
      · unfold durableCrashStart
        iexists fs', m; iframe Hv Ha
        unfold durableVar; iframe H2
        rw [hm]; simp only [durableResvElem]; iexact He
    | some r =>
      imod ghostMapElem_persist $$ He with #He
      imodintro
      iexists hL'
      isplitl [H1 Hr]
      · unfold durableVar
        iframe H1; iexists _; iframe Hr; ipureintro
        intro r' hr'
        simp [GMap.lookup_insert_eq_iff] at hr'
        subst hr'
        exact hinv r hm
      · unfold durableCrashStart
        iexists fs', m; iframe Hv Ha
        unfold durableVar; iframe H2
        rw [hm]; simp only [durableResvElem]; iexact He

end crash

/-- **The durable state's crash interpretation**: fresh ghost names per generation, the mode kept
(`durableCrashStart`). -/
instance durable_crash_interp : ExtCrashInterp durableExt where
  crashStart hL hL' := durableCrashStart hL hL'
  local_crash _ hPre hL σ σ' h := durable_local_crash hPre hL σ σ' h

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The crash, keeping the old ownership**: the old generation's files in the mode `o` come back
unchanged, and the new generation's are the same files in the same mode. -/
theorem durableOwnM_crash_keep (L L' : GooseLocalGS GF) (o : Option GoString) (fs : DurableState) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableOwnM (L := L) o fs -∗ durableOwnM (L := L) o fs ∗ durableOwnM (L := L') o fs := by
  letI := (gooseDurableGS (L := L)).durableAllG
  have hmode : ∀ m : GMap Unit (Option GoString),
      durableOwnM (L := L) o fs ∗ ghostMapAuth (gooseDurableGS (L := L)).durableResvName 1 m ⊢
        ⌜m !! () = some o⌝ := by
    intro m
    cases o <;> simp only [durableOwnM, durableOwn, durableOwnR, durableReserved]
    · iintro ⟨⟨-, He⟩, Ha⟩; iapply ghost_map_lookup $$ Ha He
    · iintro ⟨⟨-, He⟩, Ha⟩; iapply ghost_map_lookup $$ Ha He
  have hvar : ∀ fs0 : DurableState,
      durableOwnM (L := L) o fs ∗ durableVar (gooseDurableGS (L := L)) (1 : Qp).half fs0 ⊢
        ⌜fs0 = fs⌝ := by
    intro fs0
    iintro ⟨Hown, Hv⟩
    iapply durableVar_agreeM (L := L) o fs0 fs $$ Hv Hown
  change ⊢@{IProp GF} durableCrashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L')) -∗ _
  unfold durableCrashStart
  iintro Hc Hown
  icases Hc with ⟨%fs0, %m, Hv, Ha, Hv', He'⟩
  icases persistent_entails_right (hmode m) $$ [Hown Ha] with ⟨%hm, Hown, -⟩
  · isplitl [Hown]; iexact Hown; iexact Ha
  icases persistent_entails_right (hvar fs0) $$ [Hown Hv] with ⟨%hfs, Hown, -⟩
  · isplitl [Hown]; iexact Hown; iexact Hv
  subst hfs
  iframe Hown
  rw [hm]
  cases o <;> simp only [durableResvElem, durableOwnM, durableOwn, durableOwnR, durableReserved]
  · iframe Hv' He'
  · iframe Hv' He'

/-- The old generation's files, in the mode `o`, are the new one's (in the same mode). -/
theorem durableOwnM_crash (L L' : GooseLocalGS GF) (o : Option GoString) (fs : DurableState) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableOwnM (L := L) o fs -∗ durableOwnM (L := L') o fs := by
  iintro Hc Hown
  icases durableOwnM_crash_keep L L' o fs $$ Hc Hown with ⟨-, H⟩
  iexact H

/-- **A reserved area stays reserved**: the old generation's reservation is the new one's. -/
theorem durableReserved_crash (L L' : GooseLocalGS GF) (r : GoString) :
    ⊢@{IProp GF} durable_crash_interp.crashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L'))
      -∗ durableReserved (L := L) r -∗ durableReserved (L := L') r := by
  letI := (gooseDurableGS (L := L)).durableAllG
  change ⊢@{IProp GF} durableCrashStart (gooseDurableGS (L := L)) (gooseDurableGS (L := L')) -∗ _
  unfold durableCrashStart
  unfold durableReserved
  iintro Hc #Hr
  icases Hc with ⟨%fs0, %m, -, Ha, -, He'⟩
  icases ghost_map_lookup $$ Ha Hr with %hm
  have hm' : m !! () = some (some r) := hm
  rw [hm']
  simp only [durableResvElem]
  iexact He'

end gen

end Perennial
