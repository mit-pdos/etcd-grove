/-
Per-file ownership of the durable state (2026-10-31).

The extension's ghost state is one ghost variable over all the files (`durableOwn fs`, `Specs.lean`):
it says which files do not exist, which a read returns, but it is one resource, so two threads
writing two different files cannot each own its file. This file splits it, for a program that
shares the files: the program's half `durableOwn fs` goes into an invariant
(`durableFilesInv γ N`), next to the authority of a ghost map `m` from the file names claimed so
far to their contents (`none`: no such file), which agrees with `fs` on its domain; a thread owns
the entry of a file, `dfile γ f o` ("the file `f` holds `o`", `o = none` if there is none),
exclusively, and only its owner can change it.

* `durableFiles_alloc`: from `durableOwn fs`, the invariant and the entries of the names `D`
  (distinct), each with its contents in `fs`. The names are chosen at allocation (a program's
  files are named by it: kvdurable's `dir/replica-<id>`, `id ≤ maxReplicas`); a file not in `D`
  can never be written.
* `durableFiles_read_au`/`durableFiles_write_au`: a per-file atomic update (at the masks
  `E \ ↑N`, `∅`) gives the extension's atomic update on `durableOwn` (at `E`, `∅`), which the
  extension's specs (`wp_DurableRead_atomic`, `wp_DurableWrite_atomic`) and the Go functions'
  (`durable.Read.spec`, `durable.Write.spec`) take. So the owner of `dfile γ f o` can keep it in
  an invariant of its own and read or write the file inside it; the Hoare forms follow.

No trusted content: a ghost map and an invariant over the extension's specs.
-/
module

public import GooseLang.Ext.Durable.Specs
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.DFrac

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- What a read of a file holding `o` returns (`durableReadResult`, per file): its contents and
`true`, or `""` and `false` if there is no such file. -/
def durableReadVal [GooseExts] [GoGlobalContext] (o : Option GoString) : val :=
  PairV (#(o.getD ([] : GoString))) (#o.isSome)

theorem durableReadResult_eq [GooseExts] [GoGlobalContext] (fs : DurableState) (f : GoString) :
    durableReadResult fs f = durableReadVal (fs !! f) := rfl

section files
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [AllG GF]

/-- **The file `f` holds `o`** (`none`: there is no file `f`), owned: the entry of `f` in the
ghost map `γ` of a `durableFilesInv γ N`. -/
def dfile (γ : GName) (f : GoString) (o : Option GoString) : IProp GF :=
  ghostMapElem γ f (DFrac.own 1) o

instance dfile_timeless (γ : GName) (f : GoString) (o : Option GoString) :
    Timeless (dfile (GF := GF) γ f o) := by
  unfold dfile; infer_instance

/-- The ghost map `m` of the claimed files agrees with the files `fs`. -/
def DurableFilesAgree (fs : DurableState) (m : GMap GoString (Option GoString)) : Prop :=
  ∀ f o, m.lookup f = some o → fs !! f = o

/-- The invariant's body: the program's half of the files, and the authority of the claimed
files' ghost map, which agrees with them. -/
def durableFilesBody (γ : GName) : IProp GF :=
  iprop(∃ (fs : DurableState) (m : GMap GoString (Option GoString)),
    durableOwn fs ∗ ghostMapAuth γ 1 m ∗ ⌜DurableFilesAgree fs m⌝)

/-- **The files, shared per file** (see the file header): persistent. -/
def durableFilesInv (γ : GName) (N : Namespace) : IProp GF :=
  inv N (durableFilesBody γ)

instance durableFilesInv_persistent (γ : GName) (N : Namespace) :
    Persistent (durableFilesInv (GF := GF) γ N) := by
  unfold durableFilesInv; infer_instance

/-- Two owners of one file: impossible. -/
theorem dfile_excl (γ : GName) (f : GoString) (o o' : Option GoString) :
    ⊢ dfile (GF := GF) γ f o -∗ dfile γ f o' -∗ False := by
  unfold dfile
  iintro H1 H2
  icases ghostMapElem_valid_2 f γ (DFrac.own 1) (DFrac.own 1) o o' $$ H1 H2 with %Hv
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- Claiming the names `D` (distinct, none claimed yet): each gets its entry, with its contents. -/
theorem durableFiles_claim (γ : GName) (fs : DurableState) :
    ∀ (D : List GoString) (m : GMap GoString (Option GoString)), D.Nodup →
      (∀ f ∈ D, m.lookup f = none) → DurableFilesAgree fs m →
      ghostMapAuth (GF := GF) γ 1 m ⊢ |==> ∃ m' : GMap GoString (Option GoString),
        ghostMapAuth γ 1 m' ∗ ⌜DurableFilesAgree fs m'⌝ ∗
        [∗list] f ∈ D, dfile γ f (fs !! f)
  | [], m, _, _, Hag => by
    iintro H
    imodintro
    iexists m
    iframe H
    isplitl []
    · ipureintro; exact Hag
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | f :: D, m, Hnd, Hfree, Hag => by
    have Hnd' := List.nodup_cons.1 Hnd
    iintro H
    imod ghost_map_insert f (fs !! f) (Hfree f (List.mem_cons_self ..)) $$ H with ⟨H, Hf⟩
    have Hfree' : ∀ g ∈ D, (m.insert f (fs !! f)).lookup g = none := by
      intro g hg
      have hne : f ≠ g := fun h => Hnd'.1 (h ▸ hg)
      show (if f = g then _ else _) = none
      rw [if_neg hne]
      exact Hfree g (List.mem_cons_of_mem _ hg)
    have Hag' : DurableFilesAgree fs (m.insert f (fs !! f)) := by
      intro g o hg
      change (if f = g then some (fs !! f) else m.lookup g) = some o at hg
      by_cases hfg : f = g
      · subst hfg; rw [if_pos rfl] at hg; exact Option.some.inj hg
      · rw [if_neg hfg] at hg; exact Hag g o hg
    imod durableFiles_claim γ fs D (m.insert f (fs !! f)) Hnd'.2 Hfree' Hag' $$ H
      with ⟨%m', H, %Hag'', Hs⟩
    imodintro
    iexists m'
    iframe H
    isplitl []
    · ipureintro; exact Hag''
    iapply BigSepL.bigSepL_cons.2
    unfold dfile
    iframe Hf Hs

/-- **Allocation**: from the program's half of the files, the shared invariant and the entries of
the distinct names `D`, each holding its contents in `fs`. -/
theorem durableFiles_alloc (N : Namespace) (E : CoPset) (fs : DurableState) (D : List GoString)
    (HD : D.Nodup) :
    durableOwn (L := L) fs ⊢ |={E}=> ∃ γ : GName, durableFilesInv (GF := GF) γ N ∗
      [∗list] f ∈ D, dfile γ f (fs !! f) := by
  iintro Hown
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Option GoString) with ⟨%γ, H⟩
  imod durableFiles_claim γ fs D ∅ HD (fun _ _ => rfl) (fun _ _ h => by simp at h) $$ H
    with ⟨%m, H, %Hag, Hs⟩
  imod inv_alloc N E (durableFilesBody (GF := GF) γ) $$ [Hown H] with #Hinv
  · inext
    unfold durableFilesBody
    iexists fs, m
    iframe Hown H
    ipureintro; exact Hag
  imodintro
  iexists γ
  unfold durableFilesInv
  iframe Hinv Hs

/-- **A per-file read** (see the file header): the atomic update of the owner of `f`'s entry
gives the extension's read update. -/
theorem durableFiles_read_au (γ : GName) (N : Namespace) (E : CoPset) (HN : ↑N ⊆ E)
    (f : GoString) (Φ : val → IProp GF) :
    ⊢ durableFilesInv γ N -∗
      (|={E \ ↑N,∅}=> ∃ o : Option GoString, dfile γ f o ∗
        (dfile γ f o ={∅,E \ ↑N}=∗ Φ (durableReadVal o))) -∗
      |={E,∅}=> ∃ fs : DurableState, durableOwn (L := L) fs ∗
        (durableOwn fs ={∅,E}=∗ Φ (durableReadResult fs f)) := by
  iintro #Hinv HAU
  unfold durableFilesInv
  iinv Hinv with Hi Hclose
  unfold durableFilesBody
  icases Hi with ⟨%fs, %m, >Hown, >Hauth, >%Hag⟩
  imod HAU with ⟨%o, Hf, Hcl⟩
  unfold dfile
  icases ghost_map_lookup $$ Hauth Hf with %Hm
  have Hfo : fs !! f = o := Hag f o Hm
  imodintro
  iexists fs
  iframe Hown
  iintro Hown
  rw [durableReadResult_eq, Hfo]
  imod Hcl $$ Hf with HΦ
  imod Hclose $$ [Hown Hauth] with -
  · inext
    iexists fs, m
    iframe Hown Hauth
    ipureintro; exact Hag
  imodintro
  iexact HΦ

/-- **A per-file write** (see the file header): the atomic update of the owner of `f`'s entry
gives the extension's write update; the entry then holds `data`. -/
theorem durableFiles_write_au (γ : GName) (N : Namespace) (E : CoPset) (HN : ↑N ⊆ E)
    (f data : GoString) (Φ : IProp GF) :
    ⊢ durableFilesInv γ N -∗
      (|={E \ ↑N,∅}=> ∃ o : Option GoString, dfile γ f o ∗
        (dfile γ f (some data) ={∅,E \ ↑N}=∗ Φ)) -∗
      |={E,∅}=> ∃ fs : DurableState, durableOwn (L := L) fs ∗
        (durableOwn (<[f := data]> fs) ={∅,E}=∗ Φ) := by
  iintro #Hinv HAU
  unfold durableFilesInv
  iinv Hinv with Hi Hclose
  unfold durableFilesBody
  icases Hi with ⟨%fs, %m, >Hown, >Hauth, >%Hag⟩
  imod HAU with ⟨%o, Hf, Hcl⟩
  imodintro
  iexists fs
  iframe Hown
  iintro Hown
  unfold dfile
  imod ghost_map_update (some data) $$ Hauth Hf with ⟨Hauth, Hf⟩
  have Hag' : DurableFilesAgree (<[f := data]> fs) (m.insert f (some data)) := by
    intro g o' hg
    change (if f = g then some (some data) else m.lookup g) = some o' at hg
    change (if f = g then some data else fs !! g) = o'
    by_cases hfg : f = g
    · rw [if_pos hfg] at hg ⊢; exact Option.some.inj hg
    · rw [if_neg hfg] at hg ⊢; exact Hag g o' hg
  imod Hcl $$ Hf with HΦ
  imod Hclose $$ [Hown Hauth] with -
  · inext
    iexists (<[f := data]> fs), m.insert f (some data)
    iframe Hown Hauth
    ipureintro; exact Hag'
  imodintro
  iexact HΦ

end files

end Perennial
