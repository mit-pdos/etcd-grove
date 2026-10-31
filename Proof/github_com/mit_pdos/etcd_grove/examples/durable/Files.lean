/-
Lean-first (no Rocq counterpart).

# `durable.Read`/`durable.Write`, per file (2026-10-31)

The Go functions' specs (`Spec/github_com/mit_pdos/etcd_grove/examples/durable/{Read,Write}.lean`)
are the extension's, on the program's half of all the files (`durableOwn`). For a program that
shares the files per file (`GooseLang/Ext/Durable/Files.lean`: `durableFilesInv γ N`, `dfile γ f o`),
these are their per-file forms, from the specs (taken as hypotheses, as a proof takes its callees'):
the logically atomic ones (the owner of the file's entry may keep it in an invariant of its own,
opened in the update at `⊤ \ ↑N`) and, for an owner holding the entry, the forms with a
continuation (`Q -∗ Φ v`, not a Hoare triple's `▷ (Q -∗ Φ v)`: the specs are atomic updates,
whose step leaves no later to strip).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.durable.Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.durable.Write
public import GooseLang.Ext.Durable.Files

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section files
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.durable.Assumptions]

namespace github_com.mit_pdos.etcd_grove.examples.durable

/-- `Read(f)`, per file, logically atomic: the contents `o` of `f`'s entry. -/
theorem Read.wp_file_au (wp_Read : Read.spec (GF := GF) (hG := hG)) (γ : GName)
    (N : Namespace) (f : GoString) (Φ : val → IProp GF) :
    ⊢ durableFilesInv γ N -∗
      (|={⊤ \ ↑N,∅}=> ∃ o : Option GoString, dfile γ f o ∗
        (dfile γ f o ={∅,⊤ \ ↑N}=∗ Φ (durableReadVal o))) -∗
      WP (App (Val (@! Read)) (Val #f)) {{ Φ }} := by
  iintro #Hinv HAU
  iapply wp_Read f $$ %Φ
  iapply durableFiles_read_au γ N ⊤ CoPset.subseteq_top f Φ $$ Hinv HAU

/-- `Read(f)`, per file, with the entry in hand: `f`'s contents (`""` and `false` if there is no
file `f`). -/
theorem Read.wp_file (wp_Read : Read.spec (GF := GF) (hG := hG)) (γ : GName) (N : Namespace)
    (f : GoString) (o : Option GoString) (Φ : val → IProp GF) :
    ⊢ durableFilesInv γ N -∗ dfile γ f o -∗ (dfile γ f o -∗ Φ (durableReadVal o)) -∗
      WP (App (Val (@! Read)) (Val #f)) {{ Φ }} := by
  iintro #Hinv Hf HΦ
  iapply Read.wp_file_au wp_Read γ N f $$ Hinv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iexists o
  iframe Hf
  iintro Hf
  imod Hclose with -
  imodintro
  iapply HΦ $$ Hf

/-- `Write(f, data)`, per file, logically atomic: `f`'s entry then holds `data`. -/
theorem Write.wp_file_au (wp_Write : Write.spec (GF := GF) (hG := hG)) (γ : GName)
    (N : Namespace) (f data : GoString) (Φ : val → IProp GF) :
    ⊢ durableFilesInv γ N -∗
      (|={⊤ \ ↑N,∅}=> ∃ o : Option GoString, dfile γ f o ∗
        (dfile γ f (some data) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (Val (@! Write)) (Val #f)) (Val #data)) {{ Φ }} := by
  iintro #Hinv HAU
  iapply wp_Write f data $$ %Φ
  iapply durableFiles_write_au γ N ⊤ CoPset.subseteq_top f data (Φ #()) $$ Hinv HAU

/-- `Write(f, data)`, per file, with the entry in hand: `f`'s entry then holds `data`. -/
theorem Write.wp_file (wp_Write : Write.spec (GF := GF) (hG := hG)) (γ : GName) (N : Namespace)
    (f data : GoString) (o : Option GoString) (Φ : val → IProp GF) :
    ⊢ durableFilesInv γ N -∗ dfile γ f o -∗ (dfile γ f (some data) -∗ Φ #()) -∗
      WP (App (App (Val (@! Write)) (Val #f)) (Val #data)) {{ Φ }} := by
  iintro #Hinv Hf HΦ
  iapply Write.wp_file_au wp_Write γ N f data $$ Hinv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iexists o
  iframe Hf
  iintro Hf
  imod Hclose with -
  imodintro
  iapply HΦ $$ Hf

end github_com.mit_pdos.etcd_grove.examples.durable

end files

end Perennial
