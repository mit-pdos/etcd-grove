/-
**Held bytes behind an accessor** (S4, 2026-11-18): the vocabulary of the racing read's spec
(`os.File.ReadAt.specRacyLt`, `Spec/os/File__ReadAt.lean`), whose model makes several `pread`s,
each one atomic step (`wp_osPRead_racy_list`, `GooseLang/Ext/Fs/Specs.lean`).

* `heldAcc p rs P E` (persistent): from the client's resource `P`, an accessor that opens, from
  the mask `⊤` to `E` (which must keep `osN`, for the `pread`), to some ranges `rs'` of bytes of the
  file `p` held (`osBytes`) that say at least what the fixed ranges `rs` say of each byte
  (`os.heldByte rs i b → os.heldByte rs' i b`), and closes back to `P` with the same ranges. A
  reader whose bytes live in an invariant (bbolt's `pagesInv`) opens it around each `pread`; one
  that holds them (`P := [∗list] osBytes rs`) has the trivial accessor (`heldAcc_own`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace os

open Iris Iris.BI Iris.ProofMode
open Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- See the file header. -/
def heldAcc (p : Ino) (rs : List (Nat × DFrac × List ByteG)) (P : IProp GF) (E : CoPset) :
    IProp GF :=
  iprop(□ (P ={⊤, E}=∗ ∃ rs' : List (Nat × DFrac × List ByteG),
    ([∗list] r ∈ rs', osBytes (GF := GF) p r.1 r.2.1 r.2.2) ∗
    ⌜∀ i b, heldByte rs i b → heldByte rs' i b⌝ ∗
    (([∗list] r ∈ rs', osBytes (GF := GF) p r.1 r.2.1 r.2.2) ={E, ⊤}=∗ P)))

instance heldAcc_persistent (p : Ino) (rs : List (Nat × DFrac × List ByteG)) (P : IProp GF)
    (E : CoPset) : Persistent (heldAcc p rs P E) := by
  unfold heldAcc; infer_instance

/-- **Held bytes are their own accessor** (`P := [∗list] osBytes rs`, at the mask `⊤`). -/
theorem heldAcc_own (p : Ino) (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ heldAcc (GF := GF) p rs ([∗list] r ∈ rs, osBytes (GF := GF) p r.1 r.2.1 r.2.2) ⊤ := by
  unfold heldAcc
  imodintro
  iintro Hbs
  imodintro
  iexists rs
  iframe Hbs
  isplitr
  · ipureintro; exact fun _ _ h => h
  iintro Hbs
  imodintro
  iexact Hbs

end defs

end os
end Perennial
