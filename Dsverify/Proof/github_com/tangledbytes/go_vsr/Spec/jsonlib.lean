/-
The vr kit's names over the main tree's `encoding/json` registry (`Proof/encoding/json/Registry.lean`,
J1/J2 of mit-pdos/etcd-grove#24: `codecOkWith`, `codecFnsWith`, `codecSetWith`, `DecoderRep`,
`EncoderRep`, `isSpaceB`, which moved there from this file). **Definitions only.** Names are the
lab's.

* `kitFn` (the kit's generated functions: `jsonMarshal`, `jsonUnmarshal` in `examples/vsrnet`;
  the lab's `JsonKit.pkg` is that package's path), `kitCodecOk F` (= the main tree's
  `codecOkWith F` at the kit's functions), `codecFns c` (= `codecFnsWith` at them) and `codecSet`
  (the kit's codec registered: `codec ↦□ c` with `codecFns c`; **without** the registry's mutex,
  which the main tree's `codecSetWith` adds for J2's `getCodec`: notes/dsv-vr.md, "JSON on the main
  tree").
* `bufio.errWf`, `bufio.errOrNil` are the main tree's (`Proof/bufio/ErrOrNil.lean`).
-/
module

public import Proof.encoding.json.Registry
public import Net.Proof.models_lab.Errors
public import Proof.bufio.ErrOrNil

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- The package of the kit's generated codec functions (the lab's `JsonKit.pkg`). -/
def kitPkg : GoString := go!"github.com/tangledbytes/go-vsr/examples/vsrnet"

/-- The kit's generated function `name` (in `kitPkg`). -/
def kitFn [GooseExts] [GoSemanticsFunctions] (name : GoString) : GoFunc :=
  functions (kitPkg ++ go!"." ++ name) []

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [jc : models_lab.jsoncodec.JsonCodec GF]

/-- The kit's codec functions meet `JsonCodec`, and `jsoncodec.Scan` computes `F` (persistent). -/
def kitCodecOk (F : List w8 → Bool → w64 × w64) : IProp GF :=
  codecOkWith F (kitFn go!"jsonMarshal") (kitFn go!"jsonUnmarshal")

instance kitCodecOk_persistent F : Persistent (kitCodecOk (GF := GF) F) := by
  unfold kitCodecOk; infer_instance

end defs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- The `*Codec` `c` holds the kit's codec functions, for good (persistent). -/
def codecFns (c : Loc) : IProp GF :=
  codecFnsWith (kitFn go!"jsonMarshal") (kitFn go!"jsonUnmarshal") c

instance codecFns_persistent (c : Loc) : Persistent (codecFns (GF := GF) c) := by
  unfold codecFns; infer_instance

/-- A codec with the kit's functions is registered, for good (persistent). -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.json.codec ↦□ c ∗ codecFns c)

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

end defs2

end encoding.json

end Perennial
