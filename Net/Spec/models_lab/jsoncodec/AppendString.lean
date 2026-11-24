/-
`jsoncodec.AppendString(b, s)` on a string of bytes in `0x20..0x7e` other than `"`, `\\`, `<`, `>`, `&`
(`JsonScan.plainEnc`): `b` with `"`, `s`, `"` after it, as real encoding/json writes such a string.
Only the plain subset is specified: the spec holds of the function whether it panics outside the
subset (today's model) or escapes as encoding/json does (zeldovich's `jsonQuote` work, #24): one
canonical spec for either. Proved in `Net/Proof/models_lab/jsoncodec/AppendString.lean`; ported
from dsverify-lab's `wp_AppendString` (`GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev AppendString.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (str : GoString)
    (hs : ∀ c ∈ str, JsonScan.plainEnc c),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.AppendString)) (Val #b)) (Val #str))
  {{ (b' : GoSlice), RET #b';
      b' ↦* (bs ++ (34#8 :: (str ++ [34#8]))) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.jsoncodec
end Perennial
