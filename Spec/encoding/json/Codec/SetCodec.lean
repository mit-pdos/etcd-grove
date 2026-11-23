/-
`SetCodec(c)` (the encoding/json model's, `model.go`) with no codec registered yet (`codecUnset`,
from the deployment's boot with `codecMu`'s mutex) and `c` a codec of `fm`, `fu`: registers it
(`codecSetWith fm fu`, for good). A second registration panics: `codecUnset` is exclusive
(mit-pdos/etcd-grove#24, J2; as net/rpc's `SetCodec`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- See the file header. -/
abbrev SetCodec.spec : Prop :=
  ∀ (fm fu : GoFunc) (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      sync.isMutex (globalAddr encoding.json.codecMu) (codecInv (GF := GF)) ∗ codecUnset (GF := GF) ∗
      codecFnsWith (GF := GF) fm fu c ∗ ⌜c ≠ null⌝ }}
    (App (Val (@! encoding.json.SetCodec)) (Val #c))
  {{ RET #(); codecSetWith (GF := GF) fm fu }}

end spec

end encoding.json
end Perennial
