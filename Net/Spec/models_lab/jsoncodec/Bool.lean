/-
`jsoncodec.Bool(b, i)` on a JSON boolean at `i` (`true` or `false`, no whitespace before it): the
boolean, `Set`, the index after it. A spec at the inputs the generated decoders meet (valid JSON),
in the form of dsverify-lab's `String`/`Uint` (`Net/Spec/models_lab/jsoncodec/`). Proved in
`Net/Proof/models_lab/jsoncodec/Bool.lean` (#24 J2 batch 2b).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits
public import Net.Proof.models_lab.jsoncodec.Scan.Idx

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.jsoncodec

/-- The JSON literal of a boolean. -/
def boolLit (x : Bool) : List w8 := if x then go!"true" else go!"false"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev Bool.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (x : _root_.Bool) (rest : List w8)
    (hb : bs.drop (uint.nat i) = boolLit x ++ rest),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.Bool')) (Val #b)) (Val #i))
  {{ RET (PairV (PairV #x #(W64 0))
        #(W64 ((uint.nat i + (boolLit x).length : Nat) : Int))); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
