/-
`errAny err`: `err` is a non-nil error whose dynamic type implements `error` (it is in `error`'s
type set) with some `Error()` (any message, no precondition), persistently. What the codec
obligations (`pbcodec/Codec.lean`, `jsoncodec/Codec.lean`) and the models' error results say of an
error they do not describe further. Ported from dsverify-lab's `net.rpc.errAny`
(`Harness/Proof/net/rpc/Defs.lean`, `348a866`), moved here (namespace `models_lab`) as the codecs
are its first users.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace models_lab

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def errAny (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ msg : GoString, Φ #msg) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errAny_persistent (err : GoInterface) : Persistent (errAny (GF := GF) err) := by
  unfold errAny; infer_instance

theorem errAny_ne_nil (err : GoInterface) : errAny (GF := GF) err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errAny
  iintro ⟨%e, %h, -, -⟩
  ipureintro
  subst h
  intro h'
  cases h'

end defs

end models_lab
end Perennial
