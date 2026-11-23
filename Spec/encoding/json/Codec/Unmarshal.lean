/-
`json.Unmarshal(data, ptr)` over the encoding/json model's registered codec (mit-pdos/etcd-grove#24,
item 1): the general spec, which the kits take as a hypothesis while the model's bodies are opaque
(vr's `encoding.json.Unmarshal.spec`, the lab's `Harness/Proof/encoding/json/Valid.lean`, moved here
with the registry generic in the codec's functions `fm`, `fu`: a kit's `codecSet ∗ kitCodecOk F` is
`codecSetWith fm fu ∗ codecOkWith F fm fu` at its generated functions). A statement only: neither
assumed nor proved yet (it is proved over the model's `Unmarshal` once the bodies are translated:
`getCodec`, `valid`, then the codec's `Unmarshal`). The main tree's per-shape trust boundary
(`EtcdGrove.encoding.json.Unmarshal.spec`, a `*ConfigChangeContext`) is to become a lemma of it.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [jc : models_lab.jsoncodec.JsonCodec GF]

/-- `Unmarshal(data, ptr)`, with a codec of `fm`, `fu` registered that meets `JsonCodec` (scanner
`F`): on valid JSON (`jsonValid F bs`), the codec's decoding (`JsonCodec.dec`; `err` is nil exactly
when it decoded); else a syntax error (non-nil), with nothing decoded. -/
abbrev Unmarshal.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (fm fu : GoFunc) (data : GoSlice) (dq : DFrac) (bs : List w8)
    (ptr : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSetWith (GF := GF) fm fu ∗
      codecOkWith (GF := GF) F fm fu ∗ data ↦*{dq} bs ∗ models_lab.jsoncodec.JsonCodec.dec bs ptr Ψ }}
    (App (App (Val (@! encoding.json.Unmarshal)) (Val #data)) (Val #ptr))
  {{ (err : GoInterface), RET #err; data ↦*{dq} bs ∗
      ((⌜models_lab.jsoncodec.jsonValid F bs⌝ ∗ ∃ ok, ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok) ∨
       (⌜¬ models_lab.jsoncodec.jsonValid F bs ∧ err ≠ interface.nil⌝ ∗
         models_lab.jsoncodec.JsonCodec.dec bs ptr Ψ)) }}

end spec

end encoding.json
end Perennial
