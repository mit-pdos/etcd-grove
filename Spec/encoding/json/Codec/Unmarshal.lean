/-
`json.Unmarshal(data, ptr)` over the encoding/json model's registered codec (mit-pdos/etcd-grove#24,
item 1): the general spec, which the kits take as a hypothesis while the model's bodies are opaque
(vr's `encoding.json.Unmarshal.spec`, the lab's `Harness/Proof/encoding/json/Valid.lean`, moved here
with the registry generic in the codec's functions `fm`, `fu`: a kit's `codecSet ∗ kitCodecOk F` is
`codecSetWith fm fu ∗ codecOkWith F fm fu` at its generated functions). Since #24 J2/J3
(2026-11-23), with the per-type dispatch and the contract `J` explicit (`unmarshalVia J F ptr`,
whose codec case is the former `codecSetWith fm fu ∗ codecOkWith F fm fu`), proved over the model's
`Unmarshal` (`Proof/encoding/json/Codec/Unmarshal.lean`). The main tree's per-shape trust boundary
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions]

/-- `Unmarshal(data, ptr)`: by `ptr`'s dynamic type's method set, its `JSONModelUnmarshal` (jsongen's
same-package method), else the registered codec (`unmarshalVia J F ptr`: the route's contract `J`,
the scanner `F`): on valid JSON (`jsonValid F bs`), `J`'s decoding (`J.dec`; `err` is nil exactly
when it decoded); else a syntax error (non-nil), with nothing decoded (`unmarshalRet`). -/
abbrev Unmarshal.spec : Prop :=
  ∀ (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) (data : GoSlice)
    (dq : DFrac) (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ unmarshalVia J F ptr ∗
      data ↦*{dq} bs ∗ J.dec bs ptr Ψ }}
    (App (App (Val (@! encoding.json.Unmarshal)) (Val #data)) (Val #ptr))
  {{ (err : GoInterface), RET #err; data ↦*{dq} bs ∗ unmarshalRet J F bs ptr Ψ err }}

end spec

end encoding.json
end Perennial
