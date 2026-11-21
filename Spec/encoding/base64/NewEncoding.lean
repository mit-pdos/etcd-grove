/-
`NewEncoding(encoder)` (`encoding/base64`, go1.27.3 `base64.go`) for a valid alphabet (64 distinct
bytes, neither `\n` nor `\r`, which the package's two alphabets are): a fresh `*Encoding` with that
alphabet and padding `=`. Proved in `Proof/encoding/base64/NewEncoding.lean`. Lean-first.
-/
module

public import Proof.encoding.base64.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

/-- `NewEncoding(s)`, `s` a valid alphabet: an `Encoding` over `s` with padding `=` (61). -/
abbrev base64.NewEncoding.spec : Prop :=
  ∀ (s : GoString), s.length = 64 → s.Nodup → (10 : w8) ∉ s → (13 : w8) ∉ s →
  {{ (True : IProp GF) }}
    (App (Val (@! _root_.Perennial.encoding.base64.NewEncoding)) (Val #s))
  {{ (e : Loc), RET #e; ∃ enc : _root_.Perennial.encoding.base64.Encoding, e ↦ enc ∗
      ⌜enc.encode'.arr = s ∧ enc.padChar' = W32 61⌝ }}

end spec

end EtcdGrove
end Perennial
