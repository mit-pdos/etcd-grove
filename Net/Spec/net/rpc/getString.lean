/-
`getString(p)` on a payload `bs` (read, any fraction): `(s, rest, true)` when `bs` is `strEnc s`
followed by `rest`'s bytes `r` (`rest` a sub-slice of `p`, which keeps the fraction of `r`);
`ok = false` when `bs` does not start with an encoded string (shorter than 8 bytes, or a length
beyond its end). Proved in `Net/Proof/net/rpc/getString.lean`.
-/
module

public import Net.Proof.net.rpc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- See the file header. -/
abbrev getString.spec : Prop :=
  ∀ (p : GoSlice) (dq : DFrac) (bs : List w8),
  {{ (p ↦*{dq} bs : IProp GF) }}
    (App (Val (@! net.rpc.getString)) (Val #p))
  {{ (s : GoString) (rest : GoSlice) (ok : Bool), RET (PairV (PairV #s #rest) #ok);
      if ok then ∃ r, ⌜bs = strEnc s ++ r⌝ ∗ rest ↦*{dq} r
      else ⌜¬ ∃ s' r, bs = strEnc s' ++ r⌝ }}

end spec

end net.rpc
end Perennial
