/-
`fixTrailer(header, chunked, maxHeaders)` on an empty header (no `Trailer`): `nil, nil`, the header
still empty. Proved in `Net/Proof/net/http/fixTrailer.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev fixTrailer.spec : Prop :=
  ∀ (h : Loc) (chunked : Bool) (maxH : w64),
  {{ (h ↦$ (∅ : GMap GoString GoSlice) : IProp GF) }}
    (App (App (App (Val (@! net.http.fixTrailer)) (Val #h)) (Val #chunked)) (Val #maxH))
  {{ RET (PairV #map.nil #interface.nil); h ↦$ (∅ : GMap GoString GoSlice) }}

end spec

end net.http
end Perennial
