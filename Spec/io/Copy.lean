/-
`io.Copy(io.Discard, src)` on the source of a relay's direction (names only in Perennial's `io`;
`notes/client-cut-plan.md` K1): what the bridge's copy loop does once its bridge is blackholed,
reading the source until it fails and writing nothing. The vocabulary:
`Proof/net/InvRelay.lean`.
-/
module

public import Proof.net.InvRelay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `io.Copy(dst, src)`, with `dst` the writer `io.Discard` holds and `src` the source of a
relay's direction, returns a count and an error, the bytes read from `src` extended, none
written to the direction's destination. -/
abbrev io.Copy.spec : Prop :=
  ∀ (dst : GoInterface) (l s t : GoInterfaceOk) (rd wr : List w8),
  {{ typedPointsto (globalAddr io.Discard) dst DFrac.discard ∗ relayDir (GF := GF) l s t rd wr }}
    (App (App (Val (@! io.Copy)) (Val #dst)) (Val #(interface.ok s)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ rd' : List w8, relayDir l s t (rd ++ rd') wr }}

end spec

end EtcdGrove
end Perennial
