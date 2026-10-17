/-
`grpc.WithResolvers(rs...)` (grpc's `dialoptions.go`, names only; item 5). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithResolvers(rs...)` of the builders `rbs` (read-only): a dial option adding them to
the dial's resolvers. -/
abbrev grpc.WithResolvers.spec : Prop :=
  ∀ (sl : GoSlice) (rbs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ rbs }}
    (App (Val (@! google_golang_org.grpc.WithResolvers)) (Val #sl))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o (.resolvers rbs)⌝ }}

end spec

end EtcdGrove
end Perennial
