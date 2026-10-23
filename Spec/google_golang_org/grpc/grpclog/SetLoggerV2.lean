/-
`grpclog.SetLoggerV2(l)` (`google.golang.org/grpc/grpclog`, `loggerv2.go`, names-only here): it
sets grpc's logger (a package variable of grpc's); the spec says it returns. `etcd3`'s `init`
(`logger.go`) calls it with a `klogWrapper`. The trust boundary: an axiom, `Proof/google_golang_org/grpc/grpclog/SetLoggerV2.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import GeneratedProof.google_golang_org.grpc.grpclog

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

/-- See the file header. -/
abbrev grpclog.SetLoggerV2.spec : Prop :=
  ∀ (l : val),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.grpclog.SetLoggerV2)) (Val l))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
