/-
`grpclog.SetLoggerV2(l)` (`google.golang.org/grpc/grpclog`, `loggerv2.go`, names-only here): it
sets grpc's logger (a package variable of grpc's); the spec says it returns, for a logger whose dynamic
type is not grpc's `*componentData`. `etcd3`'s `init` (`logger.go`) calls it with a `klogWrapper`. The
trust boundary: an axiom, `Proof/google_golang_org/grpc/grpclog/SetLoggerV2.lean`. Lean-first (no Rocq
counterpart).

(prove-grpcsmall, 2026-11-20) Its premise was `True`, which is false: grpc v1.84.0's `SetLoggerV2`
(`grpclog/loggerv2.go:35-41`) panics ("cannot use component logger as grpclog logger") when `l` is a
`*componentData`, which the exported `grpclog.Component(name)` returns. The premise now excludes that
dynamic type (a nil `l` returns: the type assertions are comma-ok); `notes/axiom-review/setloggerv2.md`,
`notes/specs-only/ledger.md`.
-/
module

public import GeneratedProof.google_golang_org.grpc.grpclog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev grpclog.SetLoggerV2.spec : Prop :=
  ∀ (l : GoInterface),
  (∀ v : val, l ≠ interface.mkOk
    (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty) v) →
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.grpclog.SetLoggerV2)) (Val #l))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
