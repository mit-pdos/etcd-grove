/-
`grpcutil.IsCompressorNameRegistered(name)` (grpc's `internal/grpcutil/compressor.go`): whether a
compressor of that name is registered; none is (`grpcutilInit`: `RegisteredCompressorNames` holds the
nil slice for good).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `IsCompressorNameRegistered(name)` returns `false`. -/
abbrev grpcutil.IsCompressorNameRegistered.spec : Prop :=
  ∀ (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.grpcutil }}
    (App (Val (@! google_golang_org.grpc.internal.grpcutil.IsCompressorNameRegistered)) (Val #name))
  {{ RET #false; True }}

end spec

end EtcdGrove
end Perennial
