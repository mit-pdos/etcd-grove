/-
`grpcutil.RegisteredCompressors()` (grpc's `internal/grpcutil/compressor.go`): the registered
compressors' names, comma-separated; none is registered (`grpcutilInit`), so the empty string.
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

/-- `RegisteredCompressors()` returns `""`. -/
abbrev grpcutil.RegisteredCompressors.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.grpcutil }}
    (App (Val (@! google_golang_org.grpc.internal.grpcutil.RegisteredCompressors)) (Val #()))
  {{ RET #([] : GoString); True }}

end spec

end EtcdGrove
end Perennial
