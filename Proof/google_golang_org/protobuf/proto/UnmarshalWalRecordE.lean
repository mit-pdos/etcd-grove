/-
The trust boundary: `proto.UnmarshalWalRecordE.spec` (names-only; `proto.Unmarshal` of a WAL record into a
blank `*walpb.Record`, with its error's identity: not `io.EOF`, and `errors.Is` on it returns). Why it holds
in Go: `Spec/google_golang_org/protobuf/proto/UnmarshalWalRecordE.lean`'s header. **Interim**: retired by
etcd-grove#37 S3, which proves it from `proto.UnmarshalPb`'s trust-boundary spec extended with the error's
identity.
-/
module

public import Spec.google_golang_org.protobuf.proto.UnmarshalWalRecordE

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.UnmarshalWalRecordE.spec`, assumed (see the file header; interim, retired by etcd-grove#37 S3). -/
axiom proto.UnmarshalWalRecordE.wp_proof : proto.UnmarshalWalRecordE.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
