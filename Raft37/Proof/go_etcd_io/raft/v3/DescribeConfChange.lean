/-
The trust boundary: `DescribeConfChange` (`util.go`, raft v3.7), assumed (2026-10-16, stage R4):
its body formats through `fmt.Fprintf` into a `strings.Builder`, for which neither Perennial nor
this repository has a spec; see the spec file for the statement.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.DescribeConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A trust-boundary axiom** (raft v3.7 retarget, stage R4): `DescribeConfChange` (`util.go`)
only builds the string `stepLeader`'s conf-change refusal logs (`AsV2`, then `fmt.Fprintf` of the
transition, each change and the context into a `strings.Builder`, and `b.String()`). Its body is
translated, but `fmt.Fprintf` (to an `io.Writer` interface) and `strings.Builder` have no specs in
Perennial or here, so its triple is assumed: it returns some string and gives the conf change's
ownership back, reading nothing else and writing nothing. -/
axiom DescribeConfChange.wp_proof : DescribeConfChange.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
