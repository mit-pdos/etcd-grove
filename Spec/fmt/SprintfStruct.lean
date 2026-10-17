/-
`fmt.Sprintf` with a `membership.Attributes` argument: the trust boundary, for the one call shape the server's `publishV3` makes (etcd-io/etcd#22527, branch
`pr-verify/etcd-22527`): `fmt.Sprintf("%+v", s.attributes)` with a `membership.Attributes`.
Perennial's `fmt.wp_Sprintf` admits arguments of predeclared basic types only (`fmt.ArgsWf`), and
`fmt.SprintfNamed` (`Spec/fmt/SprintfNamed.lean`) named types with a basic underlying type; a
struct is neither. A spec of its own, so that the callers that need only those do not rest on it.
It says nothing of the output (the struct's fields are formatted by reflection; no caller reads
the string but a logger). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.fmt
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.membership

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Sprintf(format, av)` with one argument, a `membership.Attributes` value `av`
(`struct { Name string; ClientURLs []string }`, no methods: `server/etcdserver/api/membership/
member.go`), whose `ClientURLs` slice the caller can read (`↦*□`: Go's `fmt` reads its backing
array, field by field, by reflection), returns some string and gives the arguments' slice back.
At the trust boundary (`fmt.SprintfStruct.wp_proof`, `Proof/fmt/SprintfStruct.lean`). -/
abbrev fmt.SprintfStruct.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice)
    (av : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (urls : List GoString)
    (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        args ↦*{dq} [interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes.ty #av] ∗
        av.ClientURLs' ↦*□ urls }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s;
        args ↦*{dq} [interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes.ty #av] }}

end spec

end EtcdGrove
end Perennial
