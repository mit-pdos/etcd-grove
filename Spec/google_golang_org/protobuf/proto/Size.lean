/-
`proto.Size` of a `*pb.PutRequest`: the trust boundary (`google.golang.org/protobuf` is
names-only). Lean-first.

`proto.Size(m)` returns the length of `m`'s encoding, an `int` at least `0`; it reads the
message's fields and stores the size in its size cache with an atomic store (protobuf-go's
`sizecache`). For the one call shape of the txn package (`proto.Size(p)` of a put request,
`Put`'s and `executeTxn`'s trace fields): the request's fields read-only and its size cache in
the invariant `putRequestIs` holds it in. The message's internal fields (`state`,
`unknownFields`), which `Size` also reads, are not modelled; nothing writes them after
decoding.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Size(p)` of a put request: a size, at least `0`. -/
abbrev proto.Size.spec : Prop :=
  ∀ (p : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ txn.putRequestIs p o }}
    (App (Val (@! proto.Size))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #p)))
  {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
