/-
`newKVHasher` (`hash.go`): the trust boundary (crc32 has no Perennial model; `hash.go` is names-only).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `newKVHasher(prev, rev, keep)` returns some hasher (its `keep` the map given; its value is
opaque: `kvHasher` is an axiomatized type). -/
abbrev mvcc.newKVHasher.spec : Prop :=
  ∀ (prev rev : w64) (keep : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher)) (Val #prev))
      (Val #rev)) (Val #keep))
  {{ (h : kvHasher), RET #h; True }}

end spec

end EtcdGrove
end Perennial
