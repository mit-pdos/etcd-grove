/-
`schema.unsafeReadAuthRevision(tx)` (`auth.go`): the big-endian value the `auth` bucket holds at
`authRevision`, `0` if none (`revisionOf`; the value 8 bytes: `revWf`, else `BigEndian.Uint64`
panics), read through the `UnsafeReader` `tx` over the snapshot `D` under the token `H`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The reader `r` over the auth buckets `D` (its revision 8 bytes) under `H`: returns
`revisionOf D`. -/
abbrev schema.unsafeReadAuthRevision.spec : Prop :=
  ∀ (r : GoInterfaceOk) (H : IProp GF) (D : schema.AuthData), schema.revWf D.auth →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.authReader r H D ∗ H }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthRevision)) (Val #(GoInterface.ok r)))
  {{ (x : w64), RET #x; H ∗ ⌜x = schema.revisionOf D⌝ }}

end spec

end EtcdGrove
end Perennial
