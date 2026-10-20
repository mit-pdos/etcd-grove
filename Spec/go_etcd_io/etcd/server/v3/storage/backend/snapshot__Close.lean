/-
`Close` (the backend's `snapshot`, `backend.go`; translated). `s.Close()`: the warning goroutine
stopped (`close(s.stopc)`, `<-s.donec`) and the read transaction rolled back
(`s.Tx.Rollback()`). The trust boundary (D22 S-h, 2026-10-20; an axiom in
`Proof/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Close.lean`: `snapOpen` is opaque, so
the translated body has nothing to be proved over). Lean-first (no Rocq counterpart); the
vocabulary is `InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `s.Close()` of an open snapshot, the whole of it (no share left to read it after): closed
(`snapOpenQ` consumed), with a nil error. -/
abbrev backend.snapshot.Close.spec : Prop :=
  ∀ (sp : Loc) (D : Data) (γ : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapOpenQ sp D γ 1 }}
    (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"Close")) (Val #()))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
