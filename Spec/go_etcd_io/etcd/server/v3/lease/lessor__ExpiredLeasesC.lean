/-
`(*lessor).ExpiredLeasesC` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.ExpiredLeasesC()`: the lessor's `expiredC`, a channel of slices of leases, some lease of
each meeting the lessor's grant guard `GA` (D19n, 2026-10-18; until then no logical content). -/
abbrev lease.lessor.ExpiredLeasesC.spec : Prop :=
  ∀ (lp : Loc) (GA : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorExpiredC lp GA }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"ExpiredLeasesC")) (Val #()))
  {{ (c : GoChan), RET #c; ∃ γc : ChanNames,
      isChanBag γc c (V := GoSlice) (fun _ => iprop(∃ id : w64, GA id)) }}

end spec

end EtcdGrove
end Perennial
