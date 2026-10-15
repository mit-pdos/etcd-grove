/-
`NewLease` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

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

/-- `NewLease(id, ttl)`: a fresh lease, its fields owned: `ID`, `ttl`, `remainingTTL` 0, its two
locks and `expiry` zero, an empty item set, a fresh `revokec`. -/
abbrev lease.NewLease.spec : Prop :=
  ∀ (id ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLease)) (Val #id)) (Val #ttl))
  {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ lsF go!"ID" l ↦ id ∗ lsF go!"ttl" l ↦ ttl ∗
      lsF go!"remainingTTL" l ↦ (W64 0) ∗
      lsF go!"expiryMu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
      lsF go!"expiry" l ↦ (zero_val _root_.Perennial.time.Time) ∗
      lsF go!"mu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
      (∃ sm : Loc, lsF go!"itemSet" l ↦ sm ∗ sm ↦$ (∅ : GMap LeaseItem Unit)) ∗
      (∃ c : GoChan, lsF go!"revokec" l ↦ c) }}

end spec

end EtcdGrove
end Perennial
