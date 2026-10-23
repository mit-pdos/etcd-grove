/-
`checkKeyPoint` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2; the auth plan's S2, 2026-10-23).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `checkKeyPoint(lg, p, key, permtyp)`: the tree of the permission type (`READ` the read tree,
`WRITE` the write tree; otherwise `lg.Panic`) queried with the point `key` (`Intersects`): whether
some entry holds the key (`adt.inIvl`; `adt.stab_point_iff`); the key's slice kept. -/
abbrev auth.checkKeyPoint.spec : Prop :=
  ∀ (lg p : Loc) (Lr Lw : List adt.Entry) (key : GoSlice) (k : GoString) (dk : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ permsAt p Lr Lw ∗
      key ↦*{dk} k ∗ ⌜permTypOk pt⌝ ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyPoint)) (Val #lg)) (Val #p))
      (Val #key)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗
      ⌜b = true ↔ ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 k⌝ }}

end spec

end EtcdGrove
end Perennial
