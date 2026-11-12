/-
`checkKeyInterval` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `checkKeyInterval(lg, p, key, rangeEnd, permtyp)`: the tree of the permission type (`READ`
the read tree, `WRITE` the write tree; otherwise `lg.Panic`) queried with `[key, rangeEnd)`
(`rangeEnd` `nil` when open-ended; `Contains`): for a non-empty key and an open-ended or proper
range, whether the entries cover every key of the queried interval (`queryIvl`, `adt.inIvl`;
`adt.containsRes_iff`), else some boolean; the slices kept. -/
abbrev auth.checkKeyInterval.spec : Prop :=
  ∀ (lg p : Loc) (Lr Lw : List adt.Entry) (key re : GoSlice) (k e : GoString) (dk de : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ permsAt p Lr Lw ∗
      key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyInterval)) (Val #lg))
      (Val #p)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜k ≠ [] → (auth.isOpenEnded e ∨ go.GoStringLt k e) →
        (b = true ↔ ∀ x, adt.inIvl (queryIvl k e) x →
          ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 x)⌝ }}

end spec

end EtcdGrove
end Perennial
