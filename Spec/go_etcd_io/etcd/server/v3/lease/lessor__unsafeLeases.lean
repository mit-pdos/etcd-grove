/-
`(*lessor).unsafeLeases` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); the lease-read plan
(`notes/lease-read-plan.md`, 2026-10-31).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.unsafeLeases()`, `le.mu` read-locked (its guarded state at `q`): a fresh slice of the lease
map's values, each lease once with its id (`(l, id)` the map's pairs). -/
abbrev lease.lessor.unsafeLeases.spec : Prop :=
  ∀ (lp lm : Loc) (M : GMap w64 Loc) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"unsafeLeases")) (Val #()))
  {{ (sl : GoSlice) (ls : List (Loc × w64)), RET #sl; lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗
      lm ↦${DFrac.own q} M ∗ sl ↦* ls.map Prod.fst ∗
      ⌜(ls.map Prod.snd).Nodup ∧ ∀ (id : w64) (l : Loc), (l, id) ∈ ls ↔ M.lookup id = some l⌝ }}

end spec

end EtcdGrove
end Perennial
