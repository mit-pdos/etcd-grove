/-
`listed(ls, id)` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3, 2026-11-06,
`notes/lease-mono3-plan.md`): whether the listing `ls` has the lease `id`. Lean-first (no Rocq
counterpart).

**The triple:** for a `*LeaseLeasesResponse` whose `Leases` field is a read-only slice of the
lease ids `ids` (`leases`'s success), it returns whether `id` is one of them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
abbrev listed.spec : Prop :=
  ∀ (ls : Loc) (sl : GoSlice) (ids : List w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup ∗
      structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" ls ↦□ sl ∗
      sl ↦*□ (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.listed)) (Val #ls))
      (Val #id))
  {{ RET #(decide (id ∈ ids)); True }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
