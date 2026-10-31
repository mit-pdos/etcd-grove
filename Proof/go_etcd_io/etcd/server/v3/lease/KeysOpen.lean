/-
`(*Lease).Keys` by the lease owner, over its resource opened at the lease (`leaseOwnOpen`, which
`lessor.Lookup` gives; the lease-keys plan, item 1, 2026-10-31): a corollary of
`lease.Lease.Keys.spec`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`l.Keys()` by the owner of the opened lease `l` of `id`**: exactly the keys the owner's
item map `I` attaches to `id`, no duplicates; the opened resource back. -/
abbrev lease.Lease.Keys.specOpen : Prop :=
  ∀ (γl : GName) (L : List w64) (I : GMap LeaseItem w64) (id : w64) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      leaseOwnOpen γl L I id l }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"Keys")) (Val #()))
  {{ (s : GoSlice) (ks : List GoString), RET #s; s ↦* ks ∗ leaseOwnOpen γl L I id l ∗
      ⌜(∀ k : GoString, k ∈ ks ↔ I.lookup (LeaseItem.mk k) = some id) ∧ ks.Nodup⌝ }}

/-- `Keys()` over the opened resource, from its spec. -/
theorem lease.Lease.Keys.spec_open (h : lease.Lease.Keys.spec (GF := GF) (hG := hG)) :
    lease.Lease.Keys.specOpen (GF := GF) (hG := hG) := by
  intro γl L I id l
  iintro %Φ ⟨#Hpkg, Ho⟩ HΦ
  iunfold leaseOwnOpen at Ho
  icases Ho with ⟨#Hl, Hio, Hslot, Hback⟩
  iapply (h l I id) $$ [Hio Hslot]
  · iframe Hpkg Hl Hio Hslot
  iintro !> %s %ks ⟨Hs, Hslot, Hio, %Hks⟩
  iapply HΦ
  iframe Hs
  isplitl
  · iunfold leaseOwnOpen; iframe Hl Hio Hslot Hback
  · ipureintro; exact Hks

end spec

end EtcdGrove
end Perennial
