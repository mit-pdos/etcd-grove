/- `MemoryStorage.CreateSnapshot` (`storage.go:244`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the frozen entry at `i` (so the term is the caller's), the new snapshot's validity and delivered bound (`J.DL i`: the API's delivered prefix reaching `i`), and the client's snapshot half (the stored snapshot, whose conf state a `nil` `cs` keeps). `ErrSnapOutOfDate` when `i` is at or below the stored snapshot's index. -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.CreateSnapshot(i, cs, data)`. -/
abbrev MemoryStorage.CreateSnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (i : w64) (e : EntryM) (cs : Loc)
    (dq : DFrac) (oc : Option ConfStateM) (data : GoSlice) (bs : List w8) (sv0 : SnapshotM)
    (eood : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs (uint.nat i) DFrac.discard [e] ∗
      J.SV (memSnapCreated sv0 i e.Term' oc bs) ∗ J.DL (uint.nat i) ∗
      memSnapExact γs sv0 ∗ memCsArg cs dq oc ∗ data ↦* bs ∗
      globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot")) (Val #i)) (Val #cs)) (Val #data))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      memCsArg cs dq oc ∗
      ((⌜err = interface.nil⌝ ∗ memSnapExact γs (memSnapCreated sv0 i e.Term' oc bs) ∗
         ownSnapM snap (DFrac.own 1) (memSnapCreated sv0 i e.Term' oc bs)) ∨
       (⌜snap = null ∧ err = eood ∧ uint.nat i ≤ uint.nat sv0.Metadata'.Index'⌝ ∗
         memSnapExact γs sv0 ∗ data ↦* bs)) }}

end spec

end EtcdGrove
end Perennial
