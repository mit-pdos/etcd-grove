/- `MemoryStorage.CreateSnapshot` (`storage.go:244`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the frozen entry at `i` (so the term is the caller's), the new snapshot's validity and delivered bound (`J.DL i`: the API's delivered prefix reaching `i`), a non-`nil` `cs` (a `nil` one keeps the stored snapshot's conf state, which a writer beside another does not know), and the stored snapshot open for writes (`memSnapLb γs 0`). Either outcome gives `memSnapLb γs i`: success stores the snapshot at `i`; `ErrSnapOutOfDate` (`i` at or below the stored snapshot's index, which another writer may have moved: etcd's apply thread against the raft goroutine's `ApplySnapshot`, `server.go:2106`) says the stored index is at least `i`.

kvreconf-snapshot-thread (2026-10-30): the exclusive `memSnapExact γs sv0` replaced by the persistent `memSnapLb`; `cs` non-`nil` (was `memCsArg`, `nil` allowed). -/
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
    (dq : DFrac) (c : ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs (uint.nat i) DFrac.discard [e] ∗
      J.SV (memSnapMade i e.Term' c bs) ∗ J.DL (uint.nat i) ∗
      memSnapLb γs 0 ∗ ownCSM cs dq c ∗ data ↦* bs ∗
      globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot")) (Val #i)) (Val #cs)) (Val #data))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownCSM cs dq c ∗ memSnapLb γs (uint.nat i) ∗
      ((⌜err = interface.nil⌝ ∗ ownSnapM snap (DFrac.own 1) (memSnapMade i e.Term' c bs)) ∨
       (⌜snap = null ∧ err = eood⌝ ∗ data ↦* bs)) }}

end spec

end EtcdGrove
end Perennial
