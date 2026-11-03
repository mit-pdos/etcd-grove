/- Lean-first (no Rocq counterpart).

`m.createSnapshot(i, cs, data)` (storage.go): `MemoryStorage.CreateSnapshot` on the image: refused
with `ErrSnapOutOfDate` (`eood`), the image unchanged, when `i` is at most its snapshot's index
(`imgCreateStale`); otherwise `nil`, and the image holds `imgCreateSnapshot I i co bs`: the snapshot
at `i` and the log's term there, of the configuration `cs` (read-only for good, `co = some c`; the
old snapshot's if `cs` is `nil`, `co = none`) and a copy of the data (only read). It does not panic:
when not refused, `i` is within the log (from its start to its last index).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev image.createSnapshot.spec : Prop :=
  ∀ (p : Loc) (I : StorFile) (i : w64) (cs : Loc) (co : Option ConfStateM) (data : GoSlice)
    (dq : DFrac) (bs : List w8) (eood : GoInterface),
  (imgCreateStale I i ∨ uint.nat I.prev ≤ uint.nat i ∧ uint.nat i ≤ uint.nat I.prev + I.ents.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      ownImage p I ∗
      (match co with
       | none => iprop(⌜cs = null⌝)
       | some c => ownCSM cs DFrac.discard c) ∗
      data ↦*{dq} bs ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (p @!! go.GoType.PointerType kImageTy @!! go!"createSnapshot")) (Val #i))
      (Val #cs)) (Val #data))
  {{ (err : GoInterface), RET #err; data ↦*{dq} bs ∗
      (if imgCreateStale I i then iprop(⌜err = eood⌝ ∗ ownImage p I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage p (imgCreateSnapshot I i co bs))) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
