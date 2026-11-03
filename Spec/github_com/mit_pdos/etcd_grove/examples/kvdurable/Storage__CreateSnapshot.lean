/- Lean-first (no Rocq counterpart).

`s.CreateSnapshot(i, cs, data)` (storage.go): the image's snapshot (`image.createSnapshot`, which
copies the data), whose answer it returns, then `MemoryStorage.CreateSnapshot(i, cs, data)` (which may
keep the data). Stated over any triple of the `MemoryStorage`'s call that takes the data `bs` at `dq`
(`MemoryStorage.CreateSnapshot.spec`'s, with `P` the rest of its precondition and `Q` its
postcondition), under the image's premises (the configuration `cs`, read-only for good, or `nil`):
the caller holds the replica's `dmu` (the image), or owns the storage before its node runs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorage

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

/-- See the file header. -/
abbrev Storage.CreateSnapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (ip : Loc) (I : StorFile) (i : w64) (cs : Loc)
    (co : Option ConfStateM) (data : GoSlice) (dq : DFrac) (bs : List w8) (eood : GoInterface)
    (P : IProp GF) (Q : Loc → GoInterface → IProp GF),
  (imgCreateStale I i ∨ uint.nat I.prev ≤ uint.nat i ∧ uint.nat i ≤ uint.nat I.prev + I.ents.length) →
  {{ P ∗ data ↦*{dq} bs }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
      (Val #i)) (Val #cs)) (Val #data))
  {{ (snap : Loc) (e : GoInterface), RET (PairV #snap #e); Q snap e }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      kdStorRec s ms γs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip I ∗
      (match co with
       | none => iprop(⌜cs = null⌝)
       | some c => ownCSM cs DFrac.discard c) ∗
      data ↦*{dq} bs ∗ globalAddr ErrSnapOutOfDate ↦□ eood ∗ P }}
    (App (App (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"CreateSnapshot")) (Val #i))
      (Val #cs)) (Val #data))
  {{ (err : GoInterface), RET #err; (∃ (snap : Loc) (e : GoInterface), Q snap e) ∗
      (if imgCreateStale I i then iprop(⌜err = eood⌝ ∗ ownImage ip I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage ip (imgCreateSnapshot I i co bs))) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
