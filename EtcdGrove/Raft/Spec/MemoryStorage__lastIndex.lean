/- Port of election_proof/spec_MemoryStorage__lastIndex.v (feb5c73d4).

Lean notes: `memstorageFields` (`InvMemstorage.lean`) needs ghost state, so the section
has the extra variable `[AllG GF]` (porting guide, "Section variables"); in Rocq it
comes with `heapGS Σ`.
-/
import EtcdGrove.Raft.InvMemstorage

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.lastIndex()` (`storage.go:215`): `ents[0].Index + len(ents) - 1`. Called with
the lock held, so it is stated on `memstorageFields`, the lock's contents, rather than
on `ownMemoryStorage`. The bound is a premise: the sum cannot wrap. -/
abbrev MemoryStorage.lastIndex.spec : Prop :=
  ∀ (ms : Loc) (prev : entryID) (ents : List raftpb.Entry) (ss : entryID),
  uint.Z prev.index' + (ents.length : Int) < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hf" ∷ memstorageFields ms prev ents ss }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"lastIndex")) (Val #()))
  {{ (li : w64), RET #li;
      ⌜uint.Z li = uint.Z prev.index' + (ents.length : Int)⌝ ∗
      memstorageFields ms prev ents ss }}

end spec

end EtcdGrove
end Perennial
