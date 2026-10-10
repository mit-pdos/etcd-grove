/-
Port of election_proof/spec_MemoryStorage__FirstIndex.v (feb5c73d4).

Lean notes:
* `ownMemoryStorage` (`InvMemstorage.lean`) needs ghost state, so the section has the
  extra variable `[AllG GF]` (porting guide, "Section variables"); in Rocq it comes
  with `heapGS Σ`.
* `is_Storage_with` is `isStorageWith`; `(#fi, #interface.nil)` is `PairV #fi #interface.nil`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.FirstIndex()` (`storage.go:230`): the lock, `callStats`'s counter, the helper,
the unlock. Stated *exactly* as `isStorage`'s `HFirstIndex` asks of the method (same
return values, `err = nil`, same value), on `ownMemoryStorage` -- the one predicate for
a `MemoryStorage` -- so that `isStorageWith (ownMemoryStorage ms)` is a rearrangement
of the five public methods' specs (`InvMemstorage.lean`). -/
abbrev MemoryStorage.FirstIndex.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"FirstIndex"))
      (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜uint.Z fi = uint.Z σ.prev.index' + 1⌝ ∗
      ownMemoryStorage ms γs σ }}

end spec

end EtcdGrove
end Perennial
