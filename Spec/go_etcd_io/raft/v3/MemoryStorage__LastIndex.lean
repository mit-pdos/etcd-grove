/- Port of election_proof/spec_MemoryStorage__LastIndex.v (feb5c73d4).

Lean notes: `ownMemoryStorage`/`memstorageFields` (`InvMemstorage.lean`) need
ghost state, so the section has the extra variable `[AllG GF]` (porting guide,
"Section variables"); in Rocq it comes with `heapGS Σ`.
Rocq's `(#li, #interface.nil)` is `PairV #li #interface.nil`.
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.LastIndex()` (`storage.go:211`): the lock, `callStats`'s counter, the helper, the
unlock. Stated *exactly* as `isStorage`'s `HLastIndex` asks of the method (same return
values, `err = nil`, same value), on `ownMemoryStorage` -- the one predicate for a
`MemoryStorage` -- so that `isStorageWith (ownMemoryStorage ms)` is a rearrangement of
the five public methods' specs (`InvMemstorage.lean`). -/
abbrev MemoryStorage.LastIndex.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      -- nothing pending (2026-10-10)
      ⌜σ.pend = []⌝ }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil);
      ⌜uint.Z li = uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
      ownMemoryStorage ms γs σ }}

end spec

end EtcdGrove
end Perennial
