/- Port of election_proof/spec_MemoryStorage__Term.v (feb5c73d4).

Lean notes: `ownMemoryStorage`/`memstorageFields` (`InvMemstorage.lean`) need
ghost state, so the section has the extra variable `[AllG GF]` (porting guide,
"Section variables"); in Rocq it comes with `heapGS Σ`.
Rocq's `(#t, #interface.nil)` is `PairV #t #interface.nil`.
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

/-- `ms.Term(i)` (`storage.go:166`), stated exactly as `isStorage`'s `HTerm` asks of the
method: on the range the storage can answer for, `prev.index <= i <= prev.index +
|ents|`, it returns `termAt prev ents i` and no error. The range premise is what makes
`ErrCompacted` (`i < ents[0].Index`) and `ErrUnavailable` (`i - offset >= len(ents)`)
unreachable.

(D19i part 1, 2026-10-18) The application may have compacted the storage, up to the floor
(`σ.fl`): below its boundary `Term` answers `ErrCompacted`, which the range premise no longer
excludes; then `i0` is below the floor and the storage compacted past it (`memStorCut`). -/
abbrev MemoryStorage.Term.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (i0 : w64) (ec : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      ⌜uint.Z σ.prev.index' ≤ uint.Z i0 ∧
         uint.Z i0 ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
      -- below the pending batch (2026-10-10)
      ⌜PendFrom σ (uint.Z i0 + 1)⌝ ∗
      "#Hec" ∷ globalAddr ErrCompacted ↦□ ec }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      (⌜err = interface.nil ∧ termAt σ.prev σ.ents i0 = some t⌝ ∨
       (⌜err = ec ∧ uint.Z i0 < uint.Z σ.fl⌝ ∗ memStorCut γs (uint.Z i0 + 1))) ∗
      ownMemoryStorage ms γs σ }}

end spec

end EtcdGrove
end Perennial
