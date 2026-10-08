/- Port of election_proof/spec_MemoryStorage__Entries.v (feb5c73d4).

Lean notes: `ownMemoryStorage`/`memstorageFields` (`InvMemstorage.lean`) need
ghost state, so the section has the extra variable `[AllG GF]` (porting guide,
"Section variables"); in Rocq it comes with `heapGS Σ`.
Rocq's `(#s, #interface.nil)` is `PairV #s #interface.nil`; `` `prefix_of` `` is
`<+:` (`List.IsPrefix`); `Z.to_nat` is `Int.toNat`.
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

/-- `ms.Entries(lo, hi, maxSize)` (`storage.go:131`), stated exactly as `isStorage`'s
`HEntries` asks of the method. The range premise
`prev.index + 1 <= lo < hi <= prev.index + |ents| + 1` makes all three error paths
unreachable: `lo <= ents[0].Index` (`ErrCompacted`), `hi > lastIndex + 1` (the `Panicf`)
and `len(ents) == 1` (`ErrUnavailable`). The result is `limitSize` of the sub-slice
`ents[lo-offset:hi-offset]`, re-sliced with `cap = len`; the entries are returned
read-only and for good, which `ownMemoryStorage` can allow because it holds `ms.ents`
read-only itself. -/
abbrev MemoryStorage.Entries.spec : Prop :=
  ∀ (ms : Loc) (σ : StorState)
    (lo hi maxSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms σ ∗
      ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
         uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝ }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Entries"))
      (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (s : GoSlice) (es : List raftpb.Entry), RET (PairV #s #interface.nil);
      s ↦*□ es ∗
      ⌜es ≠ [] ∧
        (es.length : Int) ≤ uint.Z hi - uint.Z lo ∧
        (∀ e, e ∈ es → e ∈ σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat) ∧
        s.cap = s.len ∧
        es <+: (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
                 (uint.Z lo - uint.Z σ.prev.index' - 1).toNat⌝ ∗
      ownMemoryStorage ms σ }}

end spec

end EtcdGrove
end Perennial
