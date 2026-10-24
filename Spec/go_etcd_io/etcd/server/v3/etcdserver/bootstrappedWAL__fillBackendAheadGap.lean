/-
`(*bootstrappedWAL).fillBackendAheadGap()` (`server/v3/etcdserver/bootstrap.go:765`, added in
`etcd-io/etcd#22655`). Lean-first.

Computes `lastIndex` (`wal.ents[len(wal.ents)-1].GetIndex()` when `len(wal.ents) > 0`, else
`wal.snapshot.GetMetadata().GetIndex()`, i.e. `walLastIndex sv es`) and `commit := wal.st.GetCommit()`.
If `commit <= lastIndex`, returns immediately (`gapEntries = []`). Otherwise, logs `"backend
consistent index is ahead of the WAL, filling the gap with empty entries"`, builds
`gapEnts := gapEntries hs.Term' (walLastIndex sv es) hs.Commit'` (`EntryNormal` entries with empty
`Data`, `Term = wal.st.GetTerm()`, and `Index = lastIndex + 1 .. commit`), and calls
`wal.AppendAndCommitEntries(gapEnts)`.

In both cases, when `uint.Z (walLastIndex sv es) ≤ uint.Z hs.Commit'`, `wal.ents` becomes
`es ++ gapEntries hs.Term' (walLastIndex sv es) hs.Commit'` and `wal.st` remains at `hs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev bootstrappedWAL.fillBackendAheadGap.spec : Prop :=
  ∀ (w : Loc) (bw : bootstrappedWAL) (sv : SnapshotM) (hs : HardStateM) (es : List EntryM),
  bw.lg' ≠ null →
  uint.Z (walLastIndex sv es) ≤ uint.Z hs.Commit' →
  uint.Z hs.Commit' + 1 < 2 ^ 64 →
  (es.length : Int) + (uint.Z hs.Commit' - uint.Z (walLastIndex sv es)) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hwal" ∷ w ↦ bw ∗
      "Hst" ∷ hsPts bw.st' (DFrac.own 1) hs ∗
      "Hents" ∷ entsPts bw.ents' (DFrac.own 1) es ∗
      "Hcap" ∷ ownSliceCap Loc bw.ents' (DFrac.own 1) ∗
      "#Hsnap" ∷ snapOptRO bw.snapshot' sv ∗
      "#Hsave" ∷ bootWalSaveOk bw.w' }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"fillBackendAheadGap"))
      (Val #()))
  {{ RET #();
      ∃ ents' : GoSlice,
        w ↦ { bw with ents' := ents' } ∗
        hsPts bw.st' (DFrac.own 1) hs ∗
        entsPts ents' (DFrac.own 1) (es ++ gapEntries hs.Term' (walLastIndex sv es) hs.Commit') ∗
        ownSliceCap Loc ents' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
