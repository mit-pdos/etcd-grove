/-
`(*bootstrappedWAL).CommitedEntries()` (`server/v3/etcdserver/bootstrap.go:740`). Lean-first.

Iterates over `wal.ents`, returning the prefix of entries whose index is at most `wal.st.GetCommit()`
(logging `"discarding uncommitted WAL entries"` and returning `wal.ents[:i]` at the first entry with
`ent.GetIndex() > wal.st.GetCommit()`, or returning `wal.ents` when all entries are committed).
Under `PlogWf (snapId sv) es` and `uint.Z sv.Metadata'.Index' ≤ uint.Z hs.Commit'`, the returned
slice holds `es.take (uint.Z hs.Commit' - uint.Z sv.Metadata'.Index').toNat` with its capacity.
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

abbrev bootstrappedWAL.CommitedEntries.spec : Prop :=
  ∀ (w : Loc) (dq dqs : DFrac) (bw : bootstrappedWAL)
    (sv : SnapshotM) (hs : HardStateM) (es : List EntryM),
  bw.lg' ≠ null →
  PlogWf (snapId sv) es →
  uint.Z sv.Metadata'.Index' ≤ uint.Z hs.Commit' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hwal" ∷ w ↦{dq} bw ∗
      "Hst" ∷ hsPts bw.st' dqs hs ∗
      "Hents" ∷ entsPts bw.ents' (DFrac.own 1) es ∗
      "Hcap" ∷ ownSliceCap Loc bw.ents' (DFrac.own 1) }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"CommitedEntries"))
      (Val #()))
  {{ (ents' : GoSlice), RET #ents';
      w ↦{dq} bw ∗
      hsPts bw.st' dqs hs ∗
      entsPts ents' (DFrac.own 1) (es.take (uint.Z hs.Commit' - uint.Z sv.Metadata'.Index').toNat) ∗
      ownSliceCap Loc ents' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
