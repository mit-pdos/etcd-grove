/-
`(*bootstrappedWAL).MemoryStorage()` (`server/v3/etcdserver/bootstrap.go:726`). Lean-first.

Constructs a `*raft.MemoryStorage` via `raft.NewMemoryStorage()`, applies `wal.snapshot` if non-nil,
sets `wal.st` if non-nil, and appends `wal.ents` if non-empty. Under `PlogWf (snapId sv) es` (which
`bootstrapWALFromSnapshot` establishes via `fillBackendAheadGap` when `cfg.ForceNewCluster` is set),
`ApplySnapshot`, `SetHardState`, and `Append` all succeed without panicking and leave the returned
`MemoryStorage` in state `{ memStorApplied sv with ents := es }`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev bootstrappedWAL.MemoryStorage.spec : Prop :=
  ∀ (w : Loc) (dq dqs dqe : DFrac) (bw : bootstrappedWAL)
    (sv : SnapshotM) (hs : HardStateM) (es : List EntryM) (cap : Int),
  PlogWf (snapId sv) es →
  uint.Z sv.Metadata'.Index' + (es.length : Int) + 1 ≤ 2 ^ 61 →
  uint.Z sv.Metadata'.Index' ≤ cap →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hwal" ∷ w ↦{dq} bw ∗
      "Hst" ∷ (⌜bw.st' = null ∧ hs = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨ hsPts bw.st' dqs hs) ∗
      "Hents" ∷ entsPts bw.ents' dqe es ∗
      "#Hsnap" ∷ snapOptRO bw.snapshot' sv }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"MemoryStorage"))
      (Val #()))
  {{ (ms : Loc), RET #ms;
      ∃ γs : MemStorNames,
        ⌜γs.cap = cap⌝ ∗
        ownMemoryStorage ms γs { memStorApplied sv with ents := es } ∗
        memStorMeta ms γs hs ∗
        memSnapTok ms γs (memStorApplied sv) ∗
        w ↦{dq} bw ∗
        hsOpt bw.st' hs ∗
        entsPts bw.ents' dqe es }}

end spec

end EtcdGrove
end Perennial
