/-
`openWALFromPosition(cfg, pos)` (`bootstrap.go`, added by etcd-io/etcd#19693, which renames
`openWALFromSnapshot`; pr-verify, 2026-10-17): the trust boundary of the WAL. Lean-first (no Rocq
counterpart); see `InvBootWALFromBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWALFromBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

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

/-- `openWALFromPosition(cfg, pos)`: `wal.Open(lg, cfg.WALDir(), pos)` and `w.ReadAll()` (a torn
tail repaired once, any other failure `lg.Fatal`: not covered), the metadata decoded. It returns
the WAL, its last hard state (`nil` or read-only), the entries after `pos` (`EntsAfter`: owned
slice, read-only entries) and a fresh `snapshotMetadata`. What the hard state is is not related
to `pos`: the WAL's last `HardState` record. -/
abbrev openWALFromPosition.spec : Prop :=
  ∀ (cv : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (pos : go_etcd_io.etcd.server.v3.storage.wal.Position),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (Val (@! openWALFromPosition)) (Val #cv)) (Val #pos))
  {{ (w st : Loc) (ents : GoSlice) (mdp : Loc), RET (PairV (PairV (PairV #w #st) #ents) #mdp);
      ∃ (hs : HardStateM) (p : List EntryM) (mv : snapshotMetadata),
        hsOpt st hs ∗ entsPts ents (DFrac.own 1) p ∗ ⌜EntsAfter pos.Index' p⌝ ∗ mdp ↦ mv }}

end spec

end EtcdGrove
end Perennial
