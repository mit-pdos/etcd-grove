/-
`datadir.ToBackendFileName(dataDir)` (`server/storage/datadir/datadir.go`, translated with its body; bkarea,
2026-11-22). Lean-first; proved in `Proof/go_etcd_io/etcd/server/v3/storage/datadir/ToBackendFileName.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.datadir.PkgInit
public import Proof.path.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ToBackendFileName(d)` (`Join(ToSnapDir(d), "db")`) of a data directory shorter than `2^60` bytes: the name `db` in `filepath.Join(d, "member", "snap")`, which is clean and ends in the element `snap`, so the join appends `/db` (`path.joinModel_triple_snoc`). -/
abbrev datadir.ToBackendFileName.spec : Prop :=
  ∀ (d : GoString), d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.datadir }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.datadir.ToBackendFileName)) (Val #d))
  {{ RET #(path.joinModel [d, go!"member", go!"snap"] ++ [path.slash] ++ go!"db"); True }}

end spec

end EtcdGrove
end Perennial
