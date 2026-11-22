/-
`datadir.ToSnapDir(dataDir)` (`server/storage/datadir/datadir.go`, translated with its body; bkarea,
2026-11-22). Lean-first; proved in `Proof/go_etcd_io/etcd/server/v3/storage/datadir/ToSnapDir.lean`.
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

/-- `ToSnapDir(d)` (`Join(ToMemberDir(d), "snap")`) of a data directory shorter than `2^60` bytes: Go's `filepath.Join(d, "member", "snap")` (`path.joinModel`; joining in two steps is joining in one, `path.joinModel_triple`). -/
abbrev datadir.ToSnapDir.spec : Prop :=
  ∀ (d : GoString), d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.datadir }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.datadir.ToSnapDir)) (Val #d))
  {{ RET #(path.joinModel [d, go!"member", go!"snap"]); True }}

end spec

end EtcdGrove
end Perennial
