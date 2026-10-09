/-
`confchange.joint(cfg)` is `len(outgoing(cfg.Voters)) > 0`. Lean-first (no Rocq
counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `joint` of a config whose outgoing voter map is `nil` is `false`: `len` of the nil
map is `0`. Stated for that case only, the one this development reaches. -/
abbrev confchange.joint.spec : Prop :=
  ∀ (cfg : tracker.Config) (v : Loc),
  cfg.Voters'.arr = [v, map.nil] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange }}
    (App (Val #(functions confchange.joint [])) (Val #cfg))
  {{ RET #false; True }}

end spec

end EtcdGrove
end Perennial
