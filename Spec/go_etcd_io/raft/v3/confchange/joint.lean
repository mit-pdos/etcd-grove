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

/-- `joint(cfg)`: whether the outgoing voter map (`nil` or a map) is non-empty.
(Generalized 2026-10-12 from the `nil` case.) -/
abbrev confchange.joint.spec : Prop :=
  ∀ (cfg : tracker.Config) (vin vout : Loc) (s : GSet w64) (dq : DFrac),
  cfg.Voters'.arr = [vin, vout] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ownIdsetQ vout dq s }}
    (App (Val #(functions confchange.joint [])) (Val #cfg))
  {{ RET #(decide (0 < GMap.size s)); ownIdsetQ vout dq s }}

end spec

end EtcdGrove
end Perennial
