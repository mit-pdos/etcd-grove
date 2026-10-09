/-
`tracker.Config.Clone` copies a config so that it shares no memory with the original.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
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

/-- `Clone` of a voters-only non-joint config: a fresh incoming voter map with the same
ids; `nil` maps clone to `nil`; `AutoLeave` is **not** copied (the `Config{...}` literal
leaves it at `false`), which is why the result is again `ConfigSimple`. The receiver is a
value method; it is called through the field's address (`(c Config) Clone()` on
`c.Tracker.Config`), so the triple is stated on the pointer method. -/
abbrev tracker.Config.Clone.spec : Prop :=
  ∀ (p : Loc) (cfg : tracker.Config) (v : Loc) (vm : GMap w64 Unit) (dq dqv : DFrac),
  ConfigVotersOnly cfg v →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      p ↦{dq} cfg ∗ v ↦${dqv} vm }}
    (App (Val (p @!! go.GoType.PointerType tracker.Config.ty @!! go!"Clone")) (Val #()))
  {{ (cfg' : tracker.Config) (v' : Loc), RET #cfg';
      p ↦{dq} cfg ∗ v ↦${dqv} vm ∗ ⌜ConfigSimple cfg' v'⌝ ∗ v' ↦$ vm }}

end spec

end EtcdGrove
end Perennial
