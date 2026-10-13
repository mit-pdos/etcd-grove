/-
`Config.Clone` copies a configuration's maps. Lean-first (no Rocq counterpart); see
`InvConfchange.lean`.
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

/-- `Clone()` on a configuration representing `c`: a configuration with fresh maps holding
the same sets (a `nil` map cloned as `nil`, so the canonical representations stay
canonical) and **`AutoLeave` false**: `Clone` does not copy it (`raft-config-clone-autoleave`
in `issues/`). (Generalized 2026-10-12 from the voters-only config.) -/
abbrev tracker.Config.Clone.spec : Prop :=
  ∀ (p : Loc) (cfg : tracker.Config) (c : CfgM) (dq dqc : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      p ↦{dq} cfg ∗ ownCfgCC cfg dqc c }}
    (App (Val (p @!! go.GoType.PointerType tracker.Config.ty @!! go!"Clone")) (Val #()))
  {{ (cfg' : tracker.Config), RET #cfg';
      p ↦{dq} cfg ∗ ownCfgCC cfg dqc c ∗ ownCfgCC cfg' (DFrac.own 1) { c with autoLeave := false } }}

end spec

end EtcdGrove
end Perennial
