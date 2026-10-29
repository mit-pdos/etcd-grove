/- Lean-first (no Rocq counterpart).

`validConf(cs, cc)` (kv.go): whether `confchange` accepts the change `cc` on the configuration
restored from `cs` (a `nil` `cs` is the empty configuration), with fewer than `2^62` ids after it:
`ConfOk` (`Rule.lean`) of the change at the membership `m` that `cs` denotes, for `m` well formed (a
valid membership or the empty one: what `Restore` accepts). `cs` and `cc` are given back.

Its proof rests on raft's importable `confchange`/`tracker` specs (the frozen design's §4b,
`tracker.MakeProgressTracker.apiSpec`, `confchange.Restore.apiSpec`,
`Changer.{Simple,EnterJoint,LeaveJoint}.apiSpec` over `ownTrackerM`, the size law of `ownCfgPairM`),
stage U8 of `notes/raft-unified-plan.md` (track B): not proved yet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Rule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev validConf.spec : Prop :=
  ∀ (csp : Loc) (dq : DFrac) (c : ConfStateM) (m : Membership) (ccp : Loc) (dq' : DFrac)
    (cc : ConfChangeV2M),
  confStateIs c m → m.WellFormed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ csOpt csp dq c ∗ ownConfChangeV2 ccp dq' cc }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.validConf)) (Val #csp)) (Val #ccp))
  {{ (b : Bool), RET #b; csOpt csp dq c ∗ ownConfChangeV2 ccp dq' cc ∗
      ⌜b = true ↔ ConfOk (.v2 cc) m⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
