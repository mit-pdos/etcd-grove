/-
## `header(lvl, msg)` (`logger.go`)

`DefaultLogger`'s formatting (`fmt.Sprintf`). **Changes.** New (round 1).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A log line's text. -/
def header.spec : Prop :=
  ∀ (lvl msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (Val (@! go_etcd_io.raft.v3.header)) (Val #lvl)) (Val #msg))
  {{ (s : GoString), RET #s; True }}

end spec
end Raft
end EtcdGrove
end Perennial
