/- Lean-first (no Rocq counterpart).

`isFailMsg(m)`: whether `m` is marked as one of the method's messages (`strings.HasPrefix(m,
"driver: ")`, `driverMark`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev isFailMsg.spec : Prop :=
  ∀ (m : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (Val (@! isFailMsg)) (Val #m))
  {{ RET #(decide (driverMark <+: m)); True }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
