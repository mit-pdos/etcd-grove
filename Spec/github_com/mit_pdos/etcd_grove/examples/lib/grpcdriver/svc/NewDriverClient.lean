/- Lean-first (no Rocq counterpart).

`svc.NewDriverClient(cc)` (svc.go, generated): a fresh `*driverClient` whose `cc` field is `cc`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.PlainInvoke

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]

/-- See the file header. -/
abbrev NewDriverClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc }}
    (App (Val (@! svc.NewDriverClient)) (Val #cc))
  {{ (c : GoInterface), RET #c; ∃ dc : Loc,
      ⌜c = interface.mkOk (go.GoType.PointerType svc.driverClient.ty) #dc⌝ ∗
      structFieldRef svc.driverClient go!"cc" dc ↦ cc }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
