/- Lean-first (no Rocq counterpart).

`(*Svc).Echo(a, r)` on the service `isSvc γid s`, with the token of the request's id (`idTok γid
id`, which the service keeps: a second run of `id` would need a second token): it writes the
request's id and payload slice into `*r`, with `Runs = 1` (no earlier run of `id`), and returns
`nil` if the request's `Fail` is empty, else an `errors.New(Fail)` error (`errMsg e fail`). It
reads only `a`'s fields, not the payload's bytes. Proved in
`Net/Proof/.../rpcdriver/service/Svc__Echo.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Defs
public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : service.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- See the file header. -/
abbrev Svc.Echo.spec : Prop :=
  ∀ (γid : GName) (s a r : Loc) (id : w64) (dsl : GoSlice) (fail : GoString) (v : service.Reply),
  {{ isSvc (GF := GF) γid s ∗ a ↦ service.Args.mk id dsl fail ∗ (r ↦ v : IProp GF) ∗ idTok γid id }}
    (App (App (Val (s @!! go.GoType.PointerType service.Svc.ty @!! go!"Echo")) (Val #a))
      (Val #r))
  {{ (e : GoInterface), RET #e; a ↦ service.Args.mk id dsl fail ∗
      r ↦ service.Reply.mk id dsl (W64 1) ∗
      ((⌜fail = [] ∧ e = interface.nil⌝) ∨ (⌜fail ≠ []⌝ ∗ net.rpc.errMsg e fail)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
end Perennial
