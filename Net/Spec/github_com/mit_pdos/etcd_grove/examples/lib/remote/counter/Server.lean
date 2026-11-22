/-
`Server(addr)`: the counter server's program: lintest/counter's `Counter` (`New`), served at `addr`
(`remote.Serve`) with the operation `Out{N: sys.(*Counter).Apply(in).(int64)}`. Given the address's
protocols for the store `cR γs` and the start's half of `γs` at the counter's initial value, it
never returns (and never panics). Proved in `Net/Proof/.../lib/remote/counter/Server.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- See the file header. -/
abbrev Server.spec : Prop :=
  ∀ (γs : GName) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter ∗
      remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) a ∗ ghostVar γs (1 : Qp).half (W64 0) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Server)) (Val #a))
  {{ RET #(); False }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
