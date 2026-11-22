/-
`Client(c, addr, serverAddr)`: client node `c`'s program: `remote.ServeClient` at `addr`, its
operation a `remote.Do` of the same input at the server (`serverAddr`). Given both addresses'
protocols for the store `cR γs`, the slot map, and a read's update with no result (node 0's
`readNoop`), it never returns (and never panics). Proved in
`Net/Proof/.../lib/remote/counter/Client.lean`.
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
abbrev Client.spec : Prop :=
  ∀ (γs : GName) (c : w64) (a sa : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter ∗
      remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) a ∗
      remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) sa ∗
      mapCtx (Gg := hG.goose_globalGS) (I := Bool) ∗
      □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
        lin (Gg := hG.goose_globalGS) (cR (GF := GF) γs) i (fun _ => iprop(True))) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Client))
      (Val #c)) (Val #a)) (Val #sa))
  {{ RET #(); False }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
