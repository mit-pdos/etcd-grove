/-
`Orch(clientAddrs)`: the orchestrator's program: `remote.Check` of the client nodes at the two
addresses (`Ops` operations each, inputs from `Gen`), against the counter's model with pending
increments (`Model()`, `isModel cS`), with `Codec()` and `attempt()`. Given the addresses'
protocols for the store `cR γs`, the slot map, node 0's invariant (`pendCtx`) with lintest's state at
the model's start (`pendLib`), the time receipts' bound, and each client node's call budget (`Ops`
operations of `readTries` attempts: 60 units), it returns: it never panics, so porcupine
accepts the history. Proved in `Net/Proof/.../lib/remote/counter/Orch.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.ModelDefs

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
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- See the file header. -/
abbrev Orch.spec : Prop :=
  ∀ (γs : GName) (γp : PendNames) (addrs : GoSlice) (addrL : List GoString),
  addrL.length = 2 → receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter ∗
      addrs ↦*□ addrL ∗
      ([∗list] a ∈ addrL, remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := Bool) ∗
      pendCtx (Gg := hG.goose_globalGS) (cR (GF := GF) γs) (cS (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (cS (GF := GF)) γp (cS (GF := GF)).M.init ∗
      [∗list] a ∈ addrL, budUnits (Gg := hG.goose_globalGS) a 60 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Orch)) (Val #addrs))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
