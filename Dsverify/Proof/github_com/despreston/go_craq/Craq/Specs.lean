/-
The cross-package specs of go-craq's packages (stage 1 interface): the constructors and boot
functions each package exports to another (`kv.New`, `netrpc.NewNodeClient`,
`NewCoordinatorClient`, the rpc bindings, `node.New`, `Start`, `coordinator.New`, `Start`), the
services the bindings call (`node_svc`, `coord_svc`), and the sealed slots they mention.

**Sealed slots** (each package's own; their bodies are the package's to write and change, with
the specs here fixed): `isNode cfg n a` (node `n` at address `a`: its fields, its lock's and its
invariant's), `nodeStartRes cfg n a` (what `Start` consumes: the unconnected coordinator
client), `isCoord cfg c` (the coordinator `c`). Their intended content is in the docstrings and
`notes/stage1-plan.md`.

**Shares.** `nodeRes cfg a` (node `a`'s ghost state at the start: its role's half, its empty
commit log), `coordRes cfg` (the coordinator's: the tail token, no version assigned, every chain
node's other role half), `rpcReady` (the node's rpc package with the kit's codec registered).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Slots
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Slots

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-! ## store/kv -/

/-- `kv.New()`: a store, empty. -/
abbrev kv.wp_New.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv }}
      (App (Val (@! store.kv.New)) (Val #()))
    {{ (p : Loc), RET #p; ∃ γs : GName,
        isStore (interface.mkOk (go.GoType.PointerType store.kv.KV.ty) #p) γs ∗
        storeOwn γs 1 ([] : StoreS) }}

/-! ## transport/netrpc -/

/-- `netrpc.NewNodeClient()`: a new node client. -/
abbrev netrpc.wp_NewNodeClient.spec : Prop :=
  ∀ (cfg : Cfg GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
        rpcReady ∗ craqCtx cfg }}
      (App (Val (@! transport.netrpc.NewNodeClient)) (Val #()))
    {{ (c : GoInterface), RET #c; freshNodeClient cfg c }}

/-- `netrpc.NewNodeClient` as a `NodeClientFactory`. -/
abbrev netrpc.factory.spec : Prop :=
  ∀ (cfg : Cfg GF),
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
      rpcReady ∗ craqCtx cfg ⊢
    isFactory cfg (functions transport.netrpc.NewNodeClient [])

/-- `netrpc.NewCoordinatorClient()`: a new coordinator client. -/
abbrev netrpc.wp_NewCoordinatorClient.spec : Prop :=
  ∀ (cfg : Cfg GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
        rpcReady ∗ craqCtx cfg }}
      (App (Val (@! transport.netrpc.NewCoordinatorClient)) (Val #()))
    {{ (c : GoInterface), RET #c; freshCoordClient cfg c }}

-- (The lab's `netrpc.nodeBinding_ok.spec`, `coordBinding_ok.spec`, that the bindings meet the
-- methods' specs through the lab's own dispatch, are the server's side: hypothesis H2,
-- notes/dsv-craq.md; stated with the kit.)

/-! ## node -/

/-- `node.New(opts)` for the node at `a` over an empty store, with the coordinator at
`cAddr`. -/
abbrev node.wp_New.spec : Prop :=
  ∀ (cfg : Cfg GF) (a : GoString) (st : GoInterface) (γs : GName)
    (f : GoFunc) (cc : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
        ⌜a ∈ cfg.chain⌝ ∗ nodeRes cfg a ∗ isStore st γs ∗ storeOwn γs 1 ([] : StoreS) ∗
        isFactory cfg f ∗ freshCoordClient cfg cc }}
      (App (Val (@! node.New))
        (Val #(node.Opts.mk st a a cfg.cAddr f cc null)))
    {{ (n : Loc), RET #n; isNode cfg n a ∗ nodeStartRes cfg n a }}

/-- `n.Start()`: announces the node to the coordinator, once. -/
abbrev node.wp_Start.spec : Prop :=
  ∀ (cfg : Cfg GF) (n : Loc) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ isNode cfg n a ∗
        nodeStartRes cfg n a ∗ joinTicket cfg.γ a }}
      (App (Val (n @!! go.GoType.PointerType node.Node.ty @!! go!"Start")) (Val #()))
    {{ (err : GoInterface), RET #err; True }}

/-- The node is its service. -/
abbrev node.node_svc.spec : Prop :=
  ∀ (cfg : Cfg GF) (n : Loc) (a : GoString),
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ isNode cfg n a ⊢
    isNodeSvc cfg (ptrIface node.Node.ty n) a

/-! ## coordinator -/

/-- `coordinator.New(tport)`. -/
abbrev coordinator.wp_New.spec : Prop :=
  ∀ (cfg : Cfg GF) (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        ⌜cfg.chain.length < 2 ^ 31 - 1⌝ ∗ craqCtx cfg ∗ isFactory cfg f ∗ coordRes cfg }}
      (App (Val (@! coordinator.New)) (Val #f))
    {{ (c : Loc), RET #c; isCoord cfg c }}

/-- `c.Start()`: pings the replicas forever (removing those whose ping fails). -/
abbrev coordinator.wp_Start.spec : Prop :=
  ∀ (cfg : Cfg GF) (c : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"Start"))
        (Val #()))
    {{ RET #(); True }}

/-- The coordinator is its service. -/
abbrev coordinator.coord_svc.spec : Prop :=
  ∀ (cfg : Cfg GF) (c : Loc),
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
      isCoord cfg c ⊢
    isCoordSvc cfg (ptrIface coordinator.Coordinator.ty c)

end specs

end github_com.despreston.go_craq

end Perennial
