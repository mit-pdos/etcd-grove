module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section updspecs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- `n.sendCommitToPrev(prev, k, v)` (persistent precondition: it runs in a goroutine). -/
abbrev sendCommitToPrev.spec : Prop :=
  ∀ (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName) (nbM latM : Loc)
    (prev : node.neighbor) (k : GoString) (v : w64),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
      nodeFields cfg n a st γs nbM latM ∗ nbrOk cfg prev ∗ cvLb cfg.γ k v) -∗
    (∀ err : GoInterface, Φ #err) -∗
    WP (App (App (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"sendCommitToPrev" #n))
      (Val #prev)) (Val #k)) (Val #v)) {{ Φ }}

/-- `n.requestFwdPropagation(c)` under the lock: the store's newest committed versions do not
change. -/
abbrev requestFwdPropagation.spec : Prop :=
  ∀ (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName) (nbM latM : Loc)
    (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS)
    (c : GoInterface) (ca : GoString),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
      nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S ∗
      isNodeClient cfg c ca) -∗
    (∀ err : GoInterface, (∃ S' : StoreS, lockedState cfg γs n nbM latM h t nbrs lat S') -∗
      (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
    WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"requestFwdPropagation" #n))
      (Val #c)) {{ Φ }}

/-- `n.requestBackPropagation(c)` under the lock, with a cover `L` of `c`'s node: on success
the store's newest committed versions cover `cvOf L`; they only grow. -/
abbrev requestBackPropagation.spec : Prop :=
  ∀ (cfg : Cfg GF) (n : Loc) (a : GoString) (st : GoInterface) (γs : GName) (nbM latM : Loc)
    (h t : Bool) (nbrs : GMap w64 node.neighbor) (lat : GMap GoString w64) (S : StoreS)
    (c : GoInterface) (ca : GoString) (L : CLog),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ craqCtx cfg ∗
      nodeFields cfg n a st γs nbM latM ∗ lockedState cfg γs n nbM latM h t nbrs lat S ∗
      isNodeClient cfg c ca ∗ covers cfg.γ ca L) -∗
    (∀ err : GoInterface, (∃ (lat' : GMap GoString w64) (S' : StoreS),
        lockedState cfg γs n nbM latM h t nbrs lat' S' ∗
        ⌜∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (S'.maxCommitted k)⌝ ∗
        ⌜err = interface.nil → ∀ k, uint.Z (cvOf L k) ≤ uint.Z (S'.maxCommitted k)⌝) -∗
      (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
    WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"requestBackPropagation" #n))
      (Val #c)) {{ Φ }}

end updspecs

end NodeP

end github_com.despreston.go_craq

end Perennial
