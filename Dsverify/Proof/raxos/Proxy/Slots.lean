/-
Package `proxy`'s sealed slots (interface of stage 2, `notes/stage2-plan.md`): their names and
types are the interface; their bodies are the package's to choose (the store's as in stage 1; the proxy's placeholders
until package `proxy` defines them in Prove); clients use them only through the specs of `Replica.lean`.
-/
module

public import Dsverify.Proof.raxos.ReplicaDefs
public import Dsverify.Proof.raxos.Proxy.StoreDefs
public import Dsverify.Proof.raxos.Proxy.ProxyState

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-! ## The batch store (package `proxy`'s slot) -/

/-- `cb` is a replica's batch store: every batch in it is registered (persistent). Sealed:
package `proxy` defines it; clients use `ClientBatchStore.Add.spec` and `.Get.spec`. -/
def isStore (γ : QNames) (γs : GName) (cb : Loc) : IProp GF := isStoreDef γ γs cb

/-- The store `cb` has the id `x` (persistent; package `proxy`'s slot). -/
def storeHas (γs : GName) (x : GoString) : IProp GF := storeHasDef γs x

/-! ## The proxy (package `proxy`'s slots) -/

/-- The proxy's main loop's state (exclusive), replica `k` of the configuration `c`. -/
def proxyOwn (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) : IProp GF := proxyOwnDef γ c k pr

/-- What the proxy's goroutines share (persistent). -/
def proxyShared (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) : IProp GF := proxySharedDef γ c k pr

instance isStore_persistent (γ : QNames) (γs : GName) (cb : Loc) :
    Persistent (isStore (GF := GF) γ γs cb) := by
  unfold isStore; infer_instance
instance storeHas_persistent (γs : GName) (x : GoString) :
    Persistent (storeHas (GF := GF) γs x) := by
  unfold storeHas storeHasDef; infer_instance
instance proxyShared_persistent (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) :
    Persistent (proxyShared (GF := GF) γ c k pr) := by
  unfold proxyShared; infer_instance

end defs

end Perennial.raxos
