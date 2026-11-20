/-
Lemmas of `watchEvents`'s proof that other proofs use (moved out of `watchEvents.lean`: import tiers).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOptions
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Watch
public import Proof.context.LibKeysChain
public import Perennial.Proof.context.Results
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **Every context's `Err()` returns client errors**, from the store's watcher (its client's
watcher's connection facts; as `WatchCons.clientWatchOk_ctxErr`). -/
theorem storeWatchOk_ctxErr [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (sp : Loc) (c : StoreCfg GF DObj) (W : WatchSpec GF DObj) (γk : KVNames) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) :
    storeWatchOk sp c W γk ∗ context.isContext ctx cs ⊢ ctxErrClient ctx cs := by
  iintro ⟨#Hsw, #Hctx⟩
  iunfold storeWatchOk at Hsw
  icases Hsw with ⟨%wp, %nf, %crv, %rse, -, -, -, -, -, -, -, -, -, -, -, -, #Hcw, -⟩
  iunfold clientWatchOk at Hcw
  icases Hcw with ⟨%w, %V, -, #Hw, -⟩
  iunfold client.isClientWatcher at Hw
  icases Hw with ⟨%cs', %vs, -, -, -, -, -, -, -, Hsf, -⟩
  iunfold client.watchSrvFacts at Hsf
  icases Hsf with ⟨-, Hcf⟩
  iunfold client.watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, -, -, #Hca, -, -⟩
  iunfold client.ctxErrClientAllW at Hca
  iapply Hca $$ Hctx

/-- `watchOptions`' owned `SendInitialEvents` cell, persisted (`store.Watch` reads it). -/
theorem sendInitOwn_persist (p : Loc) (sie : Option Bool) :
    sendInitOwn (GF := GF) p sie ⊢ |==> sendInitIs p sie := by
  cases sie with
  | none => iintro Hp; iunfold sendInitOwn at Hp; iunfold sendInitIs; imodintro; iexact Hp
  | some b =>
    iintro Hp
    iunfold sendInitOwn at Hp
    ipersist Hp
    iunfold sendInitIs
    imodintro
    iexact Hp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
