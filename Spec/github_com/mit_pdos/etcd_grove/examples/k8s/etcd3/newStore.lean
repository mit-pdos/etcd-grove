/- Lean-first (no Rocq counterpart).

`newStore(kc)` (k8setcd3.go; stage E of 7f-6, plan §3 step 8: the three entry points' seed, features
and `etcd3.New`): the seed keys through the kubernetes client `kc` (`seed`: the seed's ghost cell
from `σb` to `σs2`, the model's store after the seeds and its history), the features (no streaming
lists: `rangeStreamOff`; `WatchList` on: `watchListOn`), and the store `etcd3.New` makes over `kc`
with the driver's codec, versioner, transformer and decoder (`isStore` at `storeCfgD`), with its
watch fields once the client's watcher over a KV is given (`storeWatchOk`, at the driver's watch
contract `driverW`: `watchContractOk_driver`, `newItemOk_driver`); or `false` if the seed or a
feature check failed (`New` does not fail).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seed
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WContract

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev newStore.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (kc cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γs γh : GName),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → ms ≠ [] →
  threadBound GF ≤ 2 ^ 30 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ levelTok 0 ∗ (kc ↦□ (go_etcd_io.etcd.client.v3.kubernetes.Client.mk cl
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
          #kc)) ∗
      isNewClient cl (ms.map (·.addr)) V ∗ client.clientWriteOnce cl (ms.map (·.addr)) ∗
      ([∗list] y ∈ ms, client.kvRegsAt y) ∗ ([∗list] y ∈ ms, seedInv γs y.γr.kv) ∗
      ghostVar γs (1 : Qp).half σb) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newStore)) (Val #kc))
  {{ (s : GoInterface) (s0 : mstore) (hsl : GoSlice) (ok : Bool),
      RET (PairV (PairV (PairV #s #s0) #hsl) #ok); levelTok 0 ∗ (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ghostVar γs (1 : Qp).half σs2 ∗ storeOwn s0 g0s.st ∗
        (∃ hs : List mstore, hsl ↦*□ hs ∗ [∗list] x;g ∈ hs;g0s.hist, storeOwn x g) ∗
        rangeStreamOff ∗ watchListOn ∗
        ∃ sp mt lt : Loc,
          ⌜s = interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty) #sp⌝ ∗
          k8s.isStore sp (storeCfgD kc cl ms V mt lt γh) ∗
          □ ∀ γk : KVNames, clientWatchOk cl γk -∗
            storeWatchOk sp (storeCfgD kc cl ms V mt lt γh) driverW γk)) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
