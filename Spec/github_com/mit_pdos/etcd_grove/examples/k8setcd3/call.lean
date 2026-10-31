/- Lean-first (no Rocq counterpart).

`call(s, in)` (k8setcd3.go): one operation through the store `s` (`isStore sp c`, the driver's
objects: `c.S = driverSpec`), with what its kind needs (`callPre`: a `Create`'s updates, a
`Delete`'s or update's token and updates, a `Get`'s maker of read updates). Its output is
`EOther`'s (an error of unknown outcome), or the store's model's at a state `σ` the caller's
update or read fired at (`callAt`), `kStep`'s output there.

Premises: the input's key is one the store takes (`prepareKeyM`), its etcd key the model's
(`mkeyL`), its name fits an object (`InOk`); a `Get`'s reads see the store's states; `errors.As`'s
target (the client's context lemma).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)
open go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev call.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (sp : Loc) (c : StoreCfg GF DObj) (eD eU : GoInterface) (x : Input) (W : IProp GF)
    [Timeless W] (Φ : KVState → IProp GF) (Q : w64 → w64 → KVState → IProp GF),
  c.S = driverSpec →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  prepareKeyM c.resourcePrefix (storeKeyL x.Key') false = some (storeKeyL x.Key') →
  c.pathPrefix ++ storeKeyL x.Key' = mkeyL x.Key' →
  InOk x → x.Val'.length ≤ 2 ^ 20 →
  (∀ R m σ, Q R m σ ⊢ ⌜kvWf c σ⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ k8s.isStore sp c ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ∗
      callPre c eD eU x W Φ Q }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.call))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty)
        #sp))) (Val #x))
  {{ (y : Output), RET #y; ⌜y = errOutL⌝ ∨
      ∃ σ : KVState, callAt x Φ Q σ ∗ ⌜y = (kStep eD eU x (c.abs σ)).2⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
