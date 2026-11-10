/- Lean-first (no Rocq counterpart).

`call(s, in)` (k8s_etcd3.go): one operation through the store `s` (`isStore sp c`, the driver's
objects: `c.S = driverSpec`), with what its kind needs (`callPre`: a `Create`'s updates, a
`Delete`'s or update's token and updates, a `Get`'s maker of read updates). Its output is
`EOther`'s (an error of unknown outcome), or the store's model's at a state `σ` the caller's
update or read fired at (`callAt`), `kStep`'s output there.

Premises: the input's key is one the store takes (`prepareKeyM`), its etcd key the model's
(`mkeyL`), its name and UID fit an object and its minimum resource version parses (`InOk`); its
cached object, if any, one the store's keys held (`cachedIn`), with no resource version
precondition on an update (`CachedNoRV`, the scope premise D1 of stage 7b,
`issues/k8s-etcd3-cached-noop-skips-preconditions.md`); a `Get`'s reads see the store's states;
`errors.As`'s target (the client's context lemma). Stage 7e-4: a list (`listPre`: `GetList`'s
updates, the first page's result at the answer's state: for the revision `R` its maker was given,
`σ`'s unless the answer is `ETooLarge`, 7e-1's R1), `ETooLarge`, the client's errors no
`APIStatus` (`clientErrPlain`, pending 7c-3), the thread token lent by `lintest` and the thread
bound `GetList` needs; for a list, the store's resource prefix, decoder and versioner the driver's
(`driver_listContractOk`) and the feature gate's `EtcdRangeStream` off (`rangeStreamOff`, from
`noStreaming`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)
open go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev call.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (sp : Loc) (c : StoreCfg GF DObj) (eD eU : GoInterface) (x : Input) (W : IProp GF)
    [Timeless W] (Φ : KVState → IProp GF) (Q : w64 → w64 → KVState → IProp GF)
    (QL : w64 → KVState → IProp GF) (PL : KVState → KVState → IProp GF),
  c.S = driverSpec → c.resourcePrefix = go!"/objs" → c.di = decoderI → c.vi = versionerI →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  clientErrPlain (sem := sem) → threadBound GF ≤ 2 ^ 30 - 1 →
  prepareKeyM c.resourcePrefix (storeKeyL x.Key') false = some (storeKeyL x.Key') →
  c.pathPrefix ++ storeKeyL x.Key' = mkeyL x.Key' →
  InOk x → x.Val'.length ≤ 2 ^ 20 → CachedNoRV x →
  (∀ R m σ, Q R m σ ⊢ ⌜kvWf c σ⌝) →
  (∀ R σ, QL R σ ⊢ ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ R σ σ', QL R σ ∗ PL σ σ' ⊢ ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ k8s.isStore sp c ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ eU ∗
      cachedIn c x ∗ rangeStreamOff ∗ threadTok ∗
      (if x.Kind' = W64 4 then listPre c QL PL else callPre c eD eU x W Φ Q) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.call))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty)
        #sp))) (Val #x))
  {{ (y : Output), RET #y; threadTok ∗ (⌜y = otherL⌝ ∨
      ∃ σ : KVState, (if x.Kind' = W64 4 then
          iprop(∃ R : w64, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 (σ.rev : Int)⌝)
        else callAt x Φ Q σ) ∗
        ⌜y = callOut c eD eU x σ⌝) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
