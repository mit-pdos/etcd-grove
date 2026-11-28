/- Lean-first (no Rocq counterpart).

`watchEvents(s, in)` (watch.go): runs the watch `in` through the store `s` (`store.Watch` under the
driver's own `WithCancel(Background())`, whose Done proposition is the driver's, `donePD`), reads it
with `consume`, stops it and cancels the context. Either the `Watch` call failed (only for a
non-initial-events watch from revision 0: `sieOfL x = some false`, `n = 0`), or it returns the events
it received as the driver records them (`toWEvL` of the received events `rs`, k8s 7g: `consume`'s
post; each `kWEvRel` of the store event in `kes`), which are
`kSeen` (the cancellation branch refuted: the driver read them while it held the watch live and its
context not done): all Error events, or a prefix of the ideal stream of the watch's scope and mode
from a start point tied to a state the read update `Q` fired at, read at another.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchEvents.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (sp : Loc) (c : StoreCfg GF DObj) (γk : KVNames) (x : Input) (k : GoString) (n : w64)
    (Q : Nat → KVState → IProp GF),
  c.S = driverSpec →
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
    kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ m ∈ c.ms, noRefusalAt m.addr) → threadBound GF ≤ 2 ^ 30 - 1 →
  prepareKeyM c.resourcePrefix x.WKey' x.Recursive' = some k →
  (c.pathPrefix ++ k).length ≤ opKeyMax → c.S.parseRV x.MinRV' = some n → uint.Z n < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (k8s.isStore sp c ∗
      storeWatchOk sp c driverW γk ∗ watchListOn ∗ rangeStreamOff ∗
      (|==> readAus c γk (Q 0)) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev))) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEvents))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty)
        #sp))) (Val #x))
  {{ (sl rsl : GoSlice) (failed : Bool), RET (PairV (PairV #sl #rsl) #failed); levelTok 0 ∗ (if failed then iprop(⌜sieOfL x = some false ∧ uint.nat n = 0⌝)
      else iprop(∃ (rs : List k8s_correctness.REv) (kes : List (KWEv DObj)),
        wevsOwnM sl (rs.map k8s_correctness.toWEvL) ∗ k8s_correctness.evsRO rsl rs ∗
        ⌜List.Forall₂ kWEvRel kes (rs.map k8s_correctness.toWEvL)⌝ ∗
        kSeen c (selD x) (predEmptyL x) (kScopeOf c k x.Recursive')
          (kModeOf (sieOfL x) x.Bookmarks' n) Q kes)) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
