/- Lean-first (no Rocq counterpart).

`runWatch(s, in)` (watch.go): one watch operation of a watcher client. A `Skip` watch, or one whose
`Watch` call failed (`watchEvents`: a non-initial-events watch from revision 0), answers
`Output{WFailed: true}` and no object; any other answers `Output{WEvents: encodeWEvents(evs)}` for
the events `wes` it received (`watchEvents`' post: each `kWEvRel` of a store event in `kes`, which
are `kSeen`), with `lastObj(evs)` (`lastObjL wes`), and (k8s 7g) the events as received in its `Raw`
(`wEventsRawOut`: read-only, of views `rs` whose records are `wes`, `consume`'s post). The hiccup sleep (`time.Sleep`) is not modelled.
The watch's facts (`watchEvents.spec`'s premises) are needed only for a watch that is not skipped.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `Output{WFailed: true}`. -/
def wFailedOut : Output := { (zero_val Output) with WFailed' := true }

/-- `Output{WEvents: s}`. -/
def wEventsOut (s : GoString) : Output := { (zero_val Output) with WEvents' := s }

/-- `Output{WEvents: s, Raw: Raw{Events: rsl}}` (k8s 7g). Its plain value is `wEventsOut s`. -/
def wEventsRawOut (s : GoString) (rsl : GoSlice) : Output :=
  { wEventsOut s with
    Raw' := { (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Raw) with Events' := rsl } }

theorem plainOut_wEventsRawOut (s : GoString) (rsl : GoSlice) :
    plainOut (wEventsRawOut s rsl) = wEventsOut s := rfl

/-- See the file header. -/
abbrev runWatch.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (sp : Loc) (c : StoreCfg GF DObj) (γk : KVNames) (x : Input) (k : GoString) (n : w64)
    (Q : Nat → KVState → IProp GF),
  c.S = driverSpec →
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
    kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ m ∈ c.ms, noRefusalAt m.addr) → threadBound GF ≤ 2 ^ 30 - 1 →
  (x.Skip' = false → prepareKeyM c.resourcePrefix x.WKey' x.Recursive' = some k ∧
    (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV x.MinRV' = some n ∧ uint.Z n < 2 ^ 63 - 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (k8s.isStore sp c ∗
      storeWatchOk sp c driverW γk ∗ watchListOn ∗ rangeStreamOff ∗
      (|==> readAus c γk (Q 0)) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev))) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.runWatch))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty)
        #sp))) (Val #x))
  {{ (y : Output) (o : Obj) (ok : Bool), RET (PairV (PairV #y #o) #ok); levelTok 0 ∗ ((⌜y = wFailedOut ∧ ok = false ∧ (x.Skip' = true ∨ (sieOfL x = some false ∧ uint.nat n = 0))⌝) ∨
      (∃ (wes : List WEv) (kes : List (KWEv DObj)) (rs : List k8s_correctness.REv) (rsl : GoSlice),
        ⌜x.Skip' = false ∧ y = wEventsRawOut (encWEventsL wes) rsl ∧
          wes = rs.map k8s_correctness.toWEvL ∧
          lastObjL wes = (if ok then some o else none) ∧ List.Forall₂ kWEvRel kes wes ∧
          ∀ w ∈ wes, (encodeWith tagV1 w.o).length < 2 ^ 63⌝ ∗
        k8s_correctness.evsRO rsl rs ∗ kSeen c (selD x) (predEmptyL x) (kScopeOf c k x.Recursive')
          (kModeOf (sieOfL x) x.Bookmarks' n) Q kes)) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
