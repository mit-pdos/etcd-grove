/- Lean-first (no Rocq counterpart).

`Apply(s, tbl, input)` (k8s_etcd3.go): one operation through the store `s`, logically atomic against
the driver's model (`k8setcd3S g0`: `pM (kSpec g0) decOp`, from the seeded store `g0`), in the
form `lintest`'s `applySpec` takes for the closure `Check` passes,
`func(input any) any { return Apply(s, tbl, input) }`:

  `{{ kInOk i ∗ threadTok }} <<{ ∀∀ S, kState γ g0 S }>> Apply(s, i) @@ drvE
     <<{ ∃∃ S' o, kState γ g0 S' ∗ ⌜(k8setcd3S g0).M.step S (i, o) = some S'⌝ }>>
     {{ o', RET #o'; ⌜∀ s, step s (i, o') = step s (i, o)⌝ ∗ ioOk i o' ∗ threadTok }}`

It returns an answer `o'` the model cannot tell from the committed `o` (`plainOut o' = plainOut o`:
the answer's `Raw` holds the store's error, allocated after the linearization point; 2026-11-19,
option A of `notes/k8s-7g-handoff.md`).

over the library's state `kState γ g0 S` (the history's ghost variable, whose other half is in the
instance's invariant `kInv γ c g0 γr.kv` at each member: `Proof/.../k8setcd3/Inv.lean`). The input
is one `Gen` may return (`kInOk c g0.st.rv`: its cached object one of the store's, its resource version
floored at the seeded revision); an answer with a name
becomes the client's cached object in the table `tbl` (`isCache c tbl`, stage 7b).

Premises: the store `s` (`isStore sp c`) holds the driver's objects (`c.S = driverSpec`) under
the driver's prefixes (`"/registry"`, `"/objs"`), decoder and versioner, the packages' facts, and
`errors.As`'s target (the client's context lemma). Stage 7e-4: the thread bound and the goroutine's `threadTok` (lent by
`lintest`) `GetList` needs, and the feature gate's `EtcdRangeStream` off (`rangeStreamOff`).
Stage E of 7f-6: a watcher's input (kind 5) runs `runWatch`, whose events the model checks
(`kSpec`'s observation) against the configuration at the commit; it needs the instance's invariant
at the cluster's KV names `γk` (whose read updates the watch fires), the store's watcher at them
(`storeWatchOk`, the driver's watch spec `driverW`) and the `WatchList` gate on (`watchListOn`).
k8s 7g step 5: the seeded revision within the seeded history (`kInv_lb_seed`: a watch starts past the
seeds, for the `ioOk` of its received events, `wrawOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s github_com.anishathalye.porcupine
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
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (γ : KNames) (sp tbl : Loc) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames),
  c.S = driverSpec → c.pathPrefix = go!"/registry" → c.resourcePrefix = go!"/objs" →
  c.di = decoderI → c.vi = versionerI →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  threadBound GF ≤ 2 ^ 30 - 1 → (∀ x ∈ c.ms, noRefusalAt x.addr) →
  uint.nat g0.st.rv ≤ g0.hist.length →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 -∗
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 -∗
    k8s.isStore sp c -∗ ([∗list] sv ∈ c.ms, kInv γ c g0 sv.γr.kv) -∗ ⌜c.ms ≠ []⌝ -∗
    isCache c tbl -∗ rangeStreamOff -∗
    kInv γ c g0 γk -∗ storeWatchOk sp c driverW γk -∗ watchListOn -∗
    iprop(∀ i : GoInterface,
      {{ kInOk c g0.st.rv i ∗ threadTok }} <<{ ∀∀ S, kState γ g0 S }>>
        (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Apply))
          (Val #(interface.mkOk (go.GoType.PointerType
            k8s_io.apiserver.pkg.storage.etcd3.store.ty) #sp))) (Val #tbl)) (Val #i)) @@ drvE
      <<{ ∃∃ S' o, kState γ g0 S' ∗ ⌜(k8setcd3S (GF := GF) g0).M.step S (i, o) = some S'⌝ }>>
      {{ (o' : GoInterface), RET #o';
        ⌜∀ s, (k8setcd3S (GF := GF) g0).M.step s (i, o') = (k8setcd3S (GF := GF) g0).M.step s (i, o)⌝ ∗
        (k8setcd3S (GF := GF) g0).ioOk i o' ∗ threadTok }})

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
