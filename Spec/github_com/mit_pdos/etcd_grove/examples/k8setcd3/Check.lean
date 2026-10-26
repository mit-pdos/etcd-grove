/- Lean-first (no Rocq counterpart).

`Check(s, st0, clients, ops, timeout)` (k8setcd3.go): `lintest.Run` of `clients` clients of
`ops` operations each through the store `s` (`Apply`), checked against `Model(st0)` (the driver's
model from the seeded store `g0`): never `Illegal`, and `Ok` without a timeout. Premises: `Apply`'s
(the store, the instance's invariant at each member, the library's state at the model's start),
`Run`'s bounds, and the seeded store's size.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Calls
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (γ : KNames) (sp : Loc) (c : k8s.StoreCfg GF DObj) (g0 : GSt) (s0 : mstore)
    (clients ops dur : w64),
  c.S = driverSpec → c.pathPrefix = go!"/registry" → c.resourcePrefix = go!"/objs" →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  c.ms ≠ [] →
  receiptBound GF ≤ 2 ^ 63 →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 → g0.items.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      context.isClosedchanInit ∗ k8s.isStore sp c ∗
      ([∗list] sv ∈ c.ms, kInv γ c g0 sv.γr.kv) ∗ kState γ g0 (linkv.pInit (kSpec g0)) ∗
      storeOwn s0 g0 }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.Check))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty)
        #sp))) (Val #s0)) (Val #clients)) (Val #ops)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
