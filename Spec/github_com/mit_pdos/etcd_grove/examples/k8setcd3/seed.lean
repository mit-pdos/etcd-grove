/- Lean-first (no Rocq counterpart).

`seed(cli)` (k8setcd3.go): `seedOne` of `a` then `b` from the store at revision `1`, on a new
member's start state (`σb`, `Main`'s half of the seeding's state): the seeded state (`σs2`) and
the driver's seeded store (`g0s`), or `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Seed

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
abbrev seed.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (x : client.SrvAt GF) (V : client.WEnv GF) (γs : GName),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl [x.addr] V ∗ client.clientWriteOnce cl [x.addr] ∗ client.kvRegsAt x ∗
      seedInv γs x.γr.kv ∗ ghostVar γs (1 : Qp).half σb }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.seed)) (Val #cl))
  {{ (s' : mstore) (ok : Bool), RET (PairV #s' #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ghostVar γs (1 : Qp).half σs2 ∗ storeOwn s' g0s) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
