/- Lean-first (no Rocq counterpart).

`seed(cli)` (k8s_etcd3.go): `seedOne` of `ns-1/pod-1` at revision 2 then `ns-2/pod-2` at 3 from
the empty store at revision `1`, on a new member's start state (`σb`, `Main`'s half of the
seeding's state): the seeded state (`σs2`), the driver's seeded store and its history (`g0s`: the
stores at revisions 1 to 3, as `Model` takes them), or `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev seed.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γs : GName),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → ms ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl (ms.map (·.addr)) V ∗ client.clientWriteOnce cl (ms.map (·.addr)) ∗
      ([∗list] y ∈ ms, client.kvRegsAt y) ∗ ([∗list] y ∈ ms, seedInv γs y.γr.kv) ∗ ghostVar γs (1 : Qp).half σb }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed)) (Val #cl))
  {{ (s' : mstore) (hsl : GoSlice) (ok : Bool), RET (PairV (PairV #s' #hsl) #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ghostVar γs (1 : Qp).half σs2 ∗ storeOwn s' g0s.st ∗
        ∃ hs : List mstore, hsl ↦*□ hs ∗ [∗list] x;g ∈ hs;g0s.hist, storeOwn x g) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
