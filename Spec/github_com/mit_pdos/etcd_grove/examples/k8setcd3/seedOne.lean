/- Lean-first (no Rocq counterpart).

`seedOne(cli, st, k)` (k8setcd3.go): the put of the key `k`'s object of value `x` in the older
encoding through the client `cli` (`New`'s, of the one member `x`, one attempt), during the seeding
(`seedInv`, `Main`'s half of the state at `σ`): its update fires at `σ` (`seed_au`), and the result
is the store `st` with the item at the put's revision (`σ.rev + 1`), `Main`'s half at the put's
next state; or `false`.
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
abbrev seedOne.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (x : client.SrvAt GF) (V : client.WEnv GF) (γs : GName) (s0 : mstore) (g : GSt)
    (k : GoString) (σ : KVState),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  (∀ op, x.γr.kv.wl.writes op) → k.length < 256 → g.items.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl [x.addr] V ∗ client.clientWriteOnce cl [x.addr] ∗ client.kvRegsAt x ∗
      seedInv γs x.γr.kv ∗ ghostVar γs (1 : Qp).half σ ∗ storeOwn s0 g }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.seedOne)) (Val #cl)) (Val #s0)) (Val #k))
  {{ (s' : mstore) (ok : Bool), RET (PairV #s' #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ ghostVar γs (1 : Qp).half (kvOpStep (seedOp k) σ) ∗
        storeOwn s' ⟨setItemL g.items ⟨k, ⟨k, go!"x", W64 ((σ.rev + 1 : Nat) : Int)⟩, false⟩,
          W64 ((σ.rev + 1 : Nat) : Int)⟩ ∗ ⌜σ.rev + 4 < 2 ^ 63⌝) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
