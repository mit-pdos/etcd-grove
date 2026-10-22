/- Lean-first (no Rocq counterpart).

`callTxn(cli, in)` (linkvtxn.go): a transaction (`in` decoding to `.txn cs t e`, not empty)
through `New`'s client `cli` that sends a write at most once, with the update its kind takes
(`callUpd`): the failed call's output (`errOut`), or the reply's at the state `σ` the update
fired at (`callRes`): the server's run of the transaction at `σ` (its verdict and results, as
`call` builds them) and the revision after it (a read-only one's, `σ`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev callTxn.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (x : Input) (cs : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString))
    (Q : KVState → IProp GF), decIn x = some (.txn cs t e) → t ++ e ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] sv ∈ ms, client.kvRegsAt sv) ∗
      ([∧list] sv ∈ ms, callUpd sv.γr.kv (.txn cs t e) Q) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.callTxn)) (Val #cl))
      (Val #x))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, callRes (.txn cs t e) Q σ ∗
        ⌜y = withResL
            (txnBase (if (linkv.MIn.txn cs t e).isWrite then
                (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).1)
            (((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (linkv.txnOf cs t e)).2.2.map linkv.resOf).map encRes) ∧
          σ.rev + 3 < 2 ^ 63⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
