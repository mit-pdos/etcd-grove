/- Lean-first (no Rocq counterpart).

`callList(cli)` (linkvtxn.go): a list of the keys `[listFrom, listTo)` through `New`'s client
`cli`, with a read update or none: the failed call's output (`errOut`), or the reply's
(`listOut`) at the state `σ` the update fired at (`□ Q σ`): its revision and its key-values of
the range.
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
abbrev callList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Range" (client.etcdRangeSpec E γr cid mid) ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.callList)) (Val #cl))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, □ Q σ ∗
        ⌜y = listOut (W64 (σ.rev : Int))
            (σ.kvs.filter fun v => inRange listFrom listTo v.key) ∧ σ.rev + 3 < 2 ^ 63⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
