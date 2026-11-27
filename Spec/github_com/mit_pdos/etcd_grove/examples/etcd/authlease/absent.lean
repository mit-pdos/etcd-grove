/-
`absent(root, k, why)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): root's linearizable
`Get(k)`; `false` on an error, a panic if it found a key, else `true`. Lean-first (no Rocq counterpart).

**The triple:** a client `root` of the member at `addr` whose `Range` is etcd's with auth on, the
member's committed index at least `c`, the floor `F`, a lower bound `n` of its published auth index, the
caller's read update `Q` (none, or a persistent `kvReadAu`), and the caller's fact that a reply of the
read finds no key: `absent` returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseEnv
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barrier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]
/-- See the file header. -/
abbrev absent.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (root : Loc) (k why addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cid mid c : w64)
    (n : Nat) (F : mvcc.Log) (P : GoString → IProp GF) (Q : KVState → IProp GF),
  opSizeOk (opGetModel k []) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗ levelTok 0 ∗ (clientTokAt root [addr] P ∗
      isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn (srvTLSId s) E γr cid mid) ∗
      committedAtLeast γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗
      □ (∀ m : RangeRespM, rangeReplyOk E γr c F (rangeWireOf (opGetModel k [])) cid mid Q m -∗
          ⌜m.kvs = []⌝)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.absent)) (Val #root))
      (Val #k)) (Val #why))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (True) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
