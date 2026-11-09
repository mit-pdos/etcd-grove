/-
`(*leaseCache).evalCmp` (`cache.go`), with a read lock held: the comparisons on the cached keys
(`evalCmp`), `ok` false if one has a range or is not cached. Proof sketch: the entries in `lcHeld`;
`evalCmp`. Its answer is not relied on (a cached transaction's branch is any). Changes: from `specs-ref`'s `leaseCache__evalCmp.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `lc.evalCmp(cmps)` under a read lock. -/
def leaseCache.evalCmp.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (q : Qp) (cs : GoSlice) (ms : List (Option EtcdModel.Compare)),
  {{ lcHeld (GF := GF) lc γ γL q ∗ cmpsAt cs ms }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"evalCmp")) (Val #cs))
  {{ (v ok : Bool), RET (PairV #v #ok); lcHeld lc γ γL q }}

end spec

end Leasing
end EtcdGrove
end Perennial
