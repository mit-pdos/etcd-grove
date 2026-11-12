/-
`(*leaseCache).evalOps` (`cache.go`), with a read lock held: each op's cached answer (a range
response), `ok` false unless every op is a cacheable get of a cached key. Proof sketch: the entries
in `lcHeld`, `leaseKey.get` of each (with its entry's `entryOk`), the facts' latest state (`etcdLb_ord`).
Changes: from `specs-ref`'s `leaseCache__evalOps.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `lc.evalOps(ops)` under a read lock: if `ok`, fresh range responses, one per op, each
`leaseKey.get` of an entry of its key (`entryOk` at a state reached). -/
def leaseCache.evalOps.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (q : Qp) (ops : GoSlice) (os : List OpM),
  {{ lcHeld (GF := GF) lc γ γL q ∗ opsAt ops os }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"evalOps")) (Val #ops))
  {{ (rs : GoSlice) (ok : Bool), RET (PairV #rs #ok); lcHeld lc γ γL q ∗ opsAt ops os ∗
      (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ (σ0 : State) (mes : List RangeRespM), etcdLb γ σ0 ∗
         ([∗list] o; me ∈ os; mes, entryOk γL o.key σ0 me) ∗
         msgsOwn responseOpOwn rs (DFrac.own 1) (List.zipWith (fun o me => ResponseOpM.range (leaseGetM o me)) os mes) ∗
         ⌜∀ o ∈ os, o.t = tRange ∧ isBadOpM o = false⌝)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
