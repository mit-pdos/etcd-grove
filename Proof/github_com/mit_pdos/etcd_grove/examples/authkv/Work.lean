/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/Work.lean` (`notes/authkv-main-plan.md`;
draft, 2026-10-29): **not proved** (a `sorry`, one of the skeleton's stubs). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Work
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkKVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkTxnReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Work.wp_proof
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG))
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_checkKVs : checkKVs.spec (GF := GF) (hG := hG))
    (wp_checkTxnReads : checkTxnReads.spec (GF := GF) (hG := hG))
    (wp_Permitted : Permitted.spec (GF := GF) (hG := hG)) :
    Work.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
