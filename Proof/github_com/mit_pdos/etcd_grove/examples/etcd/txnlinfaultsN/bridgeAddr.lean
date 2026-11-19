/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/bridgeAddr.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.bridgeAddr
public import Spec.strconv.FormatUint
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlinfaultsN

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]

theorem bridgeAddr.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    bridgeAddr.spec (GF := GF) (hG := hG) := by
  intro i
  wp_start
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_FormatUint as %_ %Hs
  · iframe #; ipureintro; decide
  (try wp_auto)
  iapply HΦ
  ipureintro
  subst Hs
  rfl

end proof

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial
