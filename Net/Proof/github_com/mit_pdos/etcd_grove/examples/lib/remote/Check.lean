/-
The proof of `Check` (`Net/Spec/.../lib/remote/Check.lean`): `Run` with timeout `0`, whose post
says porcupine answered `Ok`, so the `panic` branch is not taken.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Run

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine EtcdGrove.lintest

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St J I O : Type} [DecidableEq J] [Pos.Countable I] [Pos.Countable J] [Pos.Countable O]

theorem Check.wp_proof
    (wp_Run : Run.spec (GF := GF) (hG := hG) (St := St) (J := J) (I := I) (O := O)) :
    Check.spec (GF := GF) (hG := hG) (St := St) (J := J) (I := I) (O := O) := by
  intro R S γ m addrs addrL cd gen ops d HpE HlE HS Hinj HT Hrb H31 Hops Hmul nb Hnb
  wp_start as ⟨#Hcc, #Hm, #Hgen, #Haddrs, #Hra, #Hmap, #Hcd, #Hpend, Hlib, Hbud⟩
  wp_auto
  wp_apply wp_Run R S γ m addrs addrL cd gen ops d (W64 0) HpE HlE HS Hinj HT Hrb H31 Hops Hmul nb Hnb
    $$ [Hlib Hbud] as %r %Hr
  · iframe
    iframe #
  rw [Hr.2 (by decide)]
  wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
