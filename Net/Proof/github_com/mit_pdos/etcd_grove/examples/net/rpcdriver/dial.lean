/- Lean-first (no Rocq counterpart).

# `dial`'s proof: `rpc.Dial` at `TCPAddr` or `rpc.DialHTTP` at `HTTPAddr`
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.dial
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem dial.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_Dial : net.rpc.Dial.spec (GF := GF) (hG := hG))
    (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG)) :
    dial.spec (GF := GF) (hG := hG) := by
  intro W
  wp_start as ⟨%Hrb, #Hcli, #Hhttp, #Hcon, #Htcp, #Hha⟩
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  try wp_auto
  wp_apply wp_below (W64 2) as %b -
  wp_if_destruct
  · wp_apply wp_Dial go!"tcp" net.tcpNet_tcp W tcpAddr $$ [$HnetPk $Hcli $Htcp] as %c %err Hr
    · ipureintro; exact Hrb
    try wp_auto
    iapply HΦ
    icases Hr with (⟨%He, Hc⟩ | ⟨%He, -⟩)
    · ileft; iframe %He; iexists tcpAddr; iframe Hc; ipureintro; exact .inl rfl
    · iright; ipureintro; exact He
  · wp_apply wp_DialHTTP go!"tcp" net.tcpNet_tcp W httpAddr $$ [$HnetPk $Hcli $Hhttp $Hcon $Hha] as %c %err Hr
    · ipureintro; exact Hrb
    try wp_auto
    iapply HΦ
    icases Hr with (⟨%He, Hc⟩ | ⟨%He, -⟩)
    · ileft; iframe %He; iexists httpAddr; iframe Hc; ipureintro; exact .inr rfl
    · iright; ipureintro; exact He

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
