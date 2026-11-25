/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/Client.lean`: `AddrOK(ep)`, then
putget's `Client(ep)` (its `Client.spec`, at the share the precondition gives when `ep` is not empty).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Client
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK
public import GooseLang.Ext.Net.Deploy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

theorem Client.wp_proof
    (wp_AddrOK : AddrOK.spec (GF := GF) (hG := hG))
    (wp_Client : etcd_putget_dist.Client.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro _ _ _ ep γE mid Hat
  wp_start as ⟨Hlt, Hsh⟩
  ihave #Hpg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_AddrOK as %b %Hb
  cases b with
  | false =>
    wp_auto
    iapply HΦ; itrivial
  | true =>
  have Hne : ep ≠ [] := fun h => absurd (Hb h) (by decide)
  ihave ⟨%Hok, Hcs⟩ := Hsh $$ %Hne
  wp_auto
  have Hlen : ep.length + 1 < 2 ^ 63 := by have := Net.addrOk_length Hok; omega
  wp_apply (wp_Client ep γE mid Hlen Hat) $$ [Hlt Hcs] as %r -
  · iframe Hlt
    iintro %-
    iexact Hcs
  iapply HΦ; itrivial

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
