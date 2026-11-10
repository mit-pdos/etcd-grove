/- Lean-first (no Rocq counterpart). The proof of `runner.genEnd` (a `choose(4)` switch: `nil`, the
empty literal, `"d"` converted, `genKey`): proved. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.genEnd.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG)) :
    runner.genEnd.spec (GF := GF) (hG := hG) := by
  intro x ks
  wp_start as Hks
  wp_auto
  wp_apply wp_choose (W64 4) as %c %Hc
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iexists []
    isplitl
    · iapply ownSlice_nil
    ipureintro; exact Or.inl rfl
  · (try wp_auto)
    wp_if_destruct
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sp ⟨Hs, Hcap⟩
      (try wp_auto)
      iapply HΦ
      iexists _
      iframe
      ipureintro; exact Or.inl rfl
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
        (try wp_auto)
        iapply HΦ
        iexists _
        iframe
        ipureintro; exact Or.inr (Or.inl rfl)
      · (try wp_auto)
        wp_apply wp_genKey x ks $$ [$Hks] as %sl ⟨%k, Hsl, %Hk⟩
        (try wp_auto)
        iapply HΦ
        iexists _
        iframe
        ipureintro; exact Or.inr (Or.inr Hk)

end proof

end mvccfull
end EtcdGrove
end Perennial
