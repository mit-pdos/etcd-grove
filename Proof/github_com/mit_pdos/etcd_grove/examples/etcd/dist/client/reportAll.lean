/-
Proof of `reportAll.spec`. Lean-first (no Rocq counterpart); #50 N10a.

`CallAll` with goroutine `c`'s resource the node's protocols, call unit, input and update, and its
result `Report`'s answer; the closure `func(a, in) { return remote.Report(a, in, codec, d) }` reads
`codec` and `d`, read-only once the closure is made.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Report

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [field_sem : net.FieldAssumptions]

theorem reportAll.wp_proof
    (wp_CallAll : CallAll.spec (GF := GF) (hG := hG))
    (wp_Report : ∀ [π : NetProtoGS] [ρ : RemoteGS] {I O : Type} [Pos.Countable I] [Pos.Countable O],
      github_com.mit_pdos.etcd_grove.examples.lib.remote.Report.spec (GF := GF) (hG := hG) (I := I) (O := O)) :
    reportAll.spec (GF := GF) (hG := hG) := by
  intro π ρ I O _ _ S nodes insl ns xs inp K cd d Htb Hxl
  wp_start as ⟨Htok, #Hns, #Hxs, #Hmap, #Hwire, Hper⟩
  wp_auto
  ipersist codec
  ipersist d
  wp_apply (wp_CallAll nodes insl ns xs _
      (fun c => iprop(∃ (a : GoString) (x : GoInterface),
        ⌜ns[c]? = some a ∧ xs[c]? = some x⌝ ∗ svcAddr (Gg := hG.goose_globalGS) S a ∗
        budUnit (Gg := hG.goose_globalGS) a ∗ S.ivAt x (inp c) ∗ S.upd (inp c) (K c)))
      (fun c v ok => iprop(⌜ok = false⌝ ∨
        (⌜ok = true⌝ ∗ ((∃ o, S.ovAt v o ∗ K c o) ∨ ⌜S.unkAns (inp c) v⌝))))
      Htb Hxl) $$ [Htok Hper] as %outs %oks ⟨Htok, %Hl, Hres⟩
  · iframe Htok Hper
    iframe #
    iintro !> %c %a %x %Hax %Ψ !> HP HΨ
    rw [← recv_eq_func_mk]
    wp_auto
    icases HP with ⟨%a', %x', %Hax', #Ha, Hbud, #Hx, Hupd⟩
    obtain ⟨rfl, rfl⟩ : a' = a ∧ x' = x := by
      constructor
      · have h := Hax'.1; rw [Hax.1] at h; exact (Option.some.inj h).symm
      · have h := Hax'.2; rw [Hax.2] at h; exact (Option.some.inj h).symm
    wp_apply (wp_Report S _ _ (inp c) (K c) cd d) $$ [Hbud Hupd] as %v %ok Hr
    · iframe Hbud Hupd
      iframe #
    (try wp_auto)
    iapply HΨ
    iexact Hr
  try wp_auto
  iapply HΦ
  iframe Htok
  isplitr
  · ipureintro; exact Hl
  iexact Hres

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
