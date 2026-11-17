/- Lean-first (no Rocq counterpart). The proof of `member.size`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__size
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem member.size.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG)) :
    member.size.spec (GF := GF) (hG := hG) := by
  intro m r v
  wp_start as ⟨Hm, Hr⟩
  wp_auto
  wp_apply wp_choose $$ [$Hr] as %k ⟨⟨%v1, Hr⟩, %hk⟩
  wp_if_destruct
  · wp_apply wp_choose $$ [$Hr] as %x ⟨Hr, %hx⟩
    rw [if_neg (by decide)] at hx
    iapply HΦ
    iframe
    ipureintro
    constructor <;> word
  wp_if_destruct
  · wp_apply wp_choose $$ [$Hr] as %x ⟨Hr, %hx⟩
    rw [if_neg (by decide)] at hx
    iapply HΦ
    iframe
    ipureintro
    constructor <;> word
  wp_if_destruct
  · wp_apply wp_choose $$ [$Hr] as %x ⟨Hr, %hx⟩
    rw [if_neg (by decide)] at hx
    iapply HΦ
    iframe
    ipureintro
    constructor <;> word
  wp_apply wp_choose $$ [$Hr] as %x ⟨Hr, %hx⟩
  rw [if_neg (by decide)] at hx
  iapply HΦ
  iframe
  ipureintro
  constructor <;> word

end proof

end etcd_wal
end EtcdGrove
end Perennial
