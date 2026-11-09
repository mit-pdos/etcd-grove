/- Lean-first (no Rocq counterpart). The proof of `stream.covered`: Draft, to come (`sorry`).

The callees in call order: `stream.expect`, `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__covered
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem stream.covered.wp_proof
    (wp_stream_expect : stream.expect.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.covered.spec (GF := GF) (hG := hG) := by
  intro s x h γh Hlb w wv kk e p what dqw dqk dqe hrev hidx hp hp' hnone
  wp_start as ⟨#Hsx, #Hxh, Hw, Hk, He, Hrd, #Hlb⟩
  wp_auto
  wp_apply wp_stream_expect s x h γh Hlb w wv kk e p dqw dqk dqe hrev hidx hp hp'
    $$ [$Hsx $Hxh $Hw $Hk $He $Hrd $Hlb] as %ch %r %ok ⟨Hw, Hk, He, Hrd, %Hres⟩
  have hok : ok = false := by unfold expRes at Hres; rw [hnone] at Hres; exact Hres
  subst hok
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
