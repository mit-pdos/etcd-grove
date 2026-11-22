/-
The proof of `deadline` (`Net/Spec/.../lib/remote/deadline.lean`): `time.Now()`, then its `Add(d)`
(Perennial's specs `time.Now.spec`, `time.Time.Add.spec`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.deadline
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem deadline.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG)) :
    deadline.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_auto
  wp_apply wp_Now as %tm -
  wp_apply wp_Add as %tm' -
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
