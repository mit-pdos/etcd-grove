/- Lean-first (no Rocq counterpart). The proof of `Main`: `Run` of its configuration, whose bounds
hold. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.Main

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem Main.wp_proof (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ _ hckpt hdbo hdbc
  wp_start as ⟨Hfile, Htok, #Hvoff⟩
  (try wp_auto)
  wp_apply (wp_Run _ (by word) (by word) (by word) (by word) (by word) (by word)
      hckpt hdbo hdbc) $$ [Hfile Htok] as %rep -
  · iframe Hfile Htok Hvoff
    (try iPkgInit)
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end mvccrand
end EtcdGrove
end Perennial
