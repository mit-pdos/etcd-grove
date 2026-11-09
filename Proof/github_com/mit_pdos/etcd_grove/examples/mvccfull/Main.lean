/- Lean-first (no Rocq counterpart). The proof of `Main`: Draft, to come.

The outline: `MainConfig` (`mainMixOwn`), `Run` at it (`runCfgOk`: fails at `readMixOk`, F2).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig

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
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem Main.wp_proof
    (wp_MainConfig : MainConfig.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ _ hckpt hdbo hdbc
  wp_start as ⟨Hfiles, #Hks, Htok, #Hvoff⟩
  (try wp_auto)
  wp_apply wp_MainConfig as %mx Hmix
  iunfold mainMixOwn at Hmix
  icases Hmix with ⟨%Hp, Hs, Ho, Hc, Hr, Hrd, Ha, Hst⟩
  -- `runCfgOk` at `MainConfig`: false as `MainConfig.spec` states it. Its `mainMixOwn` gives the read
  -- weights `[1, 1, 2, 1, 1, 2]` (the hashes `2`, which F1's scope `readMixOk` excludes), but the Go
  -- (`config.go`, and its translation) now has `[1, 1, 2, 1, 1, 0]` (no hash reads until F2): with
  -- `mainMixOwn` at the code's weights, `readMixOk` holds and so does the rest (`Ops = 12000`, 15
  -- threads, the batch limits 3 and 2, the keys of depth 4). Left `sorry`: a spec fix, not this proof's.
  have hcfg : runCfgOk (mainConfigM go!"mvccfull" mx) [W64 1, W64 1, W64 2, W64 1, W64 1, W64 2] := by
    sorry
  (try wp_auto)
  wp_apply (wp_Run (mainConfigM go!"mvccfull" mx)
      [W64 1, W64 1, W64 2, W64 1, W64 1, W64 2] hcfg hckpt hdbo hdbc)
    $$ [Hfiles Hks Htok Hvoff Hs Ho Hc Hr Hrd Ha Hst] as %rep -
  · iframe Hks Htok Hvoff
    isplitl [Hs Ho Hc Hr Hrd Ha Hst]
    · iunfold mixOwn
      simp only [mainConfigM]
      iexists DFrac.own 1, _, _, _, _, _, _
      iframe
    have hfp : filePathsM (mainConfigM go!"mvccfull" mx) =
        filePathsM (mainConfigM go!"mvccfull" (zeroValDef : Mix)) := rfl
    rw [hfp]
    iexact Hfiles
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end mvccfull
end EtcdGrove
end Perennial
