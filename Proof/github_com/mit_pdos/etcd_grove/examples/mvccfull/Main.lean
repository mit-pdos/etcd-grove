/- Lean-first (no Rocq counterpart). The proof of `Main` (Draft's glue): `MainConfig`
(`mainMixOwn`), `Run` at it (`runCfgOk` at `mainConfigM`, `mainConfig_ok`).
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

/-- **`MainConfig`'s configuration is in `Run`'s scope** (its read weights the code's). -/
private theorem mainConfig_ok (mx : Mix) :
    runCfgOk (mainConfigM go!"mvccfull" mx) [W64 1, W64 1, W64 2, W64 1, W64 1, W64 0] := by
  have hk : (keysOf 4).length = 120 := by decide
  have hlim : limOf (mainConfigM go!"mvccfull" mx) = W64 3 := by
    unfold limOf; exact if_pos (show (0 : Int) < sint.Z (W64 3) by decide)
  have hcbl : cblOf (mainConfigM go!"mvccfull" mx) = W64 2 := by
    unfold cblOf; exact if_pos (show (0 : Int) < sint.Z (W64 2) by decide)
  have hdep : (normalizeM (mainConfigM go!"mvccfull" mx)).Depth' = W64 4 := by
    unfold normalizeM mainConfigM; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold readMixOk; refine ⟨by decide, ⟨0, by decide, by decide⟩, by decide⟩
  · show (0 : Int) ≤ sint.Z (W64 12000); decide
  · show sint.Z (W64 12000) < 2 ^ 38; decide
  · show 2 * max 0 (sint.Z (W64 2)) + 4 * max 0 (sint.Z (W64 2)) + 3 ≤ 2 ^ 28; decide
  · rw [hlim]; decide
  · rw [hcbl]; unfold mvcc.batchLimitOk; decide
  · rw [hdep, show sint.nat (W64 4) = 4 by decide, hk]; decide

theorem Main.wp_proof
    (wp_MainConfig : MainConfig.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ _ hdbo hdbc
  wp_start as ⟨Hfiles, Htok, #Hvoff⟩
  (try wp_auto)
  wp_apply wp_MainConfig as %mx Hmix
  iunfold mainMixOwn at Hmix
  icases Hmix with ⟨%Hp, Hs, Ho, Hc, Hr, Hrd, Ha, Hst⟩
  have hcfg := mainConfig_ok mx
  (try wp_auto)
  wp_apply (wp_Run (mainConfigM go!"mvccfull" mx)
      [W64 1, W64 1, W64 2, W64 1, W64 1, W64 0] hcfg hdbo hdbc)
    $$ [Hfiles Htok Hvoff Hs Ho Hc Hr Hrd Ha Hst] as %rep -
  · iframe Htok Hvoff
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
