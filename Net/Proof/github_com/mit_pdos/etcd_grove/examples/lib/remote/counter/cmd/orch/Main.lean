/-
The proof of the counter instance's `cmd/orch` `main`: `counter.Orch([]string{ClientAddr0,
ClientAddr1})`, the slice made read-only for `remote.Check`'s clients.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch.Base
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Orch

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch

open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.orch.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Orch : counter.Orch.spec (GF := GF) (hG := hG)) (γs : GName)
    (γp : PendNames) (hrb : receiptBound GF ≤ 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch ∗
        remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) go!"127.0.0.1:7302" ∗
        remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) go!"127.0.0.1:7303" ∗
        mapCtx (Gg := hG.goose_globalGS) (I := Bool) ∗
        pendCtx (Gg := hG.goose_globalGS) (cR (GF := GF) γs) (cS (GF := GF)) γp ∗
        pendLib (Gg := hG.goose_globalGS) (cS (GF := GF)) γp (cS (GF := GF)).M.init ∗
        budUnits (Gg := hG.goose_globalGS) go!"127.0.0.1:7302" 60 ∗
        budUnits (Gg := hG.goose_globalGS) go!"127.0.0.1:7303" 60 }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Ha0, #Ha1, #Hmap, #Hpend, Hlib, Hb0, Hb1⟩
  ihave #Hcp : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_slice_literal (l := [go!"127.0.0.1:7302", go!"127.0.0.1:7303"])); isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  imod ownSlice_persist $$ Hsl with #Hsl
  (try wp_auto)
  ihave Hbud : ([∗list] a ∈ [go!"127.0.0.1:7302", go!"127.0.0.1:7303"],
      budUnits (Gg := hG.goose_globalGS) a 60 : IProp GF) $$ [Hb0 Hb1]
  · iapply BigSepL.bigSepL_cons.2
    iframe Hb0
    iapply BigSepL.bigSepL_cons.2
    iframe Hb1
    iapply BigSepL.bigSepL_nil.2
    iempintro
  wp_apply wp_Orch γs γp _ [go!"127.0.0.1:7302", go!"127.0.0.1:7303"] rfl hrb $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply BigSepL.bigSepL_nil.2
    iempintro
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch
end Perennial
