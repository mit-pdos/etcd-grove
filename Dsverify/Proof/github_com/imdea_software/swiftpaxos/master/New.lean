/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/New.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`master.New(N, port, conf, lg)`: the frozen spec (`Spec/master/New.lean`) and the full one
(`master.createdFull`, what `Run` needs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.New

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions]

/-- `New`, with `master.createdFull`. -/
abbrev master.New.specFull : Prop :=
  ∀ (N port : w64) (cfgp lg : Loc) (γc γm : GName) (c : Conf) (fr : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      confIs γc c ∗ ⌜uint.nat N = c.n⌝ ∗ monoListAuthOwn (A := List GoString) γm 1 [] ∗
      config.plain cfgp fr ∗ dlog.quiet lg }}
    (App (App (App (App (Val (@! master.New)) (Val #N)) (Val #port)) (Val #cfgp)) (Val #lg))
  {{ (m : Loc), RET #m; master.createdFull m γc γm (uint.nat N) port }}

set_option maxHeartbeats 4000000 in
theorem master.New.wp_proof_full : master.New.specFull := fun N port cfgp lg γc γm c fr => by
  wp_start as ⟨#Hc, %HN, Ha, #Hplain, #Hq⟩
  ihave %Hv := confIs_valid γc c $$ Hc
  have hN : uint.Z N = 3 ∨ uint.Z N = 5 := by
    rcases Hv.1 with h | h
    · left; word
    · right; word
  have hN0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z N := by word
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) N hN0) as %s1 ⟨Hs1, Hc1, %Hcap1⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) N hN0) as %s2 ⟨Hs2, Hc2, %Hcap2⟩
  wp_apply (wp_slice_make3 (V := w64) (W64 0) N hN0) as %s3 ⟨Hs3, Hc3, %Hcap3⟩
  wp_apply (wp_slice_make2 (V := Loc) N) as %s4 ⟨Hs4, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := Bool) N) as %s5 ⟨Hs5, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := Bool) N) as %s6 ⟨Hs6, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w64) N) as %s7 ⟨Hs7, -⟩
  · ipureintro; word
  rename_i lk mp
  wp_apply sync.wp_NewCond as %cd #Hcd
  iapply HΦ
  unfold master.createdFull master.createdBody
  iexists _, c, fr
  have hsn : sint.nat N = uint.nat N := by word
  simp only [List.replicate_zero, hsn, show (zero_val w64 : w64) = W64 0 from rfl]
  ihave %Hlk := typedPointsto_not_null _ _ _ $$ «$v6»
  iframe
  isplitr
  · iexact Hq
  isplitr
  · iexact Hc
  isplitr
  · iexact Hplain
  isplitr
  · iexact Hcd
  ipureintro
  refine ⟨HN.symm, by word, rfl, rfl, rfl, by rw [Hcap1]; word, by rw [Hcap2]; word,
    by rw [Hcap3]; word, Hlk⟩

/-- The frozen spec (`Spec/master/New.lean`). -/
theorem master.New.wp_proof : master.New.spec := fun N port cfgp lg γc γm c fr => by
  iintro %Φ Hpre HΦ
  iapply master.New.wp_proof_full N port cfgp lg γc γm c fr $$ Hpre
  inext
  iintro %m Hm
  iapply HΦ
  iapply master.createdFull_created $$ Hm

end proof

end Perennial.github_com.imdea_software.swiftpaxos
