/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/ipv4port/FromHostPort.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension; the configured addresses are the port's (`ipv4port.addrs`), whose IP
bytes are exact (`ipBytes_intro'` without the lab's `ipBytes_intro`).
-/
/-
`(*IPv4Port).FromHostPort` on a configured address: the four runs of the parser, each
symbolically executed (its loops unrolled: the input is a literal).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Decimal

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

attribute [local instance] pure_test_execute pure_test_continue pure_test_break

/-- Evaluate the word literals' arithmetic everywhere (the concrete runs of the parser). -/
macro "lit_simp" : tactic => `(tactic| (simp only [W64, W8, BitVec.reduceOfInt, BitVec.reduceAdd,
  BitVec.reduceMul, BitVec.reduceSub, uint.Z, sint.Z, BitVec.reduceToNat, BitVec.reduceToInt,
  Int.reduceAdd, Int.reduceMul, Int.reduceNatCast, List.length_cons, List.length_nil,
  Nat.reduceAdd] at *))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

theorem ipv4port.octets_split (p : Loc) (a : GoArray w8 4) (x0 x1 x2 x3 : w8)
    (h : a.arr = [x0, x1, x2, x3]) :
    typedPointsto (GF := GF) p a (DFrac.own 1) ⊢
      typedPointsto (arrayIndexRef w8 (sint.Z (W64 0)) p) x0 (DFrac.own 1) ∗
      typedPointsto (arrayIndexRef w8 (sint.Z (W64 1)) p) x1 (DFrac.own 1) ∗
      typedPointsto (arrayIndexRef w8 (sint.Z (W64 2)) p) x2 (DFrac.own 1) ∗
      typedPointsto (arrayIndexRef w8 (sint.Z (W64 3)) p) x3 (DFrac.own 1) := by
  iintro Harr
  icases typedPointsto_split _ _ _ $$ Harr with Harr
  simp only [TypedPointsto.typedPointstoDef]
  icases Harr with ⟨%Hlen, Harr⟩
  unfold arrayElems
  rw [h]
  icases BigSepL.bigSepL_cons.1 $$ Harr with ⟨H0, Harr⟩
  icases BigSepL.bigSepL_cons.1 $$ Harr with ⟨H1, Harr⟩
  icases BigSepL.bigSepL_cons.1 $$ Harr with ⟨H2, Harr⟩
  icases BigSepL.bigSepL_cons.1 $$ Harr with ⟨H3, -⟩
  iframe

theorem ipv4port.ipCfg_unseal (v : ipv4port.IPv4Port) (a : GoString) :
    ipv4port.ipCfg (GF := GF) (hG := hG) v a = ipv4port.ipCfgDef v a := by
  with_unfolding_all rfl

theorem ipv4port.ipBytes_intro' (s : GoSlice) (l : List w8) :
    (s ↦*□ l : IProp GF) ⊢ ⌜l = [W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0,
      W8 0, W8 0, W8 255, W8 255, W8 127, W8 0, W8 0, W8 1]⌝ -∗
      s ↦*□ ([W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0,
      W8 0, W8 0, W8 0, W8 255, W8 255, W8 127, W8 0, W8 0, W8 1] : List w8) := by
  iintro H %h
  subst h
  iexact H

set_option maxHeartbeats 0 in
theorem ipv4port.IPv4Port.FromHostPort.wp_proof : ipv4port.IPv4Port.FromHostPort.spec (GF := GF) (hG := hG) :=
    fun p v0 a ha => by
  simp only [ipv4port.addrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (
    wp_start as Hp
    rw [doFor_unseal]
    wp_auto
    icases ipv4port.octets_split octets_ptr (Perennial.zero_val (GoArray w8 4)) (W8 0) (W8 0) (W8 0)
      (W8 0) rfl $$ octets with ⟨Ho0, Ho1, Ho2, Ho3⟩
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    repeat (first | (wp_call; try wp_auto) | wp_auto | lit_simp)
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte)
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    ipersist Hsl
    repeat (first | (wp_apply ipv4port.wp_decimal) | (wp_call; try wp_auto) | wp_auto | lit_simp)
    iapply HΦ
    iexists _
    iframe Hp
    rw [ipv4port.ipCfg_unseal]
    unfold ipv4port.ipCfgDef
    isplitr
    · ipureintro
      refine ⟨by simp [ipv4port.addrs], ?_⟩; dsimp only; decide
    ihave H := ipv4port.ipBytes_intro' _ _ $$ Hsl
    iapply H
    ipureintro
    decide)

end proofs
end Perennial.github_com.tangledbytes.go_vsr.pkg
