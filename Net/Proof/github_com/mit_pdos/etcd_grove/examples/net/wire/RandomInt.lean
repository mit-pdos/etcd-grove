/-
The proof of `wire.RandomInt` (`Net/Spec/.../wire/RandomInt.lean`): `RandomUint64() % (max + 1)`,
below `max + 1 ≤ 2^31`, so its conversion to `int` is itself.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomInt
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

theorem RandomInt.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    RandomInt.spec (GF := GF) (hG := hG) := by
  intro max
  wp_start as %Hmax
  (try wp_auto)
  wp_apply wp_RandomUint64 as %r -
  have hm : (max + W64 1).toNat = max.toNat + 1 := by word
  have hz : uint.Z (max + W64 1) ≠ 0 := by word
  rw [ite_eq_right_of_eq_false _ _ (eq_false hz)]
  (try wp_auto)
  iapply HΦ
  ipureintro
  have hpos : 0 < (max + W64 1).toNat := by omega
  have h := Nat.mod_lt r.toNat hpos
  rw [← BitVec.toNat_umod] at h
  constructor <;> word
