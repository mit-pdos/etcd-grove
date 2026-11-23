/-
The logging methods epaxos calls on itself (`r.Printf`, `r.Println`: promoted through the embedded
`*replica.Replica` to its embedded `*dlog.Logger`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- `dlog.Logger.Println` on a non-verbose logger (proved here from dlog's code: the package's
proof is not on this branch; a duplicate is harmless). -/
theorem dlog_Println_ok : dlog.Logger.Println.spec (GF := GF) := by
  intro l lg v
  wp_start as #Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  wp_auto
  wp_if_destruct
  · exact (Hnn rfl).elim
  iStructNamed Hl
  wp_auto
  wp_end

theorem dlog_Printf_ok : dlog.Logger.Printf.spec (GF := GF) := by
  intro l lg fmt v
  wp_start as #Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  wp_auto
  wp_if_destruct
  · exact (Hnn rfl).elim
  iStructNamed Hl
  wp_auto
  wp_end

/-- The logger of the framework (an unfold of `fwRO`, see `notes/prove-epaxos.md`). -/
theorem fwRO_logger (γ : EpNames) (rr : Loc) (i : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ rr i L p ⊢ fld rr go!"Logger" ↦□ p.logger ∗
      p.logger ↦□ dlog.Logger.mk null false := by
  rw [fwRO_unseal]; unfold fwRODef
  iintro ⟨#Hl, #Hlg, -⟩
  rw [dlog_zero_logger] at *
  iframe Hl Hlg

theorem wp_ep_Printf (hP : dlog.Logger.Printf.spec (GF := GF)) (γ : EpNames) (r rr : Loc) (i : Nat)
    (L : List GoString) (p : FwPtrs) (fmt : GoString) (args : GoSlice) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"Printf"))
        (Val #fmt)) (Val #args))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hro⟩
  ihave ⟨#Hl, #Hlg⟩ := fwRO_logger _ _ _ _ _ $$ Hro
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hP p.logger null fmt args) $$ [$Hlg]
  wp_end

theorem wp_ep_Println (hP : dlog.Logger.Println.spec (GF := GF)) (γ : EpNames) (r rr : Loc) (i : Nat)
    (L : List GoString) (p : FwPtrs) (args : GoSlice) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"Println")) (Val #args))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hro⟩
  ihave ⟨#Hl, #Hlg⟩ := fwRO_logger _ _ _ _ _ $$ Hro
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hP p.logger null args) $$ [$Hlg]
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
