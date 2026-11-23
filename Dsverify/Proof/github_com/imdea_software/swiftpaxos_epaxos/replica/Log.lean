/-
The framework's logging through its embedded logger (`r.Println`, `r.Printf`, `r.Fatal`), from
`dlog`'s specs (non-verbose logger).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Core
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Misc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem wp_rPrintln (hP : dlog.Logger.Println.spec (GF := GF)) (γ : EpNames) (r : Loc) (id : Nat)
    (L : List GoString) (p : FwPtrs) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
        fwRO γ r id L p }}
      (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"Println")) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hro
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, -⟩
  rw [dlog_zero_logger] at *
  wp_auto
  wp_apply (hP p.logger null _) $$ [$HLogv]
  wp_end

theorem wp_rPrintf (hP : dlog.Logger.Printf.spec (GF := GF)) (γ : EpNames) (r : Loc) (id : Nat)
    (L : List GoString) (p : FwPtrs) (f : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
        fwRO γ r id L p }}
      (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"Printf")) (Val #f))
        (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hro
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, -⟩
  rw [dlog_zero_logger] at *
  wp_auto
  wp_apply (hP p.logger null _ _) $$ [$HLogv]
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
