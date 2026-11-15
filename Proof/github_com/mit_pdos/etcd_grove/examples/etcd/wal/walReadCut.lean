/- Lean-first (no Rocq counterpart). The proof of `walReadCut`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walReadCut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walReadFrom

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem walReadCut.wp_proof (wp_walRead : walRead.spec (GF := GF) (hG := hG))
    (wp_walReadFrom : walReadFrom.spec (GF := GF) (hG := hG)) :
    walReadCut.spec (GF := GF) (hG := hG) := by
  intro s h k hw hk
  wp_start as #Hr
  ihave Hr2 := Hr
  iunfold opsRep at Hr2
  icases Hr2 with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  wp_if_destruct
  · wp_apply wp_walRead s h hw as %v %ok Hres
    · iexact Hr
    wp_end
  · have hk' : 0 ≤ sint.Z k ∧ sint.nat k = uint.nat k := by
      have : uint.nat k < 2 ^ 63 := by
        have : sint.nat s.len < 2 ^ 63 := by word
        omega
      constructor <;> word
    wp_apply wp_walReadFrom s h k hw hk'.1 (by omega) as %v %ok Hres
    · iexact Hr
    wp_end
    simp only [tReadCut, Hif, ↓reduceIte]
    rw [← hk'.2]
    iexact Hres

end proof

end etcd_wal
end EtcdGrove
end Perennial
