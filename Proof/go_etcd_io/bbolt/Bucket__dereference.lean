/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__dereference.lean` (U9b, `notes/bbolt-proof-plan.md`).

U9b's proof; the spec's premise `derefPre X` (batch 12) is what the code needs beyond `liveFresh`
and `liveReach` (its asserts on non-empty keys, the cached children and root nodes being objects
of the heap, no dead object live).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__dereference
public import Proof.go_etcd_io.bbolt.Spill.BucketDeref
public import Proof.go_etcd_io.bbolt.Spill.DerefWOK

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `derefStep` and the coverage of every bucket reached from the root bucket give `derefRel`. -/
theorem derefRel_of_step (X X' : WX) (h : derefStep X X') (hd : objsDisj X.t)
    (hpre : derefPre X) (hreach : liveReach X) (hcov : bktCov X' X.rl) : derefRel X X' := by
  have hd' := objsDisj_step h hd
  refine ⟨?_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, derefStep_node h, fun bl pid => derefStep_ltree h bl pid,
    derefStep_wtxData h, wOK_derefStep X X' h hd, h⟩
  apply derefOK_of_cov X' hd' (derefPre_step h hpre) (liveReach_step h hreach)
  intro bl B hB hbr rt hrt
  have := reachFrom_of_bktReach hbr
  rw [h.2.2.2.2.1] at this
  exact hcov bl B rt this hB hrt

theorem Bucket.dereference.wp_proof (hRoot : node.root.spec (GF := GF) (hG := hG))
    (hND : node.dereference.spec (GF := GF) (hG := hG)) :
    Bucket.dereference.spec (GF := GF) (hG := hG) := by
  intro K tx r m X Hpre Hfresh Hreach
  iintro %Φ Hw HΦ
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx _ X $$ Hh
  ihave Hw := Hclose $$ %X [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨B, HB⟩ := Option.isSome_iff_exists.1 Hpre.2.2.2.1
  have Hrl : X.rl = tx.[Tx, go!"root"] := Hok.1
  rw [Hrl] at HB
  have Hlive : tx.[Tx, go!"root"] ∈ X.liveB := by
    rw [← Hrl]; exact (Hpre.2.2.1 X.rl B (by rw [Hrl]; exact HB)).1
  have Hp : X.t.bs !! tx.[Tx, go!"root"] = some B ∧ tx.[Tx, go!"root"] ∈ X.liveB ∧ derefPre X ∧
    liveFresh X := ⟨HB, Hlive, Hpre, Hfresh⟩
  iapply (Bucket.dereference.wp_aux hRoot hND) $$ %K %tx %r %m %X %(tx.[Tx, go!"root"]) %B %Hp Hw
  inext
  iintro %X' ⟨Hw, %HX'⟩
  iapply HΦ
  iexists X'
  iframe
  ipureintro
  exact derefRel_of_step X X' HX'.1 Hok.2.1 Hpre Hreach (by rw [Hrl]; exact HX'.2)


end proof

end bbolt
end EtcdGrove
end Perennial
