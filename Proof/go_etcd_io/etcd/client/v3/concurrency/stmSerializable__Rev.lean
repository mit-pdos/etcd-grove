/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stmSerializable__Rev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Rev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stmSerializable.Rev.wp_proof (hGet : stmSerializable.Get.spec (GF := GF) (hG := hG))
    (hRev : stm.Rev.spec (GF := GF) (hG := hG)) :
    stmSerializable.Rev.spec (GF := GF) (hG := hG) := by
  intro lvl p pfx st k
  wp_start as ⟨Hst, %Hser, %Hpk⟩
  wp_auto
  wp_apply wp_slice_literal (l := [k])
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hksl, -⟩
  ipersist Hksl
  wp_auto
  wp_apply hGet lvl p pfx st _ [k] $$ [$Hpkg $Hst $Hksl] as %v ⟨%st1, Hst, %Hgp⟩
  · ipureintro; refine ⟨Hser, ?_⟩; simpa using Hpk
  unfold stmState
  simp only [stmBase, Hser, ↓reduceIte]
  icases Hst with ⟨#Henv, Hrs, Hws, ⟨%gs, Hopts, %Hgs⟩, #Hcf, ⟨%pre, Hpre, %HpreOk⟩⟩
  have Hgs' : ReadOptsOk gs := by
    unfold GetOptsOk at Hgs
    rw [Hser] at Hgs
    simp only [↓reduceIte] at Hgs
    rcases Hgs with h | ⟨S, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨S, h⟩)
  wp_apply hRev (structFieldRef stmSerializable go!"stm" p) pfx st1.reads gs k $$ [$Hpkg $Henv $Hrs $Hopts] as %r ⟨%reads', Hrs, Hopts, %Hrv⟩
  · ipureintro; exact ⟨Hgs', Hpk⟩
  obtain ⟨Hgw, Hgg, -, Hgv⟩ := Hgp
  obtain ⟨Hrg, e, Hre, Hr⟩ := Hrv
  iapply HΦ
  iexists ({ reads := reads', writes := st1.writes } : STMSt)
  iframe Henv Hrs Hws Hcf
  isplitl [Hopts Hpre]
  · isplitl [Hopts]
    · iexists gs; iframe Hopts; ipureintro; exact Hgs
    iexists pre; iframe Hpre; ipureintro
    intro k' hr hp
    by_cases hk : k' = k
    · subst hk
      rcases Hgv (by simp) with ⟨k'', hk'', hw | ⟨hnw, e1, he1, -⟩⟩
      · simp only [List.mem_singleton] at hk''; subst hk''
        obtain ⟨w, hw, -⟩ := hw
        show (st1.writes !! k'').isSome
        rw [Hgw, hw]; rfl
      · simp only [List.mem_singleton] at hk''; subst hk''
        exact HpreOk k'' (by rw [he1]; rfl) hp
    · rcases Hrg.2 k' hr with h | h
      · exact HpreOk k' h hp
      · simp at h; exact absurd h hk
  ipureintro
  refine ⟨Hgw, ⟨fun k' e' h => Hrg.1 k' e' (Hgg.1 k' e' h), fun k' h => ?_⟩, e, Hre, Hr⟩
  rcases Hrg.2 k' h with h' | h'
  · exact Hgg.2 k' h'
  · exact Or.inr h'

end proof

end concurrency
end EtcdGrove
end Perennial
