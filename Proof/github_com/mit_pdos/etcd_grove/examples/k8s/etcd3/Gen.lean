module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__getW
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genWatch
public import Perennial.Spec.sync.atomic.Int64__Load
public import Perennial.Proof.sync.atomic.Link
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genFrom
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Gen.wp_proof (wp_get : cache.get.spec (GF := GF) (hG := hG))
    (wp_getW : cache.getW.spec (GF := GF) (hG := hG))
    (wp_genFrom : genFrom.spec (GF := GF) (hG := hG))
    (wp_genWatch : genWatch.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  intro c tbl id
  wp_start as #Hc
  ihave #Hc2 := Hc
  iunfold isCache at Hc2
  icases Hc2 with ⟨-, ⟨%w, %u, %t, #Hw, #Hu, #Ht⟩, #Hd⟩
  wp_auto
  repeat' wp_if_destruct
  all_goals first
    | -- a watcher: `done.Load()`, then a skipped watch or `genWatch` of its cached object
      (wp_apply_core sync.atomic.Int64.wp_Load _ (DFrac.own 1) $$ [] [-]
       · iPkgInit
       iinv Hd with ⟨%v, >Hv⟩ Hclose
       iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑cacheDoneN from
         Std.LawfulSet.empty_subset)
       iintro Hclose2
       inext
       iexists v
       iframe Hv
       iintro Hv
       imod Hclose2 with -
       imod Hclose $$ [Hv] with -
       · inext; iexists v; iexact Hv
       imodintro
       wp_auto
       wp_if_destruct
       · iapply HΦ
         isplitr
         · ipureintro; right; exact ⟨rfl, rfl, fun _ => rfl, fun h => by simp at h⟩
         unfold cachedIn; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
       · wp_apply wp_getW c tbl id $$ [Hc] as %o %ok -
         · iframe Hc
         (try wp_auto)
         wp_apply wp_genWatch id o ok as %x %Hx
         (try wp_auto)
         iapply HΦ
         isplitr
         · ipureintro; exact Or.inr Hx
         unfold cachedIn
         simp only [Hx.2.1, Bool.false_eq_true, ↓reduceIte]
         itrivial)
    | -- a unary client: `genFrom` of its cached object
      (wp_apply wp_get c tbl id $$ [Hc] as %o %ok #Ho
       · iframe Hc
       (try wp_auto)
       wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
       (try wp_auto)
       wp_apply wp_genFrom n id o ok as %x %Hx
       (try wp_auto)
       iapply HΦ
       isplitr
       · ipureintro; exact Or.inl Hx.1
       unfold cachedIn
       by_cases hu : x.UseCached' = true
       · obtain ⟨hok, hc⟩ := Hx.2 hu
         simp only [hu, ↓reduceIte]
         isimp only [hok, ↓reduceIte] at Ho
         rw [hc]; iexact Ho
       · simp only [hu, Bool.false_eq_true, ↓reduceIte]
         itrivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
