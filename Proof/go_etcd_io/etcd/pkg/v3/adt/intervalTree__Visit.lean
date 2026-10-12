module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__visit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Visit.wp_proof
    (h_visit : adt.intervalNode.visit.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Visit.spec (GF := GF) (hG := hG) := by
  intro t L b e q ivv I hq
  wp_start as ⟨Ht, #Hivv, HI⟩
  icases adt.ownIvt_read _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  ipersist ivv
  simp only [recv_eq_func_mk]
  let I' : List (Loc × adt.Entry) → IProp GF :=
    fun acc => I (acc.map fun x => (x.1.[intervalNode, go!"iv"], x.2))
  wp_apply (h_visit tv.sentinel' q tv.sentinel' tv.root' T ivl_ptr (DFrac.own 1) b e _ I' []
    hsorted hq) $$ [Hn ivl HI] as ⟨%ns, Hn, ivl, HI⟩
  · iframe Hn ivl
    isplitr [HI]
    · iunfold adt.nodeVisitorOk
      imodintro
      iintro %n %z %acc %Φ'
      imodintro
      iintro ⟨HIa, Hivn⟩ HΦ'
      wp_auto
      ihave Hivv' := Hivv
      iunfold adt.ivVisitorOk at Hivv'
      ispecialize Hivv' $$ %(n.[intervalNode, go!"iv"]) %z
        %(acc.map fun x => (x.1.[intervalNode, go!"iv"], x.2))
      simp only [I', List.map_append, List.map_cons, List.map_nil]
      wp_bind (App (Val #ivv) (Val #(n.[intervalNode, go!"iv"])))
      iapply Hivv' $$ [HIa Hivn]
      · iframe
      inext
      iintro HIa
      wp_auto
      iapply HΦ'
      iexact HIa
    simp only [I', List.map_nil]
    iexact HI
  ihave %hlen := adt.ownNodeH_length _ _ _ _ _ _ _ $$ Hn
  ispecialize HΦ $$ %(ns.map fun m => m.[intervalNode, go!"iv"])
  iapply HΦ
  isplitl []
  · ipureintro; simpa using hlen
  isplitl [HI]
  · simp only [I', List.nil_append]
    rw [List.zip_map_left]
    have hf : (Prod.map (fun m : Loc => m.[intervalNode, go!"iv"]) (id : adt.Entry → adt.Entry)) =
        (fun x : Loc × adt.Entry => (x.1.[intervalNode, go!"iv"], x.2)) := rfl
    rw [hf]
    iexact HI
  iintro Hlent
  iapply Hback
  iframe Hr Hc Hs
  iapply adt.ownNodeH_fill $$ [Hn Hlent]
  iframe

end proof

end EtcdGrove
end Perennial
