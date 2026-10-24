/-
`intervalTree.Visit` (`interval_tree.go`) over a comparator, for a visitor that may stop: the
proof of `Spec/.../adt/intervalTree__Visit_gen.lean` (unit 4, generalized in the auth plan's S2b).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__visit

@[expose] public section

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

theorem adt.intervalTree.Visit_gen.wp_proof
    (h_visit : adt.intervalNode.visit.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e q ivv I J
  wp_start as ⟨Ht, Hkb, Hke, #Hivv, HI⟩
  icases adt.ownIvtK_read K _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  ipersist ivv
  simp only [recv_eq_func_mk]
  let I' : List (Loc × adt.Entry) → IProp GF :=
    fun acc => I (acc.map fun x => (x.1.[intervalNode, go!"iv"], x.2))
  let J' : List (Loc × adt.Entry) → IProp GF :=
    fun acc => J (acc.map fun x => (x.1.[intervalNode, go!"iv"], x.2))
  wp_apply (h_visit K hK tv.sentinel' q tv.sentinel' tv.root' T ivl_ptr (DFrac.own 1) vb ve db de
    b e _ (adt.stab (b, e) T.inorder) I' J' [] hsorted (by simp) (fun _ => by simp))
    $$ [Hn ivl Hkb Hke HI] as %r ⟨ivl, Hkb, Hke, %ns, %es, %Hes, Hn, HI⟩
  · iframe Hn ivl Hkb Hke
    isplitr [HI]
    · iunfold adt.nodeVisitorOk
      imodintro
      iintro %n %z %acc %Φ'
      imodintro
      iintro ⟨%hpre, HIa, Hivn⟩ HΦ'
      wp_auto
      ihave Hivv' := Hivv
      iunfold adt.ivVisitorOkK at Hivv'
      ispecialize Hivv' $$ %(n.[intervalNode, go!"iv"]) %z
        %(acc.map fun x => (x.1.[intervalNode, go!"iv"], x.2))
      simp only [I', J', List.map_append, List.map_cons, List.map_nil]
      wp_bind (App (Val #ivv) (Val #(n.[intervalNode, go!"iv"])))
      iapply Hivv' $$ [HIa Hivn]
      · iframe
        ipureintro
        simpa [List.map_map, Function.comp_def] using hpre
      inext
      iintro %rv HIa
      wp_auto
      ispecialize HΦ' $$ %rv
      iapply HΦ'
      iexact HIa
    simp only [I', List.map_nil]
    iexact HI
  ihave %hlen := adt.ownNodeH_length K _ _ _ _ _ _ _ $$ Hn
  iapply HΦ
  iframe Hkb Hke
  iexists ns.map fun m => m.[intervalNode, go!"iv"], es, r
  isplitl []
  · ipureintro
    exact ⟨Hes.1, by simp [hlen], Hes.2⟩
  isplitl [HI]
  · simp only [I', J', List.nil_append]
    rw [List.zip_map_left]
    have hf : (Prod.map (fun m : Loc => m.[intervalNode, go!"iv"]) (id : adt.Entry → adt.Entry)) =
        (fun x : Loc × adt.Entry => (x.1.[intervalNode, go!"iv"], x.2)) := rfl
    rw [hf]
    cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iexact HI
  iintro Hlent
  iapply Hback
  iframe Hr Hc Hs
  iapply adt.ownNodeH_fill K $$ [Hn Hlent]
  iframe

end proof

end EtcdGrove
end Perennial
