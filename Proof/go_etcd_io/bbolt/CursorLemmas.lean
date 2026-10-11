module
public import Proof.go_etcd_io.bbolt.CursorModel
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.Bucket__pageNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.pageNode(pid)` against the bucket's view: page `pid` (the read path, no node). -/
theorem pageNode_view (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (bl : Loc) (V : BktView) (q : Qp) (pid : w64) (p : Loc) (pg : List w8)
    (Hok : V.ok) (Hwf : V.wfAt pid) (Hpa : V.pageAt pid = some (p, pg)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktCtx bl V ∗ bktPages V q }}
      (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #pid))
    {{ RET (PairV #p #null); bktCtx bl V ∗ bktPages V q }} := by
  iintro %Φ ⟨#Hpkg, Hctx, Hpgs⟩ HΦ
  obtain ⟨p', pg', Hpa', Hlen, Hinl, Hfile, Hkind⟩ := wfAt_page V pid Hok Hwf
  obtain ⟨rfl, rfl⟩ := pageAt_unique Hpa' Hpa
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, %d1, %d2, %d3, %d4, Hb, Hib, Ht, Hdata, Hps, %Hcx⟩
  obtain ⟨Hibr, Hnodes, Hrn, Htdb, Htp, Hbp, Hdn⟩ := Hcx
  icases bktPages_acc V q pid p' pg' Hok Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
  ihave ⟨Hin, Hout⟩ : (if ib.root' = W64 0 then True else
        bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
        structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗
        bytesPointsto (V.data +ₗ uint.Z (pid * V.ps)) (DFrac.own q) pg') ∗
      (if ib.root' = W64 0 then bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
        structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗ bytesPointsto p' (DFrac.own q) pg'
       else True) $$ [Ht Hdata Hps Hpg]
  · by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr), ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr), ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr
      rw [← (Hfile Hr).1]
      iframe
  have Hp : (if ib.root' = W64 0 then bv.page' else V.data +ₗ uint.Z (pid * V.ps)) = p' := by
    by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      rw [Hibr] at Hr; rw [Hbp Hr, (Hinl Hr).2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr; rw [(Hfile Hr).1]
  wp_apply hpageNode bl bv d1 ib d2 pid bv.tx' t d3 dbl V.data V.ps d4 (DFrac.own q) pg'
      rfl Hnodes Hrn (fun h => (Hinl (Hibr ▸ h)).1)
      (fun h => ⟨Htdb, Htp, Hok.1, (Hfile (Hibr ▸ h)).2.2, Hlen, (Hfile (Hibr ▸ h)).2.1, by
        rcases Hkind with ⟨Hfl, _⟩ | ⟨Hfl, _⟩ <;> rw [Hfl] <;> unfold validPageFlags <;> decide⟩)
      $$ [Hb Hib Hin] as ⟨Hb, Hib, Hin⟩
  · iframe
  rw [Hp]
  ihave ⟨Ht, Hdata, Hps, Hpg⟩ : bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗ bytesPointsto p' (DFrac.own q) pg' $$ [Hin Hout]
  · by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr), ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      icases Hout with ⟨Ht, Hdata, Hps, Hpg⟩
      iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr), ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr
      rw [← (Hfile Hr).1]
      icases Hin with ⟨Ht, Hdata, Hps, Hpg⟩
      iframe
  ispecialize Hpgsback $$ Hpg
  iapply HΦ
  iframe
  ipureintro; exact ⟨Hibr, Hnodes, Hrn, Htdb, Htp, Hbp, Hdn⟩

end proof

end bbolt
end EtcdGrove
end Perennial
