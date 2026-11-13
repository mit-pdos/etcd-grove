/-
`Cursor.next` of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): `elemRef.count` at any level of a writer path (`wp_lvl_count`: a branch level's page's
count, `wp_br_count`, through the node or the view page; the leaf's entries, `WFirst.wp_top_count`),
and the stack ownership of a truncated stack (`wStkOwn_trunc`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WNextPure
public import Proof.go_etcd_io.bbolt.Read.WFirstTop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WNext

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common WGoFirst

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The stack ownership of a truncated stack** (its top replaced by a reference to the same page
and node). -/
theorem wStkOwn_trunc (r : TxReg) (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat)
    (ipg : List w8) (E T : List elemRef) (e e' : elemRef) (hpg : e'.page' = e.page')
    (hnd : e'.node' = e.node') :
    wStkOwn (GF := GF) r nl v rt ipg (E ++ e :: T) ⊢ wStkOwn r nl v rt ipg (E ++ [e']) := by
  unfold wStkOwn
  have hinl : wInlOwn (GF := GF) v rt ipg (E ++ e :: T) = wInlOwn v rt ipg (E ++ [e']) := by
    cases E with
    | nil => simp only [List.nil_append, wInlOwn, hpg, hnd]
    | cons a t => rfl
  rw [hinl]
  iintro ⟨Hn, Hi⟩
  iframe Hi
  icases (BigSepL.bigSepL_append (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).1 $$ Hn with ⟨HE, Ht⟩
  icases (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).1 $$ Ht with ⟨He, -⟩
  iapply (BigSepL.bigSepL_snoc (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).2
  iframe HE
  unfold nodeLoc
  rw [hnd]
  iexact He

/-- **`count()` of a branch level of a writer path**: its page's count (a node's entries are its
page's, `top_node`; a page reference is the view page). -/
theorem wp_br_count
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hc : wCurCtx X n bl rt) (hp : sPathR nl X.v bl rt els pids)
    (hnl : ∀ e ∈ els, e.node' ≠ null → nl e.node' = X.nloc !! e.node')
    (j : Nat) (x : elemRef) (pid : Nat) (pg : List w8) (hx : els[j]? = some x)
    (hpid : pids[j]? = some pid) (hj : j + 1 < els.length) (hpg : X.v.pages !! pid = some pg)
    (ptr : Loc) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ x }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (pageCount pg : Int)); wtxWQ K tx r m q X ∗ ptr ↦ x }} := by
  have hok := hc.1
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  obtain ⟨h2, -, h4096, -⟩ := Read.viewWF_page X.v hvw pid pg hpg
  obtain ⟨-, -, a3, -⟩ := hp.2.2.2 j x pid hx hpid
  obtain ⟨pg0, hpg0, hbr, -, -⟩ := a3 hj
  rw [hpg] at hpg0; cases hpg0
  iintro %Φ ⟨Hw, He⟩ HΦ
  by_cases hnn : x.node' = null
  · have hpl : x.page' = pageLoc X.v pid := ((hp.2.2.2 j x pid hx hpid).2.1 hnn).2 (by omega)
    ihave #Hsrc : srcLoc X.v x.page' Src.view pg $$ []
    · rw [hpl]; iapply srcLoc_view_page X.v pid pg hpg
    wp_apply WFirst.wp_count_page hCnt K tx r m q X ptr x Src.view pg hnn (by omega)
      $$ [Hw He] as ⟨Hw, He⟩
    · iframe; iframe #
    iapply HΦ
    iframe
  · obtain ⟨E, x', T, hE, hEl, hEx⟩ := Prev.split_at els j (by omega)
    rw [hx] at hEx; cases hEx
    obtain ⟨P, p', U, hP, hPl, hPx⟩ := Prev.split_at pids j (by have := hp.2.1; omega)
    rw [hpid] at hPx; cases hPx
    subst hE hP
    have hTne : T ≠ [] := by
      intro h; subst h; simp at hj; omega
    obtain ⟨hpre, -⟩ := trunc_prefix nl X.v hvw bl rt E T x x P U pid (by omega) hp rfl rfl
      (fun _ pg' hpg' => by
        obtain ⟨pg1, hpg1, -, hlt, -⟩ := a3 hj
        rw [hpg'] at hpg1; cases hpg1; exact hlt)
    have hpre' := sPrefix_congr nl (nlX X) X.v bl rt _ _ (fun e he hne => by
      apply hnl e _ hne
      rcases List.mem_append.1 he with h | h
      · exact List.mem_append.2 (Or.inl h)
      · simp at h; subst h; simp) hpre
    obtain ⟨rn, hrn, hlv, hleaf, hbrn⟩ := top_node X n bl rt B hc hB _ _ hpre' x pid (by simp)
      (by simp) hnn
    cases hl : rn.nv.isLeaf' with
    | true =>
      exfalso
      have hp2 := hleaf hl
      obtain ⟨-, -, -, c4⟩ := hp2.2.2.2 E.length x pid (by simp) (by rw [show E.length = P.length by omega]; simp)
      exact leaf_not_branch X.v hvw pid pg hpg hbr (c4 (by simp))
    | false =>
      obtain ⟨-, pg1, hpg1, -, -, hlen, -⟩ := hbrn hl
      rw [hpg] at hpg1; cases hpg1
      wp_apply WFirst.wp_count_node K tx r m q X bl B ptr x rn hB hnn hrn hlv $$ [Hw He]
        as ⟨Hw, He⟩
      · iframe
      rw [hlen]
      iapply HΦ
      iframe

/-- **`count()` of any level of a writer path whose leaf page holds its entries**: `cntAt`. -/
theorem wp_lvl_count
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (els : List elemRef)
    (pids : List Nat) (hc : wCurCtx X n bl rt) (hp : sPathR nl X.v bl rt els pids)
    (hlo : sLeafOK X.v ipg (wEs X n) pids els) (j : Nat) (hj : j < els.length) (x : elemRef)
    (hx : els[j]? = some x) (ptr : Loc) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ x ∗ wStkOwn r nl X.v rt ipg els }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (cntAt X.v (wEs X n) pids els j : Int)); wtxWQ K tx r m q X ∗ ptr ↦ x ∗
      ⌜cntAt X.v (wEs X n) pids els j < 2 ^ 63⌝ }} := by
  iintro %Φ ⟨Hw, He, #Hown⟩ HΦ
  by_cases hj1 : j + 1 < els.length
  · obtain ⟨pid, pg, hpid, hpg, -, -⟩ := sPathR_br nl X.v bl rt pids els hp j hj1 x hx
    rw [cntAt_br X.v (wEs X n) pids els j pid pg hj1 hpid hpg]
    unfold wStkOwn
    icases Hown with ⟨#Hnls, -⟩
    icases WBridge.wtxWQ_nodeLoc_agree K tx r m q X nl els $$ [Hw] with ⟨Hw, %Hag⟩
    · iframe; iframe #
    wp_apply wp_br_count hCnt K tx r m q X n bl rt nl els pids hc hp Hag j x pid pg hx hpid hj1 hpg
      ptr $$ [Hw He] as ⟨Hw, He⟩
    · iframe
    iapply HΦ
    iframe
    ipureintro
    have : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    omega
  · rw [cntAt_leaf X.v (wEs X n) pids els j (by omega)]
    have hlast : els.getLast? = some x := by
      rw [List.getLast?_eq_getElem?, show els.length - 1 = j by omega]; exact hx
    obtain ⟨E, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    wp_apply WFirst.wp_top_count hCnt K tx r m q X n bl rt ipg nl E x pids ptr hc hp hlo
      $$ [Hw He] as ⟨Hw, He, %H63⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    ipureintro; exact H63

end proof

end WNext

end bbolt
end EtcdGrove
end Perennial
