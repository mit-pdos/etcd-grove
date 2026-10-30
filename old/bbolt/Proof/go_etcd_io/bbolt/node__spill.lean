module
public import Proof.go_etcd_io.bbolt.SpillNodeCore
public import Spec.go_etcd_io.bbolt.sort__Sort_nodes
public import Spec.go_etcd_io.bbolt.node__split_x
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__write_x
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.Tx__page_w
public import Spec.go_etcd_io.bbolt.TxStats__IncSpill
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Assert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [float_sem : go.FloatConvSemantics]

theorem spillPages_of_view (W : WView) (T : WTx) (id : Nat) (h : (W.pages !! id).isSome) :
    (spillPages W T !! id).isSome := by
  obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 h
  unfold spillPages
  rw [GMap.lookup_union, hpg]; simp

theorem flatten_singles (l : List Loc) : (l.map (fun c => [c])).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl

theorem forall2_leaves (bl : Loc) (B : BRec) :
    ∀ l : List Loc, (∀ c ∈ l, spilledN bl B c) →
      List.Forall₂ (kidsTree B.ns) l (l.map (fun c => [c]))
  | [], _ => List.Forall₂.nil
  | c :: l, h => by
    obtain ⟨rc, hrc, -, hcs, -⟩ := h c (List.mem_cons_self ..)
    exact List.Forall₂.cons (kidsTree_leaf B.ns c rc hrc hcs)
      (forall2_leaves bl B l (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem kidsTree_spilled (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (hn : B.ns !! n = some r)
    (hs : r.nv.spilled' = false) (hnd : r.cs.Nodup) (hsp : ∀ c ∈ r.cs, spilledN bl B c) :
    kidsTree B.ns n (n :: (r.cs.map (fun c => [c])).flatten) := by
  refine kidsTree.mk n r _ hn (forall2_leaves bl B r.cs hsp) ?_
  rw [flatten_singles]
  refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
  obtain ⟨rc, hrc, hs', -⟩ := hsp n hm
  rw [hn] at hrc; cases hrc; rw [hs] at hs'; cases hs'

theorem topSpecB_mono (m M : Nat) (h : m ≤ M) (H : node.spill.topSpecB (GF := GF) (hG := hG) M) :
    node.spill.topSpecB (GF := GF) (hG := hG) m := by
  intro I γd γ W txl txid T ρ F K bl B kd ht0 n r p hf hg hB hlen
  exact H I γd γ W txl txid T ρ F K bl B kd ht0 n r p hf hg hB (by omega)

theorem subSpecB_zero : node.spill.subSpecB (GF := GF) (hG := hG) 0 := by
  intro I γd γ W txl txid T ρ F K bl B bnd kd S n r pl rp ht hf hg hB hHt hlen
  exact absurd hlen (Nat.not_lt_zero _)

theorem bigSepL_ite_true (l : List Loc) (X : Loc → IProp GF) :
    ⊢ [∗list] c ∈ l, (if true = true then (emp : IProp GF) else X c) := by
  induction l with
  | nil => exact BigSepL.bigSepL_nil.2
  | cons a l ih =>
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2
    simp only [ite_true]
    exact emp_sep.2.trans (sep_mono .rfl ih)

theorem node.spill.wp_top
    (hSort : sort.Sort.nodes_spec (GF := GF) (hG := hG))
    (hSplit : node.split.xspec (GF := GF) (hG := hG))
    (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.wspec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hAlloc : Tx.allocate.xspec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hPgid : Meta.Pgid.spec (GF := GF) (hG := hG))
    (hWrite : node.write.xspec (GF := GF) (hG := hG))
    (hKey : Inode.Key.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hAssert : Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG)) :
    node.spill.topSpec (GF := GF) (hG := hG) := by
  intro M
  induction M with
  | zero =>
    intro I γd γ W txl txid T ρ F K bl B kd ht0 n r p hf hg hB hlen
    exact absurd hlen (Nat.not_lt_zero _)
  | succ M ih =>
    intro I γd γ W txl txid T ρ F K bl B kd ht0 n r p hf hg hB hlen hn hpg hpar hleaf hK hL hcs hup
      hpnd hpv hall hthr hps hel hne hP1 hP2 hP3
    have hnd : r.cs.Nodup := (hL.2.2.2.2.2.2.2.2.2 hleaf).2.2.1
    have Hc := node.spill.wp_core hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
      hAssert hInc r.ws.length true (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ m hm => topSpecB_mono m M (by omega) ih) I γd γ W txl txid T ρ F K bl B
      (fun _ => (none, none)) (fun _ => kd) (fun _ => ht0 + 1) n r (fun _ => true) (fun c => [c]) hf hg hB
      (fun h => absurd h (by decide)) (fun h => by rw [hleaf] at h; cases h) (fun _ => by omega)
      hn hK hL
      (fun c hc => ⟨by obtain ⟨rc, hrc, -, hcs', -⟩ := hcs c hc; exact kidsTree_leaf B.ns c rc hrc hcs',
        fun _ => hcs c hc, fun h => absurd h (by decide)⟩)
      (fun _ => ⟨fun _ _ => rfl, Nat.le_refl _⟩) (fun _ => hpar) (fun _ => ⟨p, hup, hpnd, hall, hpv⟩)
      (kidsTree_spilled bl B n r hn hL.2.1 hnd hcs) hthr hps hel hne hP1
      (fun h => absurd h (by decide)) hP2 hP3 (fun h => absurd h (by decide))
      (fun _ => ⟨rfl, p, hup, hpnd, fun l hl => by rw [flatten_singles]; exact hall l hl⟩)
      (fun pl rp h1 h2 => absurd (h1.symm.trans hpar) h2)
      (fun pl rp h1 h2 _ => absurd (h1.symm.trans hpar) h2)
      (fun h => absurd hpar h)
    iintro %Φ ⟨#Hpkg, HR, Hrt⟩ HΦ
    iapply Hc $$ [Hpkg HR Hrt]
    · isplitl []
      · iexact Hpkg
      iframe
      iapply bigSepL_ite_true
    inext
    iintro %err Hpost
    rw [ite_eq_left_of_eq_true _ _ (eq_true hpar)]
    iapply HΦ
    iexact Hpost

/-- Looking the children up among `zip`. -/
def subOf (cs : List Loc) (subs : List (List Loc)) (c : Loc) : List Loc :=
  ((cs.zip subs).lookup c).getD []

theorem subOf_map : ∀ (cs : List Loc) (subs : List (List Loc)), cs.Nodup →
    cs.length = subs.length → cs.map (subOf cs subs) = subs
  | [], [], _, _ => rfl
  | a :: cs, s :: subs, hnd, hl => by
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [List.map_cons, subOf, List.zip_cons_cons, List.lookup_cons, beq_self_eq_true,
      Option.getD_some]
    congr 1
    have ih := subOf_map cs subs hnd' (by simpa using hl)
    refine Eq.trans ?_ ih
    apply List.map_congr_left
    intro c hc
    have hne : (c == a) = false := by
      rw [beq_eq_false_iff_ne]; intro e; subst e; exact ha hc
    simp [subOf, List.lookup_cons, hne]
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem forall2_mem {R : Loc → List Loc → Prop} :
    ∀ (cs : List Loc) (subs : List (List Loc)), List.Forall₂ R cs subs → cs.Nodup →
      ∀ c ∈ cs, R c (subOf cs subs c)
  | [], [], _, _, c, hc => by simp at hc
  | a :: cs, s :: subs, List.Forall₂.cons h1 h2, hnd, c, hc => by
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases e : c = a
    · subst e; simpa [subOf, List.lookup_cons] using h1
    · have hc' : c ∈ cs := by simpa [e] using hc
      have := forall2_mem cs subs h2 hnd' c hc'
      have hne : (c == a) = false := by rw [beq_eq_false_iff_ne]; exact e
      simpa [subOf, List.lookup_cons, hne] using this

/-- A tree of nodes from `n`: its children's trees. -/
theorem kidsTree_split (ns : GMap Loc NRec) (n : Loc) (r : NRec) (S : List Loc)
    (h : kidsTree ns n S) (hn : ns !! n = some r) :
    ∃ subs, List.Forall₂ (kidsTree ns) r.cs subs ∧ S = n :: subs.flatten ∧ S.Nodup := by
  cases h with
  | mk _ r' subs hr hf hnd =>
    rw [hn] at hr; cases hr
    exact ⟨subs, hf, rfl, hnd⟩

theorem bigSepL_flat_sub (cs : List Loc) (sub : Loc → List Loc) (Φ : Loc → IProp GF) :
    ([∗list] l ∈ (cs.map sub).flatten, Φ l) ⊣⊢
      [∗list] c ∈ cs, (if false = true then (emp : IProp GF) else [∗list] l ∈ sub c, Φ l) := by
  simp only [Bool.false_eq_true, ite_false]
  rw [← List.flatMap_def]
  exact BiEntails.of_eq (BigSepL.bigSepL_flatMap sub)

theorem len_le_flatten : ∀ (L : List (List Loc)) (x : List Loc), x ∈ L → x.length ≤ L.flatten.length
  | [], _, h => by simp at h
  | a :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [List.flatten_cons, List.length_append]; omega
    · have := len_le_flatten L x h; simp only [List.flatten_cons, List.length_append]; omega

theorem sub_len_lt (cs : List Loc) (subs : List (List Loc)) (c : Loc) (hc : c ∈ cs)
    (hnd : cs.Nodup) (hl : cs.length = subs.length) :
    (subOf cs subs c).length ≤ subs.flatten.length ∧
      ∀ x ∈ subOf cs subs c, x ∈ subs.flatten := by
  have hm : subOf cs subs c ∈ subs := by
    have e := subOf_map cs subs hnd hl
    have := List.mem_map_of_mem (f := subOf cs subs) hc
    rwa [e] at this
  refine ⟨?_, fun x hx => List.mem_flatten.2 ⟨_, hm, hx⟩⟩
  exact len_le_flatten _ _ hm

theorem nodeU_csNodup (W : WView) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (l : Loc) (r : NRec)
    (h : nodeU W bl B bnd kd l r) : r.cs.Nodup := by
  cases hl : r.nv.isLeaf'
  · exact (h.2.2.2.2.2.2.2.2.2 hl).2.2.1
  · rw [h.2.2.2.2.2.2.2.2.1 hl]; exact List.nodup_nil

theorem node.spill.wp_sub
    (hSort : sort.Sort.nodes_spec (GF := GF) (hG := hG))
    (hSplit : node.split.xspec (GF := GF) (hG := hG))
    (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.wspec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hAlloc : Tx.allocate.xspec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hPgid : Meta.Pgid.spec (GF := GF) (hG := hG))
    (hWrite : node.write.xspec (GF := GF) (hG := hG))
    (hKey : Inode.Key.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hAssert : Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG)) :
    node.spill.subSpec (GF := GF) (hG := hG) := by
  have htop := node.spill.wp_top hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
    hAssert hInc
  intro N
  induction N with
  | zero => exact subSpecB_zero
  | succ N ih =>
    intro I γd γ W txl txid T ρ F K bl B bnd kd S n r pl rp ht hf hg hB hHt hlen hsu hn hpar hpl hrp
      hin hplS hKp hLp hpg hbr hthr hps hel hne hP1 hP2 hP3 htr
    obtain ⟨hkt, hall⟩ := hsu
    obtain ⟨subs, hf2, hS, hnd⟩ := kidsTree_split B.ns n r S hkt hn
    have hnS : n ∈ S := by rw [hS]; exact List.mem_cons_self ..
    obtain ⟨hKn, rn, hrn, hU⟩ := hall n hnS
    rw [hn] at hrn; cases hrn
    have hcnd := nodeU_csNodup W bl B bnd kd n r hU
    have hl2 : r.cs.length = subs.length := List.Forall₂.length_eq hf2
    have hmap := subOf_map r.cs subs hcnd hl2
    have hS' : S = n :: (r.cs.map (subOf r.cs subs)).flatten := by rw [hmap]; exact hS
    have Hc := node.spill.wp_core hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
      hAssert hInc N false (fun _ => ih) (fun _ => htop) (fun h => absurd h (by decide))
      I γd γ W txl txid T ρ F K bl B bnd kd ht n r (fun _ => false) (subOf r.cs subs)
      hf hg hB (fun _ => hHt) (fun h => (hHt n r hn hU.2.1).1 h) (fun h => ((hHt n r hn hU.2.1).2 h).1)
      hn hKn (nodeL_of_nodeU W bl B bnd kd n r hU)
      (fun c hc => by
        have hk := forall2_mem r.cs subs hf2 hcnd c hc
        obtain ⟨hlt, hsub⟩ := sub_len_lt r.cs subs c hc hcnd hl2
        refine ⟨hk, fun h => absurd h (by decide), fun _ => ⟨?_, hk, fun x hx => ?_⟩⟩
        · have : S.length = (n :: subs.flatten).length := by rw [hS]
          simp only [List.length_cons] at this hlt; omega
        · exact hall x (by rw [hS]; exact List.mem_cons_of_mem _ (hsub x hx)))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (by rw [← hS']; exact hkt)
      hthr hps hel hne (fun l r h _ => hP1 l r h) (fun _ => hP1 n r hn) hP2 hP3 (fun _ => htr)
      (fun h => absurd (hpar.symm.trans h) hpl)
      (fun pl' rp' h1 _ h3 => by
        rw [← h1, hpar, hrp] at h3; cases h3
        rw [← h1, hpar, ← hS']
        exact ⟨hplS, hKp, hLp, hpg, hbr⟩)
      (fun pl' rp' h1 _ h3 => by
        rw [← h1, hpar, hrp] at h3; cases h3; exact hin)
      (fun _ => by rw [hpar, hrp]; rfl)
    rw [hS']
    iintro %Φ ⟨#Hpkg, HR, HS⟩ HΦ
    icases BigSepL.bigSepL_cons.1 $$ HS with ⟨⟨%rn, %hrn, Hrn⟩, HS⟩
    rw [hn] at hrn; cases hrn
    iapply Hc $$ [Hpkg HR Hrn HS]
    · isplitl []
      · iexact Hpkg
      iframe
      iapply (bigSepL_flat_sub r.cs (subOf r.cs subs) _).1
      iexact HS
    inext
    iintro %err Hpost
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hpar]; exact hpl))]
    icases Hpost with ⟨%rp', %hrp', Hpost⟩
    rw [hpar, hrp] at hrp'; cases hrp'
    rw [hpar]
    iapply HΦ
    iexact Hpost

theorem node.spill.wp_proof
    (hSort : sort.Sort.nodes_spec (GF := GF) (hG := hG))
    (hSplit : node.split.xspec (GF := GF) (hG := hG))
    (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.wspec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hAlloc : Tx.allocate.xspec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hPgid : Meta.Pgid.spec (GF := GF) (hG := hG))
    (hWrite : node.write.xspec (GF := GF) (hG := hG))
    (hKey : Inode.Key.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hAssert : Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG)) :
    node.spill.spec (GF := GF) (hG := hG) := by
  have htop := node.spill.wp_top hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
    hAssert hInc
  have hsubs := node.spill.wp_sub hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
    hAssert hInc
  intro I γd γ W txl txid T ρ F K bl B bnd kd ht S hf hg hB hrn hpar0 hbnd hsu hHt hdom hthr hps hel hne
    hP1 hP2 hP3 htr
  obtain ⟨hkt, hall⟩ := hsu
  obtain ⟨r, hr⟩ : ∃ r, B.ns !! B.bv.rootNode' = some r :=
    Option.isSome_iff_exists.1 ((hdom _).2 (by
      exact kidsTree_head B.ns _ S hkt))
  have hpar := hpar0 r hr
  obtain ⟨subs, hf2, hS, hnd⟩ := kidsTree_split B.ns _ r S hkt hr
  have hnS : B.bv.rootNode' ∈ S := by rw [hS]; exact List.mem_cons_self ..
  obtain ⟨hKn, rn, hrn, hU⟩ := hall _ hnS
  rw [hr] at hrn; cases hrn
  have hcnd := nodeU_csNodup W bl B bnd kd _ r hU
  have hl2 : r.cs.length = subs.length := List.Forall₂.length_eq hf2
  have hmap := subOf_map r.cs subs hcnd hl2
  have hS' : S = B.bv.rootNode' :: (r.cs.map (subOf r.cs subs)).flatten := by rw [hmap]; exact hS
  have Hc := node.spill.wp_core hSort hSplit hTxid hPage hSize hAlloc hId hPgid hWrite hKey hPut
    hAssert hInc S.length false (fun _ => hsubs S.length) (fun _ => htop) (fun h => absurd h (by decide))
    I γd γ W txl txid T ρ F K bl B bnd kd ht _ r (fun _ => false) (subOf r.cs subs)
    hf hg hB (fun _ => hHt) (fun h => (hHt _ r hr hU.2.1).1 h) (fun h => ((hHt _ r hr hU.2.1).2 h).1)
    hr hKn (nodeL_of_nodeU W bl B bnd kd _ r hU)
    (fun c hc => by
      have hk := forall2_mem r.cs subs hf2 hcnd c hc
      obtain ⟨hlt, hsub⟩ := sub_len_lt r.cs subs c hc hcnd hl2
      refine ⟨hk, fun h => absurd h (by decide), fun _ => ⟨?_, hk, fun x hx => ?_⟩⟩
      · rw [hS]; simp only [List.length_cons]; omega
      · exact hall x (by rw [hS]; exact List.mem_cons_of_mem _ (hsub x hx)))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (by rw [← hS']; exact hkt)
    hthr hps hel hne (fun l r h _ => hP1 l r h) (fun _ => hP1 _ r hr) hP2
    (fun l r w h1 h2 h3 => spillPages_of_view W T _ (hP3 l r w h1 h2 h3)) (fun _ => htr)
    (fun _ => ⟨hbnd, [B.bv.rootNode'], upPath.self _ r hr hpar, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun l hl => by
        have := (hdom l).1 hl
        rw [hS'] at this
        rcases List.mem_cons.1 this with h | h
        · exact Or.inl (by rw [h]; exact List.mem_singleton_self _)
        · exact Or.inr h⟩)
    (fun pl rp h1 h2 _ => absurd (h1.symm.trans hpar) h2)
    (fun pl rp h1 h2 _ => absurd (h1.symm.trans hpar) h2)
    (fun h => absurd hpar h)
  rw [hS']
  iintro %Φ ⟨#Hpkg, HR, HS⟩ HΦ
  icases BigSepL.bigSepL_cons.1 $$ HS with ⟨⟨%rn, %hrn, Hrn⟩, HS⟩
  rw [hr] at hrn; cases hrn
  iapply Hc $$ [Hpkg HR Hrn HS]
  · isplitl []
    · iexact Hpkg
    iframe
    iapply (bigSepL_flat_sub r.cs (subOf r.cs subs) _).1
    iexact HS
  inext
  iintro %err Hpost
  rw [ite_eq_left_of_eq_true _ _ (eq_true hpar)]
  iapply HΦ
  unfold finPost
  iexact Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
