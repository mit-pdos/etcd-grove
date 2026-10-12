module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__iterate
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__find
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

set_option maxHeartbeats 10000000 in
theorem node.iterate.wp_proof (wp_find : items.find.spec (GF := GF) (hG := hG)) :
    node.iterate.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less dq n t dir start stop ks ku includeStart hit iter r acc I d h
  induction h using Nat.strongRecOn generalizing n t hit acc with
  | _ h IH =>
  intro hshape hsorted hdir hinc hhit seg hseg
  obtain ⟨is, cs⟩ := t
  have hok := shapeOk_of_shape hshape
  have hs : Sorted o.lt (Tree.elemsAux is cs) := by simpa using hsorted
  have hsegdef : seg = (if dir = W64 1 then ascRange o.lt (Tree.node is cs).elems ks ku
      else descRange o.lt (Tree.node is cs).elems ks ku) := rfl
  clear_value seg
  subst hsegdef
  simp only [Tree.elems_node] at hseg ⊢
  wp_start as ⟨#Hcow, Hn, #Hitems, #Hks, #Hku, #Hiter, HI⟩
  icases ownNode_read o c f less dq n is cs $$ [Hn] with
    ⟨%dq', %isl, %csl, %cow, %ps, Hnf, #Hcow', Hisl, Hcsl, Hch, Hclose⟩
  · iframe Hn Hcow
  unfold nodeFields
  icases Hnf with ⟨Hnn, Hfi, Hfc, Hfw⟩
  ihave #Hless := isCow_less o f less cow $$ Hcow'
  ihave #HisLess := isCow_isLess o f less cow $$ Hcow'
  ihave %Hlenc := ownSlice_len _ _ _ $$ Hcsl
  ihave %Hlenps := ownNodes_length o c f less dq ps cs $$ Hch
  ihave %Hleni := ownSlice_len _ _ _ $$ Hisl
  simp only [List.length_map] at Hleni
  wp_auto
  ihave %Hksv := optKey_valid o start ks $$ Hks
  ihave %Hkuv := optKey_valid o stop ku $$ Hku
  have hsi : Sorted o.lt is := Sorted.sublist (items_sublist_elemsAux is cs) hs
  ihave #HitemsIs := allItems_mono o (l1 := is) (l2 := Tree.elemsAux is cs)
    (fun e he => (items_sublist_elemsAux is cs).subset he) $$ Hitems
  wp_if_destruct
  · -- ascend
    simp only [ite_eq_left] at hseg ⊢
    wp_join iprop(∃ idx : w64, index_ptr ↦ idx ∗
        ⌜sint.nat idx = ascStart o.lt is ks ∧ 0 ≤ sint.Z idx⌝ ∗
        isl ↦*{dq'} is.map Prod.fst ∗ n_ptr ↦ n ∗
        n.[node V, go!"items"] ↦{dq'} isl ∗ n.[node V, go!"cow"] ↦{dq'} cow ∗ start_ptr ↦ start)
      at next with [index Hisl n Hfi Hfw start] as ⟨%idx, index, %Hidx, Hisl, n, Hfi, Hfw, start⟩
    · cases hv : start.valid'
      · wp_auto
        have hks : ks = none := Hksv.2 hv
        subst hks
        isplitr
        · ipureintro; rfl
        iexists W64 0
        iframe
        ipureintro; simp [ascStart]
      · wp_auto
        obtain ⟨a, rfl⟩ := Hksv.1 hv
        ihave #Ha := optKey_some o start a $$ Hks
        wp_apply wp_find o isl is dq' start.item' a less hsi $$ [Hisl] as %idx %found ⟨Hisl, %Hres⟩
        · iframe # ∗
        isplitr
        · ipureintro; rfl
        iexists idx
        iframe
        ipureintro; exact ⟨Hres.1, Hres.2.1⟩
    ihave HInv : (∃ (i : w64) (hitv okv : Bool),
        "i" ∷ i_ptr ↦ i ∗ "hit" ∷ hit_ptr ↦ hitv ∗ "ok" ∷ ok_ptr ↦ okv ∗
        "HI" ∷ I (acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku) false ∗
        "%Hi" ∷ ⌜ascStart o.lt is ks ≤ sint.nat i ∧ sint.nat i ≤ is.length ∧ 0 ≤ sint.Z i⌝ :
        IProp GF) $$ [i hit ok HI]
    · iexists idx, hit, false
      rw [Hidx.1, asc_pre_start o.order hok hs ks ku, List.append_nil]
      iframe
      ipureintro
      exact ⟨Nat.le_refl _, ascStart_le ks, Hidx.2⟩
    wp_for HInv
    have hiN := Hi.2.1
    wp_if_destruct
    · -- an iteration: child `i`, then item `i`
      have hiN' : sint.nat i < is.length := by word
      wp_if_destruct
      focus
        -- an internal node: iterate over child `i`
        have hcs : cs ≠ [] := by
          intro hc; rw [hc] at Hlenps
          have h0 : ps.length = 0 := by simpa using Hlenps
          word
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
          cases h with
          | zero => exact absurd (by simpa [Tree.Shape] using hshape) hcs
          | succ h' => exact ⟨h', rfl⟩
        have hcl : cs.length = is.length + 1 := hshape.1
        list_elem ps (sint.nat i) as p
        list_elem cs (sint.nat i) as ch
        have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z csl.len := by word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index csl (sint.Z i) ps dq' p Hi.2.2 $$ [Hcsl] as Hcsl
        · iframe; ipureintro; exact Hp_lookup
        icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
          with ⟨Hc, Hch⟩
        have hchs : ch.Shape d h' := (hshape.2 ch (List.mem_of_getElem? Hch_lookup)).2
        have hdec := elems_decomp (sint.nat i) is cs hok (by omega)
        have hsub : ch.elems.Sublist (Tree.elemsAux is cs) := by
          rw [hdec, chElems_eq Hch_lookup]
          exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
        ihave #HitemsC := allItems_mono o (l1 := ch.elems) (l2 := Tree.elemsAux is cs)
          (fun e he => hsub.subset he) $$ Hitems
        have hpre' : acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku ++
            (if W64 1 = W64 1 then ascRange o.lt ch.elems ks ku
              else descRange o.lt ch.elems ks ku) <+: r := by
          rw [ite_eq_left rfl]
          refine List.IsPrefix.trans ?_ hseg
          rw [asc_decomp hok hs ks ku (sint.nat i) (by omega), chElems_eq Hch_lookup]
          exact ⟨ascRange o.lt (sufElems is cs (sint.nat i)) ks ku, by simp⟩
        wp_apply (IH h' (by omega) p ch hitv _ hchs (Sorted.sublist hsub hs) (Or.inl rfl) hinc
          (fun h => absurd h (by decide)) hpre') $$ [Hc HI] as %hitv %okv ⟨Hc, Hpost⟩
        · iframe # ∗
        cases okv
        · -- the child stopped
          wp_auto
          wp_for_post
          icases Hpost with (⟨%Hok, _⟩ | ⟨_, Hst⟩)
          · exact absurd Hok.1 (by simp)
          iapply HΦ
          isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch Hc]
          · iapply Hclose; iframe
            iapply (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2; iframe
          iright
          isplitr
          · ipureintro; rfl
          have hdec' := asc_decomp hok hs ks ku (sint.nat i) (by omega)
          rw [chElems_eq Hch_lookup] at hdec'
          icases Hst with (⟨%pre, %Hpre, HI⟩ | ⟨HI, %Hstop⟩)
          · ileft; iexists pre; iframe; ipureintro
            refine ⟨(List.prefix_append _ _).trans Hpre.1, Hpre.2.trans ?_⟩
            rw [hdec']
            exact ⟨ascRange o.lt (sufElems is cs (sint.nat i)) ks ku, by simp⟩
          · iright
            obtain ⟨b, hb, e, he1, he2⟩ := Hstop
            have hsufnil : ascRange o.lt (sufElems is cs (sint.nat i)) ks ku = [] :=
              asc_nil_above o.order ks ku b hb e he2 _ (fun e' he' h' => o.order.irrefl _
                (o.order.trans _ _ _ (lt_pre_ch_suf o.order hok hs _ (by omega) e
                  (by simp [chElems_eq Hch_lookup, he1]) e' he') h'))
            rw [hdec', hsufnil, List.append_nil]
            isplitl [HI]
            · iExactEq HI; simp
            ipureintro; exact ⟨b, hb, e, hsub.subset he1, he2⟩
        -- go on
        wp_auto
        icases Hpost with (⟨%Hok, HI⟩ | ⟨%Hok, _⟩)
        rotate_left
        · exact absurd Hok (by simp)
        icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2 $$ [Hc Hch]
          with Hch
        · iframe
        rw [← chElems_eq Hch_lookup]
      rotate_left
      focus
        -- a leaf
        have hcs : cs = [] := by
          cases cs with
          | nil => rfl
          | cons _ _ =>
            have h0 : 0 < ps.length := by simp [Hlenps]
            word
        rw [show acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku =
            acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku ++
              ascRange o.lt (chElems cs (sint.nat i)) ks ku by
          rw [hcs, chElems_of_nil]; simp [ascRange]]
      all_goals
        -- item `i`
        list_elem is (sint.nat i) as x
        have hxi : is[sint.nat i] = x := (List.getElem?_eq_some_iff.1 Hx_lookup).2
        have hxmem : x ∈ is := List.mem_of_getElem? Hx_lookup
        ihave #Hx := allItems_elem o hxmem $$ HitemsIs
        -- the skip check never skips (it is only for `includeStart = false`, which comes
        -- with no `start`)
        wp_join at next with [includeStart hit start]
        · cases hI : includeStart
          · have hv : start.valid' = false := by
              cases h' : start.valid'
              · rfl
              · exact absurd (hinc h') (by simp [hI])
            cases hitv
            · wp_auto
              rw [hv]
              wp_auto
              wp_join_done
            · wp_auto
              wp_join_done
          · wp_auto
            wp_join_done
        -- the stop check
        have hbx : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z isl.len := by word
        wp_join (v := #(@decide (∃ b, ku = some b ∧ ¬ o.lt x.2 b) (Classical.propDecidable _)))
          at (If (Val #(stop.valid')) _ _) with [Hisl Hfi Hfw n i stop]
        · cases hsv : stop.valid'
          · have hku : ku = none := Hkuv.2 hsv
            wp_auto
            isplitr
            · ipureintro; simp [hku]
            iframe
          · obtain ⟨b, rfl⟩ := Hkuv.1 hsv
            ihave #Hb := optKey_some o stop b $$ Hku
            wp_auto
            simp only [hbx, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 Hi.2.2 $$ [Hisl]
              as Hisl
            · iframe; ipureintro
              rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_map, Hx_lookup]; rfl
            unfold isLess
            wp_apply HisLess $$ %x.1 %stop.item' %x.2 %b as %rr %Hrr
            · iframe # ∗
            isplitr
            · ipureintro
              cases rr <;> simp_all
            iframe
        rcases Classical.em (∃ b, ku = some b ∧ ¬ o.lt x.2 b) with Hif | Hif
        · -- `stop` reached: the range is done
          rw [@_root_.decide_eq_true _ (Classical.propDecidable _) Hif]
          wp_auto
          obtain ⟨b, hb, hxb⟩ := Hif
          wp_for_post
          iapply HΦ
          isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
          · iapply Hclose; iframe
          iright
          isplitr
          · ipureintro; rfl
          iright
          have hsufnil : ascRange o.lt (sufElems is cs (sint.nat i)) ks ku = [] := by
            apply asc_nil_above o.order ks ku b hb x hxb
            rw [sufElems_succ is cs _ hok hiN', hxi]
            intro e he h'
            rcases List.mem_cons.1 he with rfl | he
            · exact o.order.irrefl _ h'
            · have := item_lt o.order hok hs _ hiN' e he
              rw [hxi] at this
              exact o.order.irrefl _ (o.order.trans _ _ _ h' this)
          rw [asc_decomp hok hs ks ku (sint.nat i) (by omega), hsufnil, List.append_nil]
          isplitl [HI]
          · iExactEq HI; simp
          ipureintro; exact ⟨b, hb, x, (items_sublist_elemsAux is cs).subset hxmem, hxb⟩
        · -- visit item `i`
          have hstop : ∀ b, ku = some b → o.lt is[sint.nat i].2 b := fun b hb => by
            rw [hxi]
            exact Classical.byContradiction fun h' => Hif ⟨b, hb, h'⟩
          have hin : ascIn o.lt ks ku x.2 := hxi ▸ ascIn_item o.order hs ks ku _ Hi.1 hiN' hstop
          rw [@_root_.decide_eq_false _ (Classical.propDecidable _) Hif]
          wp_auto
          simp only [hbx, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 Hi.2.2 $$ [Hisl]
            as Hisl
          · iframe; ipureintro
            rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_map, Hx_lookup]; rfl
          have hpre_succ := asc_pre_succ (lt := o.lt) hok ks ku (sint.nat i) hiN'
          rw [hxi, ite_eq_left hin] at hpre_succ
          have hpref : acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku ++
              ascRange o.lt (chElems cs (sint.nat i)) ks ku ++ [x] <+:
              acc ++ ascRange o.lt (Tree.elemsAux is cs) ks ku := by
            rw [asc_decomp hok hs ks ku (sint.nat i + 1) (by omega), hpre_succ]
            exact ⟨ascRange o.lt (chElems cs (sint.nat i + 1)) ks ku ++
              ascRange o.lt (sufElems is cs (sint.nat i + 1)) ks ku, by simp⟩
          unfold iterProtocol
          wp_apply Hiter $$ %(acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku ++
              ascRange o.lt (chElems cs (sint.nat i)) ks ku) %x %(hpref.trans hseg) [HI] as %bv HI
          · iframe # ∗
          cases bv
          · -- the callback stops
            wp_auto
            wp_for_post
            iapply HΦ
            isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
            · iapply Hclose; iframe
            iright
            isplitr
            · ipureintro; rfl
            ileft
            simp only [Bool.not_false]
            iexists (acc ++ ascRange o.lt (preElems is cs (sint.nat i)) ks ku ++
              ascRange o.lt (chElems cs (sint.nat i)) ks ku ++ [x])
            iframe
            ipureintro
            refine ⟨?_, hpref⟩
            rw [List.append_assoc, List.append_assoc]; exact List.prefix_append _ _
          · -- next item
            wp_auto
            wp_for_post
            simp only [Bool.not_true]
            have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            iframe
            iexists (i + W64 1), true, _
            rw [hi1, hpre_succ]
            iframe
            isplitl [HI]
            · iExactEq HI; simp
            ipureintro
            refine ⟨by omega, by omega, by word⟩
    · -- the end: the last child
      have hiN' : sint.nat i = is.length := by word
      have hsegN : ascRange o.lt (Tree.elemsAux is cs) ks ku =
          ascRange o.lt (preElems is cs is.length) ks ku ++
            ascRange o.lt (chElems cs is.length) ks ku := by
        rw [asc_decomp hok hs ks ku is.length (Nat.le_refl _), sufElems_length]
        simp [ascRange]
      rw [hiN']
      wp_if_destruct
      · -- an internal node: the last child
        have hcs : cs ≠ [] := by
          intro hc; rw [hc] at Hlenps
          have h0 : ps.length = 0 := by simpa using Hlenps
          word
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
          cases h with
          | zero => exact absurd (by simpa [Tree.Shape] using hshape) hcs
          | succ h' => exact ⟨h', rfl⟩
        have hcl : cs.length = is.length + 1 := hshape.1
        list_elem ps is.length as p
        list_elem cs is.length as ch
        have hb : 0 ≤ sint.Z (csl.len - W64 1) ∧ sint.Z (csl.len - W64 1) < sint.Z csl.len := by
          word
        simp only [hb, _root_.and_self, ↓reduceIte]
        have hidx' : (sint.Z (csl.len - W64 1)).toNat = is.length := by word
        wp_apply wp_load_slice_index csl (sint.Z (csl.len - W64 1)) ps dq' p hb.1 $$ [Hcsl]
          as Hcsl
        · iframe; ipureintro; rw [hidx']; exact Hp_lookup
        icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
          with ⟨Hc, Hch⟩
        have hchs : ch.Shape d h' := (hshape.2 ch (List.mem_of_getElem? Hch_lookup)).2
        have hdec := elems_decomp is.length is cs hok (Nat.le_refl _)
        have hsub : ch.elems.Sublist (Tree.elemsAux is cs) := by
          rw [hdec, chElems_eq Hch_lookup]
          exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
        ihave #HitemsC := allItems_mono o (l1 := ch.elems) (l2 := Tree.elemsAux is cs)
          (fun e he => hsub.subset he) $$ Hitems
        rw [chElems_eq Hch_lookup] at hsegN
        have hpre' : acc ++ ascRange o.lt (preElems is cs is.length) ks ku ++
            (if W64 1 = W64 1 then ascRange o.lt ch.elems ks ku
              else descRange o.lt ch.elems ks ku) <+: r := by
          rw [ite_eq_left rfl]
          refine List.IsPrefix.trans ?_ hseg
          rw [hsegN, List.append_assoc]
          exact List.prefix_refl _
        wp_apply (IH h' (by omega) p ch hitv _ hchs (Sorted.sublist hsub hs) (Or.inl rfl) hinc
          (fun h => absurd h (by decide)) hpre') $$ [Hc HI] as %hitv %okv ⟨Hc, Hpost⟩
        · iframe # ∗
        ihave Hn := Hclose $$ [Hnn Hfi Hfc Hfw Hisl Hcsl Hch Hc]
        · iframe
          iapply (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2; iframe
        cases okv
        · -- the child stopped
          wp_auto
          iapply HΦ
          iframe Hn
          iright
          isplitr
          · ipureintro; rfl
          icases Hpost with (⟨%Hok, _⟩ | ⟨_, (⟨%pre, %Hpre, HI⟩ | ⟨HI, %Hstop⟩)⟩)
          · exact absurd Hok.1 (by simp)
          · ileft; iexists pre; iframe; ipureintro
            refine ⟨(List.prefix_append _ _).trans Hpre.1, ?_⟩
            rw [hsegN, ← List.append_assoc]; exact Hpre.2
          · iright
            obtain ⟨b, hb, e, he1, he2⟩ := Hstop
            rw [hsegN]
            isplitl [HI]
            · iExactEq HI; simp
            ipureintro; exact ⟨b, hb, e, hsub.subset he1, he2⟩
        -- the child went to its end
        wp_auto
        icases Hpost with (⟨%Hok, HI⟩ | ⟨%Hok, _⟩)
        rotate_left
        · exact absurd Hok (by simp)
        iapply HΦ
        iframe Hn
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, fun h => absurd h (by decide)⟩
        rw [hsegN]
        iExactEq HI; simp
      · -- a leaf
        have hcs : cs = [] := by
          cases cs with
          | nil => rfl
          | cons _ _ =>
            have h0 : 0 < ps.length := by simp [Hlenps]
            word
        rw [show chElems cs is.length = [] by rw [hcs, chElems_of_nil]] at hsegN
        iapply HΦ
        isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
        · iapply Hclose; iframe
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, fun h => absurd h (by decide)⟩
        rw [hsegN]
        iExactEq HI; simp [ascRange]
  · wp_if_destruct
    · -- descend
      have hne : ¬ (W64 (-1) = W64 1) := by decide
      simp only [ite_eq_right hne] at hseg ⊢
      have hhit' := hhit rfl
      wp_join iprop(∃ idx : w64, index_ptr ↦ idx ∗
          ⌜sint.Z idx + 1 = (descStart o.lt is ks : Int) ∧ -1 ≤ sint.Z idx⌝ ∗
          (∃ fv : Bool, found_ptr ↦ fv) ∗
          isl ↦*{dq'} is.map Prod.fst ∗ n_ptr ↦ n ∗
          n.[node V, go!"items"] ↦{dq'} isl ∗ n.[node V, go!"cow"] ↦{dq'} cow ∗ start_ptr ↦ start)
        at next with [index found Hisl n Hfi Hfw start]
        as ⟨%idx, index, %Hidx, ⟨%fv, found⟩, Hisl, n, Hfi, Hfw, start⟩
      · cases hv : start.valid'
        · wp_auto
          have hks : ks = none := Hksv.2 hv
          subst hks
          isplitr
          · ipureintro; rfl
          iexists (isl.len - W64 1)
          iframe
          ipureintro
          simp only [descStart]
          constructor <;> word
        · wp_auto
          obtain ⟨a, rfl⟩ := Hksv.1 hv
          ihave #Ha := optKey_some o start a $$ Hks
          wp_apply wp_find o isl is dq' start.item' a less hsi $$ [Hisl]
            as %idx %fnd ⟨Hisl, %Hres⟩
          · iframe # ∗
          obtain ⟨Hres1, Hres2, Hres3⟩ := Hres
          have hcl := countLt_le (lt := o.lt) is a
          cases fnd
          · wp_auto
            isplitr
            · ipureintro; rfl
            iexists (idx - W64 1)
            iframe
            ipureintro
            have hnf : ¬ ∃ e, is[countLt o.lt is a]? = some e ∧ e.2 = a := by
              rw [← Hres1]; intro hh; exact absurd (Hres3.2 hh) (by simp)
            simp only [descStart, hnf, ↓reduceIte]
            constructor <;> word
          · wp_auto
            isplitr
            · ipureintro; rfl
            iexists idx
            iframe
            ipureintro
            have hf : ∃ e, is[countLt o.lt is a]? = some e ∧ e.2 = a := by
              rw [← Hres1]; exact Hres3.1 rfl
            simp only [descStart, hf, ↓reduceIte]
            constructor <;> word
      have hdsl := descStart_le (lt := o.lt) (is := is) ks
      ihave HInv : (∃ (i : w64) (j : Nat) (hitv okv : Bool),
          "i" ∷ i_ptr ↦ i ∗ "hit" ∷ hit_ptr ↦ hitv ∗ "ok" ∷ ok_ptr ↦ okv ∗
          "HI" ∷ I (acc ++ descRange o.lt (sufElems is cs j) ks ku) false ∗
          "%Hi" ∷ ⌜sint.Z i = (j : Int) - 1 ∧ j ≤ descStart o.lt is ks ∧
            hitv = (hit || !(descRange o.lt (sufElems is cs j) ks ku).isEmpty)⌝ :
          IProp GF) $$ [i hit ok HI]
      · iexists idx, descStart o.lt is ks, hit, false
        rw [desc_suf_start o.order hok hs ks ku, List.append_nil]
        iframe
        ipureintro
        refine ⟨by omega, Nat.le_refl _, by simp⟩
      wp_for HInv
      obtain ⟨Hij, Hjs, Hhv⟩ := Hi
      wp_if_destruct
      · -- an iteration: item `j - 1`, after child `j`
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
          cases j with
          | zero => exfalso; simp at Hij; word
          | succ j' => exact ⟨j', rfl⟩
        have hjN : j' < is.length := by omega
        have hinat : sint.nat i = j' := by word
        list_elem is j' as x
        have hxi : is[j'] = x := (List.getElem?_eq_some_iff.1 Hx_lookup).2
        have hxmem : x ∈ is := List.mem_of_getElem? Hx_lookup
        ihave #Hx := allItems_elem o hxmem $$ HitemsIs
        have hbx : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z isl.len := by word
        have hHit : hitv = true → ∀ a, ks = some a →
            ∀ e ∈ preElems is cs (j' + 1) ++ chElems cs (j' + 1), o.lt e.2 a := by
          intro hh a ha
          subst ha
          exact desc_hit_lt o.order hok hs a ku hit (j' + 1) (by omega)
            (fun h1 => hhit' h1 a rfl) (Hhv ▸ hh)
        have hxpre : x ∈ preElems is cs (j' + 1) ++ chElems cs (j' + 1) := by
          rw [preElems_succ is cs j' hok hjN, hxi]; simp
        -- the start check never skips: the item at `start` is only skipped once an entry
        -- was visited, and then none ahead of it has `start`'s key
        wp_join at next with [start includeStart hit Hisl Hfi Hfw n i]
        · cases hv : start.valid'
          · wp_auto
            wp_join_done
          · obtain ⟨a, rfl⟩ := Hksv.1 hv
            ihave #Ha := optKey_some o start a $$ Hks
            obtain rfl : includeStart = true := hinc hv
            wp_auto
            simp only [hbx, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 hbx.1
              $$ [Hisl] as Hisl
            · iframe; ipureintro
              rw [show (sint.Z i).toNat = j' by word, List.getElem?_map, Hx_lookup]; rfl
            unfold isLess
            wp_apply HisLess $$ %x.1 %start.item' %x.2 %a as %r1 %Hr1
            · iframe # ∗
            cases r1
            · -- `x` is not below `start`: it is `start`
              have hxa : ¬ o.lt a x.2 := hxi ▸ item_le_descStart o.order hs a j' (by omega) hjN
              have hnlt : ¬ o.lt x.2 a := fun h' => absurd (Hr1.2 h') (by simp)
              cases hitv
              · wp_auto
                simp only [hbx, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 hbx.1
                  $$ [Hisl] as Hisl
                · iframe; ipureintro
                  rw [show (sint.Z i).toNat = j' by word, List.getElem?_map, Hx_lookup]; rfl
                wp_apply HisLess $$ %start.item' %x.1 %a %x.2 as %r2 %Hr2
                · iframe # ∗
                cases r2
                · wp_auto
                  wp_join_done
                · exact absurd (Hr2.1 rfl) hxa
              · exact absurd (hHit rfl a rfl x hxpre) hnlt
            · wp_auto
              wp_join_done
        -- child `j' + 1`
        have hhvj : hitv = (hit || !(descRange o.lt (sufElems is cs (j' + 1)) ks ku).isEmpty) := Hhv
        clear Hhv
        wp_if_destruct
        focus
          -- an internal node: iterate over child `j' + 1`
          have hcs : cs ≠ [] := by
            intro hc; rw [hc] at Hlenps
            have h0 : ps.length = 0 := by simpa using Hlenps
            word
          obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
            cases h with
            | zero => exact absurd (by simpa [Tree.Shape] using hshape) hcs
            | succ h' => exact ⟨h', rfl⟩
          have hcl : cs.length = is.length + 1 := hshape.1
          list_elem ps (j' + 1) as p
          list_elem cs (j' + 1) as ch
          have hb : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) < sint.Z csl.len := by word
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index csl (sint.Z (i + W64 1)) ps dq' p hb.1 $$ [Hcsl] as Hcsl
          · iframe; ipureintro
            rw [show (sint.Z (i + W64 1)).toNat = j' + 1 by word]; exact Hp_lookup
          icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
            with ⟨Hc, Hch⟩
          have hchs : ch.Shape d h' := (hshape.2 ch (List.mem_of_getElem? Hch_lookup)).2
          have hdec := elems_decomp (j' + 1) is cs hok (by omega)
          have hsub : ch.elems.Sublist (Tree.elemsAux is cs) := by
            rw [hdec, chElems_eq Hch_lookup]
            exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
          ihave #HitemsC := allItems_mono o (l1 := ch.elems) (l2 := Tree.elemsAux is cs)
            (fun e he => hsub.subset he) $$ Hitems
          have hdd := desc_decomp hok hs ks ku (j' + 1) (by omega)
          rw [chElems_eq Hch_lookup] at hdd
          have hpre' : acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
              (if W64 (-1) = W64 1 then ascRange o.lt ch.elems ks ku
                else descRange o.lt ch.elems ks ku) <+: r := by
            rw [ite_eq_right hne]
            refine List.IsPrefix.trans ?_ hseg
            rw [hdd]
            exact ⟨descRange o.lt (preElems is cs (j' + 1)) ks ku, by simp⟩
          have hchit : W64 (-1) = W64 (-1) → hitv = true → ∀ a, ks = some a →
              ∀ e ∈ ch.elems, o.lt e.2 a := by
            intro _ hh a ha e he
            exact hHit hh a ha e (by rw [chElems_eq Hch_lookup]; simp [he])
          wp_apply (IH h' (by omega) p ch hitv _ hchs (Sorted.sublist hsub hs) (Or.inr rfl) hinc
            hchit hpre') $$ [Hc HI] as %hitv %okv ⟨Hc, Hpost⟩
          · iframe # ∗
          cases okv
          · -- the child stopped
            wp_auto
            wp_for_post
            icases Hpost with (⟨%Hok, _⟩ | ⟨_, Hst⟩)
            · exact absurd Hok.1 (by simp)
            iapply HΦ
            isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch Hc]
            · iapply Hclose; iframe
              iapply (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2; iframe
            iright
            isplitr
            · ipureintro; rfl
            icases Hst with (⟨%pre, %Hpre, HI⟩ | ⟨HI, %Hstop⟩)
            · ileft; iexists pre; iframe; ipureintro
              refine ⟨(List.prefix_append _ _).trans Hpre.1, Hpre.2.trans ?_⟩
              rw [hdd]
              exact ⟨descRange o.lt (preElems is cs (j' + 1)) ks ku, by simp⟩
            · iright
              obtain ⟨b, hb, e, he1, he2⟩ := Hstop
              have hprenil : descRange o.lt (preElems is cs (j' + 1)) ks ku = [] :=
                desc_nil_below o.order ks ku b hb e he2 _ (fun e' he' h' => o.order.irrefl _
                  (o.order.trans _ _ _ (lt_pre_ch_suf' o.order hok hs _ (by omega) e' he' e
                    (by simp [chElems_eq Hch_lookup, he1])) h'))
              rw [hdd, hprenil, List.append_nil]
              isplitl [HI]
              · iExactEq HI; simp
              ipureintro; exact ⟨b, hb, e, hsub.subset he1, he2⟩
          -- go on
          wp_auto
          icases Hpost with (⟨%Hok, HI⟩ | ⟨%Hok, _⟩)
          rotate_left
          · exact absurd Hok (by simp)
          icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2 $$ [Hc Hch]
            with Hch
          · iframe
          have hhv : hitv = (hit || !(descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
              descRange o.lt (chElems cs (j' + 1)) ks ku).isEmpty) := by
            rw [Hok.2 trivial, hhvj, chElems_eq Hch_lookup, not_isEmpty_append, Bool.or_assoc]
          clear hhvj
          rw [← chElems_eq Hch_lookup]
        rotate_left
        focus
          -- a leaf
          have hcs : cs = [] := by
            cases cs with
            | nil => rfl
            | cons _ _ =>
              have h0 : 0 < ps.length := by simp [Hlenps]
              word
          have hchn : chElems cs (j' + 1) = [] := by rw [hcs, chElems_of_nil]
          rw [show acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku =
              acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
                descRange o.lt (chElems cs (j' + 1)) ks ku by
            rw [hchn]; simp [descRange]]
          have hhv : hitv = (hit || !(descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
              descRange o.lt (chElems cs (j' + 1)) ks ku).isEmpty) := by
            rw [hhvj, hchn]; simp [descRange]
          clear hhvj
        all_goals
          -- the stop check
          wp_join (v := #(@decide (∃ b, ku = some b ∧ ¬ o.lt b x.2) (Classical.propDecidable _)))
            at (If (Val #(stop.valid')) _ _) with [Hisl Hfi Hfw n i stop]
          · cases hsv : stop.valid'
            · have hku : ku = none := Hkuv.2 hsv
              wp_auto
              isplitr
              · ipureintro; simp [hku]
              iframe
            · obtain ⟨b, rfl⟩ := Hkuv.1 hsv
              ihave #Hb := optKey_some o stop b $$ Hku
              wp_auto
              simp only [hbx, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 hbx.1
                $$ [Hisl] as Hisl
              · iframe; ipureintro
                rw [show (sint.Z i).toNat = j' by word, List.getElem?_map, Hx_lookup]; rfl
              unfold isLess
              wp_apply HisLess $$ %stop.item' %x.1 %b %x.2 as %rr %Hrr
              · iframe # ∗
              isplitr
              · ipureintro
                cases rr <;> simp_all
              iframe
          have hdd := desc_decomp hok hs ks ku (j' + 1) (by omega)
          rcases Classical.em (∃ b, ku = some b ∧ ¬ o.lt b x.2) with Hif | Hif
          · -- `stop` reached: the range is done
            rw [@_root_.decide_eq_true _ (Classical.propDecidable _) Hif]
            wp_auto
            obtain ⟨b, hb, hxb⟩ := Hif
            wp_for_post
            iapply HΦ
            isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
            · iapply Hclose; iframe
            iright
            isplitr
            · ipureintro; rfl
            iright
            have hprenil : descRange o.lt (preElems is cs (j' + 1)) ks ku = [] := by
              apply desc_nil_below o.order ks ku b hb x hxb
              rw [preElems_succ is cs j' hok hjN, hxi]
              intro e he h'
              simp only [List.mem_append, List.mem_singleton] at he
              rcases he with (he | he) | rfl
              · have := lt_item o.order hok hs j' hjN e (by simp [he])
                rw [hxi] at this
                exact o.order.irrefl _ (o.order.trans _ _ _ h' this)
              · have := lt_item o.order hok hs j' hjN e (by simp [he])
                rw [hxi] at this
                exact o.order.irrefl _ (o.order.trans _ _ _ h' this)
              · exact o.order.irrefl _ h'
            rw [hdd, hprenil, List.append_nil]
            isplitl [HI]
            · iExactEq HI; simp
            ipureintro; exact ⟨b, hb, x, (items_sublist_elemsAux is cs).subset hxmem, hxb⟩
          · -- visit item `j'`
            have hstop : ∀ b, ku = some b → o.lt b is[j'].2 := fun b hb => by
              rw [hxi]
              exact Classical.byContradiction fun h' => Hif ⟨b, hb, h'⟩
            have hin : descIn o.lt ks ku x.2 :=
              hxi ▸ descIn_item o.order hs ks ku j' (by omega) hjN hstop
            rw [@_root_.decide_eq_false _ (Classical.propDecidable _) Hif]
            wp_auto
            simp only [hbx, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index isl (sint.Z i) (is.map Prod.fst) dq' x.1 hbx.1 $$ [Hisl]
              as Hisl
            · iframe; ipureintro
              rw [show (sint.Z i).toNat = j' by word, List.getElem?_map, Hx_lookup]; rfl
            have hsuf_pred := desc_suf_pred (lt := o.lt) hok ks ku j' hjN
            rw [hxi, ite_eq_left hin] at hsuf_pred
            have hpref : acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
                descRange o.lt (chElems cs (j' + 1)) ks ku ++ [x] <+:
                acc ++ descRange o.lt (Tree.elemsAux is cs) ks ku := by
              rw [desc_decomp hok hs ks ku j' (by omega), hsuf_pred]
              exact ⟨descRange o.lt (chElems cs j') ks ku ++
                descRange o.lt (preElems is cs j') ks ku, by simp⟩
            unfold iterProtocol
            wp_apply Hiter $$ %(acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
                descRange o.lt (chElems cs (j' + 1)) ks ku) %x %(hpref.trans hseg) [HI]
              as %bv HI
            · iframe # ∗
            cases bv
            · -- the callback stops
              wp_auto
              wp_for_post
              iapply HΦ
              isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
              · iapply Hclose; iframe
              iright
              isplitr
              · ipureintro; rfl
              ileft
              simp only [Bool.not_false]
              iexists (acc ++ descRange o.lt (sufElems is cs (j' + 1)) ks ku ++
                descRange o.lt (chElems cs (j' + 1)) ks ku ++ [x])
              iframe
              ipureintro
              refine ⟨?_, hpref⟩
              rw [List.append_assoc, List.append_assoc]; exact List.prefix_append _ _
            · -- next item
              wp_auto
              wp_for_post
              simp only [Bool.not_true]
              iframe
              iexists (i - W64 1), j', true, _
              rw [hsuf_pred]
              iframe
              isplitl [HI]
              · iExactEq HI; simp
              ipureintro
              refine ⟨by word, by omega, by simp⟩
      · -- the end: child 0
        have hj0 : j = 0 := by word
        subst hj0
        have hdd0 := desc_decomp hok hs ks ku 0 (Nat.zero_le _)
        rw [preElems_zero] at hdd0
        rw [show descRange o.lt ([] : List (V × K)) ks ku = [] from rfl, List.append_nil] at hdd0
        have hHit0 : hitv = true → ∀ a, ks = some a →
            ∀ e ∈ preElems is cs 0 ++ chElems cs 0, o.lt e.2 a := by
          intro hh a ha
          subst ha
          exact desc_hit_lt o.order hok hs a ku hit 0 (Nat.zero_le _)
            (fun h1 => hhit' h1 a rfl) (Hhv ▸ hh)
        wp_if_destruct
        · -- an internal node: child 0
          have hcs : cs ≠ [] := by
            intro hc; rw [hc] at Hlenps
            have h0 : ps.length = 0 := by simpa using Hlenps
            word
          obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
            cases h with
            | zero => exact absurd (by simpa [Tree.Shape] using hshape) hcs
            | succ h' => exact ⟨h', rfl⟩
          have hcl : cs.length = is.length + 1 := hshape.1
          list_elem ps 0 as p
          list_elem cs 0 as ch
          have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len := by word
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index csl (sint.Z (W64 0)) ps dq' p hb.1 $$ [Hcsl] as Hcsl
          · iframe; ipureintro; exact Hp_lookup
          icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
            with ⟨Hc, Hch⟩
          have hchs : ch.Shape d h' := (hshape.2 ch (List.mem_of_getElem? Hch_lookup)).2
          have hdec := elems_decomp 0 is cs hok (Nat.zero_le _)
          have hsub : ch.elems.Sublist (Tree.elemsAux is cs) := by
            rw [hdec, chElems_eq Hch_lookup]
            exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
          ihave #HitemsC := allItems_mono o (l1 := ch.elems) (l2 := Tree.elemsAux is cs)
            (fun e he => hsub.subset he) $$ Hitems
          rw [chElems_eq Hch_lookup] at hdd0
          have hpre' : acc ++ descRange o.lt (sufElems is cs 0) ks ku ++
              (if W64 (-1) = W64 1 then ascRange o.lt ch.elems ks ku
                else descRange o.lt ch.elems ks ku) <+: r := by
            rw [ite_eq_right hne]
            refine List.IsPrefix.trans ?_ hseg
            rw [hdd0, List.append_assoc]
            exact List.prefix_refl _
          have hchit : W64 (-1) = W64 (-1) → hitv = true → ∀ a, ks = some a →
              ∀ e ∈ ch.elems, o.lt e.2 a := by
            intro _ hh a ha e he
            exact hHit0 hh a ha e (by rw [chElems_eq Hch_lookup]; simp [he])
          wp_apply (IH h' (by omega) p ch hitv _ hchs (Sorted.sublist hsub hs) (Or.inr rfl) hinc
            hchit hpre') $$ [Hc HI] as %hitv' %okv ⟨Hc, Hpost⟩
          · iframe # ∗
          ihave Hn := Hclose $$ [Hnn Hfi Hfc Hfw Hisl Hcsl Hch Hc]
          · iframe
            iapply (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2; iframe
          cases okv
          · -- the child stopped
            wp_auto
            iapply HΦ
            iframe Hn
            iright
            isplitr
            · ipureintro; rfl
            icases Hpost with (⟨%Hok, _⟩ | ⟨_, (⟨%pre, %Hpre, HI⟩ | ⟨HI, %Hstop⟩)⟩)
            · exact absurd Hok.1 (by simp)
            · ileft; iexists pre; iframe; ipureintro
              refine ⟨(List.prefix_append _ _).trans Hpre.1, ?_⟩
              rw [hdd0, ← List.append_assoc]; exact Hpre.2
            · iright
              obtain ⟨b, hb, e, he1, he2⟩ := Hstop
              rw [hdd0]
              isplitl [HI]
              · iExactEq HI; simp
              ipureintro; exact ⟨b, hb, e, hsub.subset he1, he2⟩
          -- the child went to its end
          wp_auto
          icases Hpost with (⟨%Hok, HI⟩ | ⟨%Hok, _⟩)
          rotate_left
          · exact absurd Hok (by simp)
          iapply HΦ
          iframe Hn
          ileft
          isplitr
          · ipureintro
            refine ⟨rfl, fun _ => ?_⟩
            rw [Hok.2 trivial, Hhv, hdd0, not_isEmpty_append, Bool.or_assoc]
          rw [hdd0]
          iExactEq HI; simp
        · -- a leaf
          have hcs : cs = [] := by
            cases cs with
            | nil => rfl
            | cons _ _ =>
              have h0 : 0 < ps.length := by simp [Hlenps]
              word
          rw [show chElems cs 0 = [] by rw [hcs, chElems_of_nil]] at hdd0
          rw [show descRange o.lt ([] : List (V × K)) ks ku = [] from rfl, List.append_nil] at hdd0
          iapply HΦ
          isplitl [Hclose Hnn Hfi Hfc Hfw Hisl Hcsl Hch]
          · iapply Hclose; iframe
          ileft
          isplitr
          · ipureintro
            refine ⟨rfl, fun _ => ?_⟩
            rw [Hhv, hdd0]
          rw [hdd0]
          iExactEq HI; rfl
    · exfalso
      rcases hdir with h1 | h1 <;> contradiction

end proof

end btree
end EtcdGrove
end Perennial
