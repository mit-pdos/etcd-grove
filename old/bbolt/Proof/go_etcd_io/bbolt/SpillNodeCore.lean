module
public import Proof.go_etcd_io.bbolt.SpillNodeGhost
public import Proof.go_etcd_io.bbolt.SpillNodePost
public import Proof.go_etcd_io.bbolt.SpillNodeDone
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

/-- A spilled part returns at once. -/
theorem node.spill.wp_done : node.spill.doneSpec (GF := GF) (hG := hG) := by
  intro I γd γ W txl txid T ρ F K bl B n hg hB hsp
  obtain ⟨rc, hrc, hs, -, hbk, -⟩ := hsp
  wp_start as HR
  icases spillR_node I γd γ W txl txid T ρ F K bl B n rc hB hrc $$ HR with ⟨Hn, Hb, Hback⟩
  wp_auto
  rw [hbk]
  wp_auto
  rw [hs]
  wp_auto
  iapply HΦ
  iapply Hback $$ Hn Hb

/-- An error, whatever the mode. -/
theorem spErrPost (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (S : List Loc) (n : Loc) (r : NRec) (K : Loc → Bool) (ht : Loc → Nat) (err : GoInterface)
    (he : err ≠ interface.nil) (hp : r.nv.parent' ≠ null → (B.ns !! r.nv.parent').isSome) :
    spillErr I γd txl txid ⊢
      if r.nv.parent' = null then finPost I γd γ W txl txid T bl B K err
      else ∃ rp, ⌜B.ns !! r.nv.parent' = some rp⌝ ∗
        node.spill.subPost I γd γ W txl txid T bl B bnd S n r r.nv.parent' rp K ht err := by
  iintro H
  by_cases h : r.nv.parent' = null
  · rw [if_pos h]
    unfold finPost
    iright
    iframe
    ipureintro; exact he
  · rw [if_neg h]
    obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.1 (hp h)
    iexists rp
    isplitr
    · ipureintro; exact hrp
    unfold node.spill.subPost
    iright
    iframe
    ipureintro; exact he

set_option maxHeartbeats 2000000 in
/-- The body of `n.spill()` on an unspilled node `n` (record `r`) in its children loop
(`nodeL`): each child spilled (`sp c`) or unspilled with its tree `sub c` (`subU`, shorter than
`N`: `hsub`); its parent nil (a root, or a new parent: `top`, its children all spilled, the
up-recursion by `htopB`; a root's by `htop`) or the unspilled branch `pl` (`subPost`). -/
theorem node.spill.wp_core
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
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (N : Nat) (top : Bool)
    (hsub : top = false → node.spill.subSpecB (GF := GF) (hG := hG) N)
    (htop : top = false → node.spill.topSpec (GF := GF) (hG := hG))
    (htopB : top = true → ∀ m, m < N → node.spill.topSpecB (GF := GF) (hG := hG) m)
    (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (ht : Loc → Nat) (n : Loc)
    (r : NRec) (sp : Loc → Bool) (sub : Loc → List Loc) :
    I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → T.bs !! bl = some B →
    (top = false → nodeHts B ht) → (r.nv.isLeaf' = true → ht n = 0) →
    (r.nv.isLeaf' = false → 1 ≤ ht n) →
    B.ns !! n = some r → K n = false → nodeL W bl B bnd kd n r →
    (∀ c ∈ r.cs, kidsTree B.ns c (sub c) ∧
      (sp c = true → spilledN bl B c) ∧
      (sp c = false → (sub c).length < N ∧ subU W bl B bnd kd K c (sub c))) →
    (top = true → (∀ c ∈ r.cs, sp c = true) ∧ r.ws.length ≤ N) → (top = true → r.nv.parent' = null) →
    (top = true → ∃ p, upPath B.ns B.bv.rootNode' p n ∧ p.Nodup ∧
      (∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ r.cs) ∧
      ∀ l ∈ p, l = n ∨ l ∈ r.cs ∨ ∃ r', B.ns !! l = some r' ∧ noViewRec r') →
    kidsTree B.ns n (n :: (r.cs.map sub).flatten) →
    uint.Z (splitThr (W64 (W.ps : Int)) B.bv.FillPercent') ≤ W.ps → W.ps < 2 ^ 20 →
    (∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) →
    (∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) →
    (∀ l r, B.ns !! l = some r → l ≠ n → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) →
    (top = false → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) →
    (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) →
    (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
      (spillPages W T !! uint.nat w.pgid).isSome) →
    (top = false → treeOK bl B) →
    (r.nv.parent' = null → bnd n = (none, none) ∧
      ∃ p, upPath B.ns B.bv.rootNode' p n ∧ p.Nodup ∧
        ∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ (r.cs.map sub).flatten) →
    (∀ pl rp, r.nv.parent' = pl → pl ≠ null → B.ns !! pl = some rp →
      pl ∉ n :: (r.cs.map sub).flatten ∧ K pl = false ∧ nodeL W bl B bnd kd pl rp ∧
      rp.nv.pgid' ≠ W64 0 ∧ rp.nv.isLeaf' = false) →
    (∀ pl rp, r.nv.parent' = pl → pl ≠ null → B.ns !! pl = some rp → n ∈ rp.cs) →
    (r.nv.parent' ≠ null → (B.ns !! r.nv.parent').isSome) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
        rtoks γ (spillPages W T) B (bnd n) (kd n) (ht n - 1) r ∗
        [∗list] c ∈ r.cs, (if sp c then emp else
          [∗list] l ∈ sub c, ∃ rl, ⌜B.ns !! l = some rl⌝ ∗ rtoks γ (spillPages W T) B (bnd l) (kd l) (ht l - 1) rl) }}
      (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
    {{ (err : GoInterface), RET #err;
        if r.nv.parent' = null then finPost I γd γ W txl txid T bl B K err
        else ∃ rp, ⌜B.ns !! r.nv.parent' = some rp⌝ ∗
          node.spill.subPost I γd γ W txl txid T bl B bnd (n :: (r.cs.map sub).flatten) n r
            r.nv.parent' rp K ht err }} := by
  intro hf hg hB hHt hht0 hht1 hn hK hL hch htopc htopn htopv hkt hthr hps hel hne hP1 hP1n hP2 hP3 htok hpar0 hplf
    hplin hpar1
  wp_start as ⟨HR, Hrt, Hch⟩
  icases spillR_node I γd γ W txl txid T ρ F K bl B n r hB hn $$ HR with ⟨Hn, Hb, Hback⟩
  icases typedPointsto_not_null_dup n r.nv (DFrac.own 1) $$ Hn with ⟨Hn, %hnn⟩
  wp_auto
  rw [hL.1]
  wp_auto
  rw [hL.2.1]
  wp_auto
  ihave HR := Hback $$ Hn Hb
  have hkids : ∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ 0 < rc.ws.length ∧
      rc.ins.length = rc.ws.length ∧ wsLive rc.ws :=
    spKids_ok W bl B bnd kd K N n r sp sub hnn hL hch hne
  have hcnd : r.cs.Nodup := spCs_nodup W bl B bnd kd n r hL
  have hnc : n ∉ r.cs := spKids_notin B.ns n r.cs sub hkt (fun c hc => (hch c hc).1)
  have hcar : W.data.locCar ≠ 0 := hg.1.1
  icases spillR_sort I γd γ W txl txid T ρ F K bl B n r hB hn hcnd hnc hcar hkids $$ HR
    with ⟨%q, Hcs, Hsr, Hsback⟩
  unfold sortRes
  wp_apply hSort r.nv.children' r.cs (sortF B.ns) (sortG B.ns) (sortK B.ns) (fun _ => DFrac.own 1)
    (fun _ => DFrac.own 1) (sortQ B.ns q) (sortG_ne B.ns r.cs hkids) $$ [Hcs Hsr] as %ys ⟨%hperm, Hcs, Hsr⟩
  · iframe
  ihave HR := Hsback $$ %ys %hperm Hcs Hsr
  have hL0 : loopP (hG := hG) bl bnd kd ht N n txl txid W T B r K (n :: (r.cs.map sub).flatten)
      W (setB T bl (setN B n { r with cs := ys })) ρ F K (setN B n { r with cs := ys })
      { r with cs := ys } 0 sp sub :=
    spLoopStart W txl txid T ρ F K bl B bnd kd ht N n r sp sub ys hg hB hn hK hL hch hkt hel hne hP1 hP2
      hP3 hperm
  ihave Hch0 : subToks γ (spillPages W (setB T bl (setN B n { r with cs := ys })))
      (setN B n { r with cs := ys }) bnd kd ht sp sub ({ r with cs := ys }.cs.drop 0) $$ [Hch]
  · iapply spSubToks_sort γ (spillPages W T) (spillPages W (setB T bl (setN B n { r with cs := ys }))) B n r ys bnd kd ht sp sub rfl hperm (spKids_notsub B.ns n r.cs sub hkt)
    iexact Hch
  ihave Hrt0 : rtoks γ (spillPages W (setB T bl (setN B n { r with cs := ys })))
      (setN B n { r with cs := ys }) (bnd n) (kd n) (ht n - 1) { r with cs := ys } $$ [Hrt]
  · iapply spRtoks_sort γ (spillPages W T) (spillPages W (setB T bl (setN B n { r with cs := ys }))) B n r ys (bnd n) (kd n) (ht n - 1) rfl
    iexact Hrt
  ihave IH : iprop(∃ (iv : w64) (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8))
      (K' : Loc → Bool) (B' : BRec) (rn : NRec) (sp' : Loc → Bool) (sub' : Loc → List Loc),
      "n" ∷ n_ptr ↦ n ∗ "tx" ∷ tx_ptr ↦ B.bv.tx' ∗ "i" ∷ i_ptr ↦ iv ∗
      "HR" ∷ spillR I γd γ W' txl txid T' ρ' F' K' ∗
      "Hrt" ∷ rtoks γ (spillPages W' T') B' (bnd n) (kd n) (ht n - 1) rn ∗
      "Hch" ∷ subToks γ (spillPages W' T') B' bnd kd ht sp' sub' (rn.cs.drop (sint.nat iv)) ∗
      "%Hlp" ∷ ⌜loopP (hG := hG) bl bnd kd ht N n txl txid W T B r K (n :: (r.cs.map sub).flatten)
        W' T' ρ' F' K' B' rn (sint.nat iv) sp' sub' ∧ 0 ≤ sint.Z iv ∧
        (top = true → ∀ c ∈ rn.cs.drop (sint.nat iv), sp' c = true) ∧
        (top = false → treeOK bl B') ∧
        (top = true → W' = W ∧ T' = setB T bl (setN B n { r with cs := ys }) ∧
          B' = setN B n { r with cs := ys } ∧ rn = { r with cs := ys } ∧ K' = K)⌝) $$ [n tx i HR Hrt0 Hch0]
  · iexists W64 0, W, (setB T bl (setN B n { r with cs := ys })), ρ, F, K,
      (setN B n { r with cs := ys }), { r with cs := ys }, sp, sub
    iframe
    ipureintro
    refine ⟨hL0, by decide, fun ht c hc => (htopc ht).1 c ((List.Perm.mem_iff hperm).1 hc),
      fun ht => treeOK_perm_cs bl B n r ys (htok ht) hn hperm, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  wp_for IH
  obtain ⟨hlp, hiv, htp, htrp, htt0⟩ := Hlp
  icases spillR_kids I γd γ W' txl txid T' ρ' F' K' bl B' n rn hlp.2.1 hlp.2.2.1 $$ HR
    with ⟨Hnn, Hkc, Hkback⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hkc
  try wp_auto
  by_cases hlt : sint.Z iv < sint.Z rn.nv.children'.len
  · rw [decide_eq_true hlt, ite_eq_left_of_eq_true _ _ (eq_true (by simp))]
    try wp_auto
    obtain ⟨c, hc⟩ : ∃ c, rn.cs[sint.nat iv]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by have := Hkl.1; word)⟩
    icases ownSlice_elem_acc (sint.Z iv) c rn.nv.children' (DFrac.own 1) rn.cs hiv
      (by have e : (sint.Z iv).toNat = sint.nat iv := rfl; rw [e]; exact hc) $$ Hkc with ⟨Hc, Hcback⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hiv, hlt⟩)]
    try wp_auto
    ihave Hkc := Hcback $$ Hc
    rw [list_set_lookup_self rn.cs _ c (by have e : (sint.Z iv).toNat = sint.nat iv := rfl; rw [e]; exact hc)]
    ihave HR := Hkback $$ Hnn Hkc
    have hi1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by have := Hkl.1; have := Hkl.2; word
    have hi1' : 0 ≤ sint.Z (iv + W64 1) := by have := Hkl.1; have := Hkl.2; word
    by_cases hsp : sp' c = true
    · have hspn := loop_child bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' c hlp hc hsp
      wp_apply (node.spill.wp_done I γd γ W' txl txid T' ρ' F' K' bl B' c hlp.1 hlp.2.1 hspn) $$ [HR] as HR
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists (iv + W64 1), W', T', ρ', F', K', B', rn, sp', sub'
      iframe
      rw [hi1]
      isplitl [Hch]
      · iapply subToks_done γ _ B' bnd kd ht sp' sub' rn.cs (sint.nat iv) c hc hsp
        iexact Hch
      ipureintro
      refine ⟨loop_done bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' c hlp hc hsp, hi1',
        fun ht x hx => htp ht x (mem_drop_succ _ _ _ hx), htrp, htt0⟩
    · have hspf : sp' c = false := by simpa using hsp
      have htf : top = false := by
        cases ht : top
        · rfl
        · exact absurd (htp ht c (mem_drop_of_get _ _ _ hc)) hsp
      obtain ⟨hg', hB', hrn', hKn', hbv', hps', hL', hok', hpar', hleaf', hpgid'⟩ :=
        loopP_facts bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' hlp
      obtain ⟨rc, hrc, hlen, hsu, hparc, hnS, hleafn, hpgn, hP1a⟩ :=
        loop_sub_pre bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' c hlp hc hspf
          hnn (hP1n htf)
      icases subToks_sub γ _ B' bnd kd ht sp' sub' rn.cs (sint.nat iv) c hc hspf $$ Hch with ⟨Hsc, Hch⟩
      have hHt' : nodeHts B' ht :=
        (loopP_tree bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' hlp
          (htok htf) (hHt htf)).2
      have hnS0 : n ∈ n :: (r.cs.map sub).flatten := List.mem_cons_self
      wp_apply (hsub htf I γd γ W' txl txid T' ρ' F' K' bl B' bnd kd (sub' c) c rc n rn ht hf hg' hB'
        hHt' hlen hsu hrc hparc hnn hrn' (List.mem_of_getElem? hc) hnS hKn' hL' hpgn hleafn (by rw [hbv', hps']; exact hthr)
        (by rw [hps']; exact hps) hok'.1 hok'.2.1 hP1a hok'.2.2.1 hok'.2.2.2 (htrp htf)) $$ [HR Hsc] as %err Hpost
      · iframe
      isimp only [node.spill.subPost] at Hpost
      icases Hpost with (⟨%he, %W'', %T'', %ρ'', %F'', %K'', %B'', %ps, %xs, %rn', HR, Hpcs, %hpp⟩ |
        ⟨%he, Herr⟩)
      · subst he
        try wp_auto
        wp_for_post
        iframe
        iexists (iv + W64 1), W'', T'', ρ'', F'', K'', B'', rn', (fun x => if x ∈ xs then true else sp' x),
          (fun x => if x ∈ xs then [x] else sub' x)
        iframe
        rw [hi1]
        ihave ⟨Hrt, Hch⟩ := toks_sub_post γ bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp'
          sub' c rc W'' T'' ρ'' F'' K'' B'' ps xs rn' hlp hc hspf hrc hpp (hHt htf) $$ [Hrt Hch Hpcs]
        · iframe
        iframe
        ipureintro
        refine ⟨loop_sub_post bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub' c rc
          W'' T'' ρ'' F'' K'' B'' ps xs rn' hlp hc hspf hrc hpp hnS0 (htok htf) (hHt htf), hi1', fun ht => absurd ht (by rw [htf]; decide),
          fun _ => subPostP_tree hpp, fun h => absurd h (by rw [htf]; decide)⟩
      · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
          cases err with
          | nil => exact absurd rfl he
          | ok e => exact ⟨e, rfl⟩
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ
        iapply spErrPost
        · exact he
        · exact hpar1
        iexact Herr
  · rw [decide_eq_false hlt]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => by simp only [decide_eq_true_eq, intoVal_eq_iff] at h; cases h))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true rfl))]
    ihave HR := Hkback $$ Hnn Hkc
    obtain ⟨hall, hdrop⟩ := loop_exit bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _ sp' sub'
      hlp (by have := Hkl.1; have := Hkl.2; word)
    generalize hic : sint.nat iv = ic at hlp hdrop
    icases spillR_upd I γd γ W' txl txid T' ρ' F' K' bl B' n rn hlp.2.1 hlp.2.2.1 $$ HR
      with ⟨Hn, Hcap, Hupd⟩
    isimp only [nodeOwnX] at Hn
    icases Hn with ⟨Hnn, Hins, Hents, Hch, Hchcap, Hkey⟩
    try wp_auto
    ihave Hch0 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hcc0 := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave HR := Hupd $$ %({ rn with nv := { rn.nv with children' := slice.nil }, cs := [] } : NRec) %(K' n)
      [Hnn Hins Hents Hch0 Hcc0 Hkey] [Hcap]
    · unfold nodeOwnX; dsimp only; iframe; iframe #
    · unfold capK capOwn; iexact Hcap
    -- the cut: the children leave the bucket, but those on the root's parent chain
    have hK2 : (fun l => if l = n then K' n else K' l) = K' := by
      funext l; by_cases e : l = n
      · subst e; simp
      · simp [e]
    rw [hK2]
    have hB2 : (setB T' bl (setN B' n { rn with nv := { rn.nv with children' := slice.nil }, cs := [] })).bs !! bl =
        some (setN B' n { rn with nv := { rn.nv with children' := slice.nil }, cs := [] }) :=
      GMap.lookup_insert _ _ _
    ihave HR := spillR_cut I γd γ W' txl txid _ ρ' F' K' bl _
      (onRootPath B') rn.cs hB2 hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ HR
    have htx : B.bv.tx' = txl := hg.2.2.2.2.2.2.2.2.2.1 bl B hB
    have hdb' : T'.t.db' = W'.dbl := hlp.1.2.2.2.2.2.2.2.1
    rw [htx]
    icases (spillR_at I γd γ W' txl txid _ ρ' F' K' bl _ (GMap.lookup_insert _ _ _)).1 $$ HR
      with ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
    isimp only [TxW_rest_root] at Ht
    icases Ht with ⟨Hwr, Hman, Hdbf, Hmet, Hpgs, Hsts, Hchs, Hwf, %Htn⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hd, #Hps, #Hlg, Hfl, #Hdl, %Hlgv, Hpv⟩
    dsimp only [setB] at hdb' ⊢
    try wp_auto
    rw [hdb']
    try wp_auto
    ihave HR := (spillR_at I γd γ W' txl txid
      (setB (setB T' bl (setN B' n { rn with nv := { rn.nv with children' := slice.nil }, cs := [] })) bl
        { setN B' n { rn with nv := { rn.nv with children' := slice.nil }, cs := [] } with
          ns := cutNs (setN B' n { rn with nv := { rn.nv with children' := slice.nil }, cs := [] }).ns
            (onRootPath B') rn.cs }) ρ' F' K' bl _ (GMap.lookup_insert _ _ _)).2 $$
      [Hdb Hd Hfl Hpv Hwr Hman Hdbf Hmet Hpgs Hsts Hchs Hwf Hm Hpm Hbufs Hb Hc Ho Hg HF]
    · dsimp only [setB]
      iframe Hdb Hm Hpm Hbufs Hb Hc Ho Hg HF
      isplitl [Hd Hfl Hpv]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      unfold TxW_rest_root; rw [hdb']; iframe; ipureintro; exact Htn
    generalize hrc : ({ rn with nv := { rn.nv with children' := slice.nil }, cs := [] } : NRec) = rc at *
    generalize hB3 : ({ setN B' n rc with ns := cutNs (setN B' n rc).ns (onRootPath B') rn.cs } : BRec) = B3 at *
    generalize hT3 : setB (setB T' bl (setN B' n rc)) bl B3 = T3 at *
    have hT3b : T3.bs !! bl = some B3 := by rw [← hT3]; exact GMap.lookup_insert _ _ _
    icases spP_nnull I γd γ W' txl txid T3 ρ' F' K' bl B3 hT3b $$ HR with ⟨%h3nn, HR⟩
    have hlpc := hlp
    obtain ⟨-, -, -, -, -, -, -, -, hl9, -, -, -, hl13, hl14, -, -, hl17, -, -, -, hl21, hl22, -, -, -, -, -,
      hl28, -, -, hl31, -⟩ := hlpc
    have hn3 : B3.ns !! n = some rc := by
      rw [← hB3]
      show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! n = some rc
      rw [cutNs_lookup _ _ _ hl21 n, if_neg hl22]; exact GMap.lookup_insert _ _ _
    have hrcb : rc.nv.bucket' = bl := by rw [← hrc]; exact hl17.1
    have hrcs : rc.cs = [] := by rw [← hrc]
    have htx3 : B3.bv.tx' = txl := by
      rw [← hB3]; show B'.bv.tx' = txl; rw [hl9]; exact htx
    have hpe3 : rc.nv.parent' = r.nv.parent' := by
      rw [← hrc]; show rn.nv.parent' = r.nv.parent'; rw [hl13]
    have hpar3 : rc.nv.parent' ≠ null → ∃ rp, B3.ns !! rc.nv.parent' = some rp ∧ wsLive rp.ws ∧
        rp.ins.length = rp.ws.length ∧ wsSorted rp.ws ∧ rp.nv.bucket' = bl ∧ rc.nv.parent' ≠ n ∧
        ∃ (i1 : Nat) (w : WEntry), rp.ws[i1]? = some w ∧ w.key = rc.key ∧ w.pgid = rc.nv.pgid' := by
      intro hp
      rw [hpe3] at hp ⊢
      obtain ⟨rp0, hrp0⟩ := Option.isSome_iff_exists.1 (hpar1 hp)
      obtain ⟨hnS, -, hLp, -, hbr⟩ := hplf _ rp0 rfl hp hrp0
      obtain ⟨rp, hrp, h1, h2, h3, h4, hplc, hpln, i1, w, hw, hk, hpg, -⟩ :=
        spParentAtCut bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn ic sp' sub' hlp hn hL
          List.mem_cons_self _ rp0 hrp0 hnS hLp hbr (hplin _ rp0 rfl hp hrp0)
      refine ⟨rp, ?_, h1, h2, h3, h4, hpln, i1, w, hw, ?_, ?_⟩
      · rw [← hB3]
        show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! r.nv.parent' = some rp
        rw [cutNs_lookup _ _ _ hl21 _, if_neg hplc]
        show (<[n := rc]> B'.ns) !! r.nv.parent' = some rp
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hpln)]; exact hrp
      · rw [hk, ← hrc]; exact hl14.symm
      · rw [hpg, ← hrc]; show r.nv.pgid' = rn.nv.pgid'; rw [hl13]
    -- the node's entry in its parent: its key non-nil, its bounds within the entry's
    have hpar3b : rc.nv.parent' ≠ null → rc.nv.key' ≠ slice.nil ∧ ∃ rp, B3.ns !! rc.nv.parent' = some rp ∧
        wsSorted rp.ws ∧ ∃ (i1 : Nat) (w : WEntry), rp.ws[i1]? = some w ∧ w.key = rc.key ∧
        bndIn (bnd n) (entryBnd (bnd rc.nv.parent') rp.ws i1) := by
      intro hp
      rw [hpe3] at hp ⊢
      obtain ⟨rp0, hrp0⟩ := Option.isSome_iff_exists.1 (hpar1 hp)
      obtain ⟨hnS, -, hLp, -, hbr⟩ := hplf _ rp0 rfl hp hrp0
      obtain ⟨rp, hrp, -, -, h3, -, hplc, hpln, i1, w, hw, hk, -, hkn, hbnd⟩ :=
        spParentAtCut bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn ic sp' sub' hlp hn hL
          List.mem_cons_self _ rp0 hrp0 hnS hLp hbr (hplin _ rp0 rfl hp hrp0)
      have hkl : 0 < r.key.length := by
        rcases hL.2.2.2.2.2.2.1 with h | ⟨h, -⟩
        · exact absurd h hkn
        · exact h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        hkk⟩ := hlp
      refine ⟨by rw [← hrc]; exact hkk hkn hkl, rp, ?_, h3, i1, w, hw, by rw [hk, ← hrc]; exact hl14.symm, hbnd⟩
      rw [← hB3]
      show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! r.nv.parent' = some rp
      rw [cutNs_lookup _ _ _ hl21 _, if_neg hplc]
      show (<[n := rc]> B'.ns) !! r.nv.parent' = some rp
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hpln)]; exact hrp
    have hpl3 : rc.nv.parent' ≠ null → B3.ns !! rc.nv.parent' = some ((B3.ns !! rc.nv.parent').getD rc) ∧
        rc.nv.parent' ≠ n := by
      intro hp
      obtain ⟨rp, h, -, -, -, -, hpln, -⟩ := hpar3 hp
      rw [h]; exact ⟨rfl, hpln⟩
    have hdok3 : derefOK bl rc := by
      have h := spDerefOK_nodeL W' bl B' bnd kd n rn hl17
      rw [← hrc]; exact h
    have hlv : ∃ S, liveNodesX B' S ∧ (∀ l ∈ S, ∃ r, B'.ns !! l = some r ∧ derefOK bl r) ∧ n ∈ S ∧
        (rn.nv.parent' ≠ null → rn.nv.parent' ∈ S ∧ rn.nv.parent' ∉ rn.cs) ∧
        (rn.nv.parent' = null → ∃ p, upPath B'.ns B'.bv.rootNode' p n) ∧
        (∀ l r, B'.ns !! l = some r → l ∉ S → noViewRec r) := by
      cases htt : top
      · exact hlv_of_treeOK bl B' n rn (loopP_tree bl bnd kd ht N n txl txid W T B r K _ W' T' ρ' F' K' B' rn _
          sp' sub' hlp (htok htt) (hHt htt)).1 hlp.2.2.1
      · obtain ⟨p, hu, hpnd, hdom, hpv⟩ := htopv htt
        obtain ⟨-, -, hB', hrn, -⟩ := htt0 htt
        obtain ⟨hu', hdom', hpv'⟩ := spTopP B n r ys p hn hperm hu hdom hpv
        have hpn' : rn.nv.parent' = null := by rw [hrn]; exact htopn htt
        subst hB' hrn
        exact hlv_top bl _ n _ p (GMap.lookup_insert _ _ _) hpn' hall hl21 hl22 hu' hpnd hpv'
          (spDerefOK_nodeL W' bl _ bnd kd n _ hl17) hdom'
    obtain ⟨hg3c, hlive3c⟩ := spillG_cut W' txl txid T' ρ' F' bl B' n rn hlp.1 hlp.2.1 hlp.2.2.1 hall hl21 hl22 hlv
    have hg3 : spillG (hG := hG) W' txl txid T3 ρ' F' := by rw [← hT3, ← hB3, ← hrc]; exact hg3c
    have hKp3 : rc.nv.parent' ≠ null → K' rc.nv.parent' = false := by
      intro hp
      rw [hpe3] at hp ⊢
      obtain ⟨rp0, hrp0⟩ := Option.isSome_iff_exists.1 (hpar1 hp)
      obtain ⟨hnS, hKp, -⟩ := hplf _ rp0 rfl hp hrp0
      rw [hl31.1 _ hnS (by rw [hrp0]; rfl)]; exact hKp
    icases persistent_entails_left (spSpillR_lens I γd γ W' txl txid T3 ρ' F' K' bl B3 n rc hT3b hn3) $$ HR
      with ⟨HR, %hlensC⟩
    have hilR : rc.ins.length = rc.ws.length := by rw [← hrc]; exact hl17.2.2.1
    have hliveR : wsLive rc.ws := by rw [← hrc]; exact hl17.2.2.2.2.2.1
    have hlensR : ∀ (i : Nat) (it : Inode) (w : WEntry), rc.ins[i]? = some it → rc.ws[i]? = some w →
        uint.nat it.key'.len = w.key.length ∧ uint.nat it.value'.len = w.value.length := by
      intro i it w h1 h2
      have h := hlensC i it w h1 h2
      have hw := hliveR w (List.mem_of_getElem? h2)
      exact ⟨h.1 hw.1, h.2 hw.2⟩
    have helR : ∀ w ∈ rc.ws, w.key.length + w.value.length ≤ 2 ^ 28 := by
      intro w hw
      have hw' : w ∈ rn.ws := by rw [← hrc] at hw; exact hw
      exact hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1 n rn hlp.2.2.1 w hw'
    have hWps : W'.ps = W.ps := hlp.2.2.2.2.2.2.1
    have hB3bv : B3.bv = B.bv := by rw [← hB3]; show B'.bv = B.bv; exact hl9
    icases spillR_split I γd γ W' txl txid T3 ρ' F' K' bl B3 n rc ((B3.ns !! rc.nv.parent').getD rc)
      hT3b hn3 hlp.2.2.2.1 hrcb htx3 hpl3 hrcs hKp3 $$ HR with ⟨⟨Hn, Hins, Hcap, Hbk, Hst, Hpo⟩, Hsback⟩
    ihave %Hinsl := ownSlice_len _ _ _ $$ Hins
    rw [htx3]
    wp_apply hSplit n rc.nv rc.ins B3.bv (DFrac.own 1) T3.t.stats' ((B3.ns !! rc.nv.parent').getD rc).nv
      ((B3.ns !! rc.nv.parent').getD rc).cs (W64 (W'.ps : Int)) $$ [Hn Hins Hcap Hbk Hst Hpo]
      as %sl %xs ⟨%hxsf, Hbk, Hsl, Hxs⟩
    · rw [hrcb, htx3]; iframe
    try wp_auto
    -- TODO: the parts loop (free, allocate, write, put into the parent, key), then the
    -- up-recursion `n.parent.spill()` or the return.
    ihave Hst0 := parts_start I γd γ W' txl txid T3 ρ' F' K' bl B3 n rc ((B3.ns !! rc.nv.parent').getD rc)
      (bnd n).1 (bnd n).2 hg3 hT3b hn3 hlp.2.2.2.1 hrcs xs hdok3
      (fun hp => by
        obtain ⟨rp, h, h1, h2, h3, h4, hpln, i1, w, hw, hk, hpg⟩ := hpar3 hp
        rw [h]; exact ⟨rfl, hKp3 hp, h1, h2, h3, h4, hpln, i1, w, hw, hk, hpg⟩)
      (by rw [← hB3, ← hrc]; exact hlive3c) $$ [Hxs Hsback Hbk]
    · icases Hxs with (⟨%heq, Hn, Hins, Hcap, Hst, Hpo⟩ | ⟨%pl, %pv', %pcs', %xl, %hsf, Hpts, Hxl, Hpl, Hpch, Hpcc, Hst⟩)
      · ileft
        icases Hsback with ⟨Hb1, -⟩
        isplitl []
        · ipureintro; exact heq
        iapply Hb1; rw [hrcb, htx3]; iframe
      · iright
        icases Hsback with ⟨-, Hb2⟩
        iexists pl, pv', pcs', xl, _
        isplitl []
        · ipureintro; exact hsf
        rw [hrcb, htx3]
        iapply Hb2 $$ %xs %pl %pv' %pcs' %xl %_ %hsf Hbk Hpts Hxl Hpl Hpch Hpcc Hst
    icases Hst0 with ⟨%Ts, %Bs, %Ks, %par, %ws0, %i0, HR, %hst⟩
    have hlay := spSplitLayout rc xs (splitThr (W64 (W'.ps : Int)) B3.bv.FillPercent') (W64 (W'.ps : Int))
      (by
        have e : uint.Z (W64 (W'.ps : Int)) = (W'.ps : Int) := by rw [hWps]; have := hps; word
        rw [e, hWps, hB3bv]; exact hthr)
      (by rw [hWps]; have := hps; word) hxsf.1 hxsf.2 hst.2.1.2.2.2.1.1 hilR hlensR helR
      (by have := Hinsl.1; have := Hinsl.2; word)
    icases toks_start γ (spillPages W' T') B' Bs (bnd n) (kd n) (ht n - 1) rn rc xs
      (by rw [hst.2.2.2.1.2.2.1, ← hB3]; rfl)
      (by rw [← hrc]) (by rw [← hrc]) (by rw [← hrc]) hst.2.1.2.2.2.1 (by rw [← hrc]; exact hl17.2.2.1)
      $$ Hrt with ⟨Hpg0, Hct⟩
    have hPs : spillPages W' Ts = spillPages W' T' := by
      have hb3 : Ts.bufs = T'.bufs := by
        rcases hst.2.2.2.2 with ⟨-, hTs, -, -⟩ | ⟨pv', pcs', st, -, -, -, -, hTs, -⟩
        · rw [hTs, ← hT3]; rfl
        · rw [hTs, ← hT3]; rfl
      unfold spillPages; rw [hb3]
    rw [← hPs]
    ihave IH : iprop(∃ (iv : w64) (W'' : WView) (T'' : WTx) (ρ'' : DBState) (F'' : GMap Nat (List w8))
        (K'' : Loc → Bool) (B'' : BRec) (ps : List (w64 × List w8)) (nl : Loc),
        "n" ∷ n_ptr ↦ n ∗ "tx" ∷ tx_ptr ↦ txl ∗ "i" ∷ i_ptr ↦ iv ∗ "node" ∷ node_ptr ↦ nl ∗
        "Hsl" ∷ sl ↦* xs.map (fun x => x.1) ∗
        "HR" ∷ spillR I γd γ W'' txl txid T'' ρ'' F'' K'' ∗
        "Hpcs" ∷ pieceResP (par ≠ null) γ (spillPages W'' T'') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) ps
          (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
        "Hct" ∷ chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2 ps.length ∗
        "Hpg" ∷ (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ∗
        "%Hpp" ∷ ⌜partsP (hG := hG) bl txl txid n rc xs par ws0 i0 (bnd n).1 (bnd n).2 W' Ts Bs Ks
          W'' T'' ρ'' F'' K'' B'' ps ∧ ps.length = sint.nat iv ∧ 0 ≤ sint.Z iv⌝)
      $$ [n tx i node Hsl HR Hct Hpg0]
    · iexists (W64 0), W', Ts, ρ', F', Ks, Bs, [], _
      iframe
      isplitl []
      · unfold pieceResP; iapply BigSepL.bigSepL_nil.2; iempintro
      isplitl [Hpg0]
      · by_cases h : rc.nv.pgid' = W64 0
        · rw [if_pos h] at *; rw [if_neg (fun h' => h'.2 h)]; iexact Hpg0
        · rw [if_neg h]; rw [if_pos ⟨rfl, h⟩]; iexact Hpg0
      ipureintro
      exact ⟨hst.1, rfl, by decide⟩
    wp_for IH
    obtain ⟨hpp, hpl, hiv⟩ := Hpp
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    by_cases hlt2 : sint.Z iv < sint.Z sl.len
    · rw [decide_eq_true hlt2]
      try wp_auto
      simp only [decide_eq_true_eq, eq_self_iff_true, ite_true]
      try wp_auto
      obtain ⟨x, hx⟩ : ∃ x, (xs.map (fun x => x.1))[sint.nat iv]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by have := Hsll.1; simp only [List.length_map] at this ⊢; word)⟩
      icases ownSlice_elem_acc (sint.Z iv) x sl (DFrac.own 1) _ hiv
        (by have e : (sint.Z iv).toNat = sint.nat iv := rfl; rw [e]; exact hx) $$ Hsl with ⟨Hx, Hxback⟩
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z sl.len from ⟨hiv, hlt2⟩))]
      try wp_auto
      ihave Hsl := Hxback $$ Hx
      rw [list_set_lookup_self _ _ x (by have e : (sint.Z iv).toNat = sint.nat iv := rfl; rw [e]; exact hx)]
      -- the part `x`: its record
      have hxj : (xs[sint.nat iv]?).map (fun x => x.1) = some x := by
        rw [← List.getElem?_map]; exact hx
      obtain ⟨rs, rx, hrs, hrx, hdnk, hpz⟩ :=
        hpp.2.2.2.2.2.2.2.2.2.2.2.2.1 (sint.nat iv) x (by omega) hxj
      icases spillR_node I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' x rx hpp.2.1 hrx $$ HR
        with ⟨Hxn, Hxb, Hxback⟩
      try wp_auto
      wp_join iprop(∃ (ρ3 : DBState) (F3 : GMap Nat (List w8)) (T3 : WTx) (B3 : BRec) (rx3 : NRec),
          "HR" ∷ spillR I γd γ W'' txl txid T3 ρ3 F3 K'' ∗
          "tx" ∷ tx_ptr ↦ txl ∗ "node" ∷ node_ptr ↦ x ∗
          "%Hj" ∷ ⌜T3.bs !! bl = some B3 ∧ B3.ns !! x = some rx3 ∧
            rx3 = { rx with nv := { rx.nv with pgid' := W64 0 } } ∧
            (∀ y, y ≠ x → B3.ns !! y = B''.ns !! y) ∧ B3.bv = B''.bv ∧ B3.ib = B''.ib ∧
            B3.nm = B''.nm ∧ B3.bm = B''.bm ∧ spillFrame T'' T3 (· = bl) ∧ T3.bufs = T''.bufs ∧
            T3.pm = T''.pm ∧ T3.mv = T''.mv ∧ spillG (hG := hG) W'' txl txid T3 ρ3 F3 ∧
            (B3 = setN B'' x rx3 ∨ (B3 = B'' ∧ rx3 = rx))⌝)
        with [Hxn Hxb Hxback Hpg tx node]
      · -- the old page freed
        have hpgn : rx.nv.pgid' ≠ W64 0 := by
          intro h; rw [h] at Hif; exact absurd Hif (by decide)
        have hj0 : ps = [] := by
          cases hps0 : ps with
          | nil => rfl
          | cons a l =>
            rw [hps0] at hpl; simp only [List.length_cons] at hpl
            exact absurd (hpz (by omega)) hpgn
        have hiv0 : sint.nat iv = 0 := by rw [← hpl, hj0]; rfl
        have hrcp : rc.nv.pgid' = rx.nv.pgid' :=
          (spFirstPart bl n rc xs par Bs ws0 i0 hst.2.1 x (by rw [← hiv0]; exact hxj) rs rx hrs hdnk).symm
        obtain ⟨pg, hpgv, hwh, hwf⟩ : ∃ pg, W''.pages !! uint.nat rx.nv.pgid' = some pg ∧
            ∃ h, treeWF W''.pages h (uint.nat rx.nv.pgid') := by
          have hrcn : rx.nv.pgid' = rn.nv.pgid' := by rw [← hrcp, ← hrc]
          rw [hrcn, hpp.2.2.2.1]
          exact hl17.2.2.2.2.2.2.2.1 (by rw [← hrcn]; exact hpgn)
        have hpmn : T''.pm !! rx.nv.pgid' = none :=
          spDirty_pm_none ρ'' W'' T'' rx.nv.pgid' pg hpp.1.2.2.2.2.2.2.2.2.2.2.1 hpgv
        obtain ⟨Hl16, Hid, -, Hk⟩ := treeWF_page _ _ _ pg hwf hpgv
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show ps = [] ∧ rc.nv.pgid' ≠ W64 0 from
          ⟨hj0, by rw [hrcp]; exact hpgn⟩)), hrcp]
        ihave HR := Hxback $$ Hxn Hxb
        icases (spillR_at I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' hpp.2.1).1 $$ HR
          with ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
        isimp only [TxW_rest_root] at Ht
        icases Ht with ⟨Hwr, Hman, Hdbf, Hmet, Hpgs, Hsts, Hchs, Hwf2, %Htn⟩
        isimp only [wView] at Hv
        icases Hv with ⟨Hd, #Hps, #Hlg, Hfl, #Hdl, %Hlgv, Hpv⟩
        icases persistent_entails_left (dbWR_facts I γd W'' txl txid ρ'') $$ Hdb with ⟨Hdb, %hdbf⟩
        ihave #Hcom : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
        · iPkgInit
        ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
        · iPkgInit
        try wp_auto
        wp_apply hTxid T''.t.meta' T''.mv (DFrac.own 1) $$ [Hm] as Hm
        · iframe
        isimp only [bktOwnX] at Hb
        icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W'' l r)
          (show Std.get? B''.ns x = some rx from hrx)).1 $$ Hns with ⟨Hxo, Hns⟩
        isimp only [nodeOwnX] at Hxo
        icases Hxo with ⟨Hxn, Hxi, Hxe, Hxch, Hxcc, Hxk⟩
        have hdb2 : T''.t.db' = W''.dbl := hpp.1.2.2.2.2.2.2.2.1
        rw [hdb2]
        try wp_auto
        have HvOK := hpp.1.1
        have Hlt := HvOK.2.2.2.1 _ pg hpgv
        have HuZ := spFree_uZN rx.nv.pgid' W''.ps HvOK.2.2.1 Hlt
        icases viewLoc_acc W'' _ pg (inViewLoc_page W'' _ pg hpgv) $$ Hpv with ⟨Hpgb, Hpvback⟩
        have Hloc : W''.data +ₗ ((uint.nat rx.nv.pgid' * W''.ps : Nat) : Int) =
            W''.data +ₗ uint.Z (rx.nv.pgid' * W64 (W''.ps : Int)) := by rw [HuZ]
        have Hcar : (W''.data +ₗ ((uint.nat rx.nv.pgid' * W''.ps : Nat) : Int)).locCar ≠ 0 := by
          simpa [Loc.add] using HvOK.1
        have Hflv : validPageFlags (W16 (pageFlags pg : Int)) :=
          validPageFlags_of pg (by rcases Hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])
        have Hidw : W64 (pageId pg : Int) = rx.nv.pgid' := by rw [Hid]; unfold uint.nat; word
        wp_apply hPage txl T''.t.pages' T''.pm (DFrac.own 1) (DFrac.own 1) W''.dbl W''.data
          (W64 (W''.ps : Int)) (DFrac.own W''.q) DFrac.discard rx.nv.pgid'
          (W''.data +ₗ ((uint.nat rx.nv.pgid' * W''.ps : Nat) : Int)) (DFrac.own W''.q) pg
          (Or.inr ⟨hpmn, Hloc, HvOK.1, by rw [HuZ]; push_cast; omega⟩) Hcar Hl16 Hidw Hflv
          $$ [Hpgs Hpm Hdbf Hd Hpgb] as ⟨Hpgs, Hpm, Hdbf, Hd, -, Hpgb⟩
        · iframe; iframe #
        try wp_auto
        -- the freelist
        icases spDbWR_free_acc I γd γ W'' txl txid ρ'' F'' (uint.nat rx.nv.pgid') pg HvOK
          hpp.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hpgv $$ [Hdb HF Hpg] with ⟨%fls, %hfr, Hflo, Hdbback⟩
        · iframe
        obtain ⟨hfli, hcan, hfok⟩ := hfr
        rw [hfli]
        simp only [FLImpl.iface, interface.mkOk]
        try wp_auto
        icases (page_header_bytes (W''.data +ₗ ((uint.nat rx.nv.pgid' * W''.ps : Nat) : Int))
          (DFrac.own W''.q) pg Hl16 Hcar).1 $$ Hpgb with ⟨Hhd, Hrest⟩
        have hid' : (pageOf pg).id' = W64 ((uint.nat rx.nv.pgid' : Nat) : Int) := by
          simp only [pageOf]; rw [Hid]
        have Hcan' : ρ''.fl.canFree txid (pageOf pg).id' (uint.nat (pageOf pg).overflow' + 1) := by
          rw [spFree_ovN pg, hid']; exact hcan
        have htxid : T''.mv.txid' = txid := hpp.1.2.2.2.2.2.1
        rw [htxid]
        wp_apply hf fls ρ''.fl txid _ (pageOf pg) (DFrac.own W''.q) Hcan' $$ [Hflo Hhd] as ⟨Hflo, Hhd⟩
        · iframe
        have Heq : ρ''.fl.freePages txid (W64 (pageId pg : Int)) (uint.nat (W32 (pageOverflow pg : Int)) + 1) =
            ρ''.fl.freePages txid (W64 ((uint.nat rx.nv.pgid' : Nat) : Int)) (1 + pageOverflow pg) := by
          have := spFree_ovN pg
          simp only [pageOf] at this
          rw [this, Hid]
        isimp only [Heq] at Hflo
        try wp_auto
        icases Hdbback $$ Hflo with ⟨Hdb, HF⟩
        ihave Hpgb := (page_header_bytes (W''.data +ₗ ((uint.nat rx.nv.pgid' * W''.ps : Nat) : Int))
          (DFrac.own W''.q) pg Hl16 Hcar).2 $$ [Hhd Hrest]
        · iframe
        ihave Hpv := Hpvback $$ Hpgb
        isplitl []
        · ipureintro; rfl
        have hx3 : (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } }).ns !! x =
            some { rx with nv := { rx.nv with pgid' := W64 0 } } := GMap.lookup_insert _ _ _
        have hB3' : (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } })).bs !! bl =
            some (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } }) := GMap.lookup_insert _ _ _
        ihave HR := (spillR_at I γd γ W'' txl txid
          (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } }))
          { ρ'' with fl := ρ''.fl.freePages txid (W64 ((uint.nat rx.nv.pgid' : Nat) : Int)) (1 + pageOverflow pg) }
          (<[uint.nat rx.nv.pgid' := pg]> F'') K'' bl _ hB3').2 $$
          [Hdb Hd Hfl Hpv Hwr Hman Hdbf Hmet Hpgs Hsts Hchs Hwf2 Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns
            Hxn Hxi Hxe Hxch Hxcc Hxk Hc Ho Hg HF]
        · have e1 : bufsOwn (GF := GF) (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } })) =
              bufsOwn T'' := rfl
          have e2 : ghostOK (GF := GF) γ W'' (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } })) =
              ghostOK γ W'' T'' := rfl
          have e3 : othersOwn (GF := GF) W''
              (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } })).bs bl K'' =
              othersOwn W'' T''.bs bl K'' := othersOwn_insert W'' T''.bs bl _ K''
          rw [e1, e2, e3]
          dsimp only [setB]
          iframe Hdb Hm Hpm Hbufs Ho Hg HF
          isplitl [Hd Hfl Hpv]
          · unfold wView; rw [hfli]; iframe; iframe #; ipureintro; exact Hlgv
          isplitl [Hwr Hman Hdbf Hmet Hpgs Hsts Hchs Hwf2]
          · unfold TxW_rest_root; rw [hdb2]; iframe; ipureintro; exact Htn
          isplitl [Hbv Hib Hnm Hbm Hpo Hns Hxn Hxi Hxe Hxch Hxcc Hxk]
          · unfold bktOwnX setN
            rw [show pageOwn W'' { B'' with ns := <[x := { rx with nv := { rx.nv with pgid' := W64 0 } }]> B''.ns } =
              pageOwn W'' B'' from rfl]
            iframe Hbv Hib Hnm Hbm Hpo
            iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B''.ns) (i := x)
              (x := { rx with nv := { rx.nv with pgid' := W64 0 } }) (Φ := fun l r => nodeOwnX (GF := GF) W'' l r)).2
            iframe Hns
            unfold nodeOwnX
            iframe
          · unfold capsB setN
            icases (BigSepM.bigSepM_delete (M := GMap Loc)
              (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)
              (show Std.get? B''.ns x = some rx from hrx)).1 $$ Hc with ⟨Hcn, Hc⟩
            iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B''.ns) (i := x)
              (x := { rx with nv := { rx.nv with pgid' := W64 0 } })
              (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)).2
            iframe
        iexists { ρ'' with fl := ρ''.fl.freePages txid (W64 ((uint.nat rx.nv.pgid' : Nat) : Int)) (1 + pageOverflow pg) },
          (<[uint.nat rx.nv.pgid' := pg]> F''),
          (setB T'' bl (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } })),
          (setN B'' x { rx with nv := { rx.nv with pgid' := W64 0 } }),
          { rx with nv := { rx.nv with pgid' := W64 0 } }
        iframe
        ipureintro
        refine ⟨hB3', hx3, rfl, fun y hy => GMap.lookup_insert_ne _ _ (Ne.symm hy), rfl, rfl, rfl, rfl,
          spillFrame_setB T'' bl _ (by rw [hpp.2.1]; rfl), rfl, rfl, rfl, ?_, Or.inl rfl⟩
        apply spSpillG_setN W'' txl txid T'' _ _ bl B'' x rx { rx with nv := { rx.nv with pgid' := W64 0 } }
          ?_ hpp.2.1 hrx rfl rfl (fun h => h) ?_
        · exact spSpillG_free W'' txl txid T'' ρ'' F'' _ _ _ hpp.1 hdbf.1 hfok
        · intro ⟨h1, h2, h3, h4⟩
          refine ⟨h1, h2, h3, ?_⟩
          rcases h4 with h4 | ⟨h4a, -⟩
          · exact Or.inl h4
          · exact Or.inr ⟨h4a, Or.inl rfl⟩
      · -- no page
        have hp0 : rx.nv.pgid' = W64 0 := by
          have : ¬ (uint.Z (W64 0) < uint.Z rx.nv.pgid') := Hif
          apply Classical.byContradiction; intro h; apply this
          have : uint.Z rx.nv.pgid' ≠ 0 := fun e => h (by word)
          have : (0 : Int) ≤ uint.Z rx.nv.pgid' := by word
          simp only [show uint.Z (W64 0) = 0 from rfl]; omega
        ihave HR := Hxback $$ Hxn Hxb
        iexists ρ'', F'', T'', B'', rx
        iframe
        ipureintro
        refine ⟨hpp.2.1, hrx, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl, spillFrame_reflN _ _, rfl, rfl,
          rfl, hpp.1, Or.inr ⟨rfl, rfl⟩⟩
        rw [← hp0]
      iintro ⟨%ρ3, %F3, %T3, %B3, %rx3, HR, tx, node, %Hj⟩
      obtain ⟨hT3, hx3, hrx3, hoth, hbv3, hib3, hnm3, hbm3, hfr3, hbuf3, hpm3, hmv3, hg3, hBx3⟩ := Hj
      icases spP_nnull I γd γ W'' txl txid T3 ρ3 F3 K'' bl B3 hT3 $$ HR with ⟨%hnn3, HR⟩
      icases persistent_entails_left (spSpillR_lens I γd γ W'' txl txid T3 ρ3 F3 K'' bl B3 x rx3 hT3 hx3) $$ HR
        with ⟨HR, %hlx3⟩
      -- the part live in the bucket (the parts loop's live set)
      obtain ⟨S'', hlvS, hokS, hxsS, hparS'', hnvS⟩ :=
        (id hpp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hlv3 : liveNodesX B3 S'' ∧ ∀ l ∈ S'', ∃ r, B3.ns !! l = some r ∧ derefOK bl r := by
        rcases hBx3 with hB3e | ⟨hB3e, -⟩
        · rw [hB3e]
          refine liveNodesX_setN bl B'' S'' x rx rx3 hlvS hokS hrx (by rw [hrx3]) (by rw [hrx3])
            (fun h => ?_) (fun h => by rw [hrx3]; exact h)
          rw [hrx3]
          refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
          rcases h.2.2.2 with h' | ⟨h1, -⟩
          · exact Or.inl h'
          · exact Or.inr ⟨h1, Or.inl rfl⟩
        · rw [hB3e]; exact ⟨hlvS, hokS⟩
      have hxS : x ∈ S'' := hxsS (sint.nat iv) x hxj
      have hnv3 : ∀ l r, B3.ns !! l = some r → l ∉ S'' → noViewRec r := by
        intro l r hl hlS
        have hlx : l ≠ x := fun e => hlS (e ▸ hxS)
        rw [hoth l hlx] at hl; exact hnvS l r hl hlS
      have hrn3 : B3.bv.rootNode' ≠ null := by
        obtain ⟨p, top, hup, -⟩ := hlv3.1
        obtain ⟨r0, hr0⟩ := spUpPath_head _ hup
        exact hnn3 _ r0 hr0
      icases spSpillR_nodeIns I γd γ W'' txl txid T3 ρ3 F3 K'' bl B3 x rx3 hT3 hx3 $$ HR
        with ⟨Hxn, Hxi, Hxback⟩
      try wp_auto
      wp_apply hSize x rx3.nv (DFrac.own 1) rx3.ins (DFrac.own 1) $$ [Hxn Hxi] as ⟨Hxn, Hxi⟩
      · iframe
      ihave HR := Hxback $$ Hxn Hxi
      have hdb3 : T3.t.db' = W''.dbl := hg3.2.2.2.2.2.2.2.1
      icases spSpillR_dbps I γd γ W'' txl txid T3 ρ3 F3 K'' hdb3 $$ HR with ⟨Hdbf, #Hps, Hdbback⟩
      try wp_auto
      ihave HR := Hdbback $$ Hdbf
      -- the part's pages: its layout fits (the split's `split_fit`)
      obtain ⟨xe, hxe, hxe1⟩ : ∃ xe, xs[sint.nat iv]? = some xe ∧ xe.1 = x := by
        cases h : xs[sint.nat iv]? with
        | none => rw [h] at hxj; cases hxj
        | some xe => rw [h] at hxj; cases hxj; exact ⟨xe, rfl, rfl⟩
      obtain ⟨hwsx, hlivex, hilx, hxl, hmemx⟩ := spCurPart bl n rc xs par Bs ws0 i0 hst.2.1 hilR hliveR (sint.nat iv)
        xe hxe rs rx (by rw [hxe1]; exact hrs) hdnk
      have hlay3 : layoutOf rx3.ins ≤ 2147483647 ∧ 16 ≤ layoutOf rx3.ins := by
        have hws3 : rx3.ws = rx.ws := by rw [hrx3]
        have hins3 : rx3.ins.length = rx3.ws.length := by rw [hrx3]; exact hilx
        have heq := spLayout_eq rx3.ins rx3.ws hins3 (fun i it w h1 h2 => by
          have h := hlx3 i it w h1 h2
          have hw := hlivex w (by rw [← hws3]; exact List.mem_of_getElem? h2)
          exact ⟨h.1 hw.1, h.2 hw.2⟩)
        have := layoutOf_ge rx3.ins
        refine ⟨?_, by omega⟩
        rw [heq, ← spLayoutW_fresh, hws3, hwsx, spLayoutW_fresh]
        exact (hlay _ xe hxe).1
      have hlayEq : layoutOf rx3.ins = spLayoutW rx3.ws := by
        have hws3 : rx3.ws = rx.ws := by rw [hrx3]
        have hins3 : rx3.ins.length = rx3.ws.length := by rw [hrx3]; exact hilx
        exact spLayout_eq rx3.ins rx3.ws hins3 (fun i it w h1 h2 => by
          have h := hlx3 i it w h1 h2
          have hw := hlivex w (by rw [← hws3]; exact List.mem_of_getElem? h2)
          exact ⟨h.1 hw.1, h.2 hw.2⟩)
      have hsz : uint.nat (sizeFrom (W64 16) (W64 16) rx3.ins) = layoutOf rx3.ins := by
        have h16 : uint.nat (W64 16) = 16 := rfl
        rw [spSizeFrom_nat rx3.ins (W64 16) (by rw [h16]; unfold layoutOf at hlay3; omega), h16]; rfl
      obtain ⟨hcnt0, hcnt1, hcnt2, hcnt3⟩ := spCount_bounds (sizeFrom (W64 16) (W64 16) rx3.ins) W''.ps _ hsz
        hlay3.2 hlay3.1 (by have := hpp.1.1.2.1; omega) (by rw [hpp.2.2.2.2.1, hWps]; exact hps)
      generalize hcn : BitVec.sdiv (sizeFrom (W64 16) (W64 16) rx3.ins + W64 (W''.ps : Int) - W64 1)
        (W64 (W''.ps : Int)) = cnt at hcnt0 hcnt1 hcnt2 hcnt3 ⊢
      wp_apply (spill_alloc hAlloc I γd γ W'' txl txid T3 ρ3 F3 K'' _ hg3 hcnt0 hcnt1 hcnt2) $$ [HR]
        as %pp %err Hres
      · iframe
      icases Hres with (⟨%he, %data', %T0, %T4, %ρ4, %id, %st4, HR, Htok, %ha⟩ | ⟨%he, Herr⟩)
      · subst he
        obtain ⟨hg4, hT0, hT4, hmv0, hbuf0, hpm0, hpmid, hwid, hid2, hidc, hmvle, hpcar⟩ := ha
        try wp_auto
        -- the part after the allocation (possibly dereferenced)
        obtain ⟨B4, rx4, hB4', hx4, hdn4, hlv4, hok4, hbv4, hib4, hnm4, hbm4, hdn4all, hfw4, hnv4⟩ :=
          spAllocPart bl x T3 T0 B3 rx3 S'' hT3 hx3 hT0 hlv3.1 hlv3.2 hxS hrn3 hnv3
        have hB4 : T4.bs !! bl = some B4 := by rw [hT4]; exact hB4'
        have hcpos : 0 < uint.nat cnt := by unfold uint.nat; have := hcnt0; word
        have hc32 : uint.nat cnt ≤ 2 ^ 32 := by unfold uint.nat; have := hcnt0; have := hcnt1; word
        obtain ⟨hfl, hfid, hfd⟩ := freshPage_facts id (uint.nat cnt) W''.ps hcpos hc32 (by have := hpp.1.1.2.1; omega)
        obtain ⟨hpo1, hpo2, hpo3⟩ := spFresh_pageOf id (uint.nat cnt) W''.ps hcpos hc32 (by have := hpp.1.1.2.1; omega)
        have hpm4 : T4.pm !! id = some pp := by rw [hT4]; exact GMap.lookup_insert _ _ _
        have hbf4 : T4.bufs !! id = some (freshPage id (uint.nat cnt) W''.ps) := by rw [hT4]; exact GMap.lookup_insert _ _ _
        icases (spillR_at I γd γ _ txl txid T4 ρ4 F3 K'' bl B4 hB4).1 $$ HR
          with ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
        have h16f : 16 ≤ (freshPage id (uint.nat cnt) W''.ps).length := by
          rw [hfl]; have := hpp.1.1.2.1
          exact Nat.le_trans (by omega : 16 ≤ W''.ps) (Nat.le_mul_of_pos_left _ hcpos)
        icases spBufsHdr T4 id pp _ hpm4 hbf4 h16f hpcar $$ Hbufs
          with ⟨Hhd, Hrest, Hbufsback⟩
        ihave #Hcom : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
        · iPkgInit
        wp_apply hId pp _ (DFrac.own 1) $$ [Hhd] as Hhd
        · iframe
        isimp only [TxW_rest_root] at Ht
        icases Ht with ⟨Hwr, Hman, Hdbf, Hmet, Hpgs, Hsts, Hchs, Hwf2, %Htn⟩
        try wp_auto
        wp_apply hPgid T4.t.meta' T4.mv (DFrac.own 1) $$ [Hm] as Hm
        · iframe
        have hlt4 : ¬ uint.Z T4.mv.pgid' ≤ uint.Z (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) := by
          rw [hfid]; have h1 := hidc; have h2 := hcpos; unfold uint.nat at h1 h2; word
        rw [decide_eq_false hlt4]
        try wp_auto
        wp_apply hId pp _ (DFrac.own 1) $$ [Hhd] as Hhd
        · iframe
        isimp only [bktOwnX] at Hb
        icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) _ l r)
          (show Std.get? B4.ns x = some rx4 from hx4)).1 $$ Hns with ⟨Hxo, Hns⟩
        isimp only [nodeOwnX] at Hxo
        icases Hxo with ⟨Hxn, Hxi, Hxe, Hxch, Hxcc, Hxk⟩
        try wp_auto
        isimp only [wView] at Hv
        icases Hv with ⟨Hd, #Hps, #Hlg, Hfl, #Hdl, %Hlgv, Hpv⟩
        obtain ⟨hlv4f, hil4f, hws4f, hnv4f, -, -, hwl4f, -, -⟩ := spDnK_facts rx3 rx4 hdn4
        have hws3 : rx3.ws = rx.ws := by rw [hrx3]
        have hlive4 : wsLive rx4.ws := hlv4f (by rw [hws3]; exact hlivex)
        have hil4 : rx4.ins.length = rx4.ws.length := hil4f (by rw [hrx3]; exact hilx)
        have hlen4 : rx4.ins.length = (borrowEs rx4.ws ({ W'' with data := data' } : WView).q).length := by
          rw [spBorrowEs_length]; exact hil4
        have hwsc : rx4.ws.map ownFresh = ((chunksOf rc xs).getD (sint.nat iv) []).map ownFresh := by
          rw [hws4f, hws3, hwsx]
        have hlay4e : spLayoutW rx4.ws = layoutOf rx3.ins := by
          rw [hlayEq, ← spLayoutW_fresh rx4.ws, hws4f, spLayoutW_fresh]
        have hlay4 : spLayoutW rx4.ws ≤ 2147483647 := by rw [hlay4e]; exact hlay3.1
        have hlen65 : rx4.ins.length < 65535 := by rw [hil4, hwl4f, hws3, hxl]; exact (hlay _ xe hxe).2
        obtain ⟨hbk, hbvv⟩ := spBorrowEs_kv rx4.ws ({ W'' with data := data' } : WView).q
        have hkpos : ∀ k ∈ rx4.ws.map WEntry.key, 0 < k.length := by
          intro k hk
          rw [← spFresh_key, hwsc, spFresh_key] at hk
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
          have hw' : w ∈ rn.ws := by have := hmemx w hw; rw [← hrc] at this; exact this
          exact (hl17.2.2.2.2.1 w hw').1
        have hcp : layoutOf rx3.ins ≤ uint.nat cnt * W''.ps := by
          have e : ((uint.nat cnt : Nat) : Int) = sint.Z cnt := by
            unfold uint.nat; have := hcnt0; have := hcnt1; word
          have h := hcnt3
          rw [← e, ← Int.natCast_mul] at h
          omega
        icases persistent_entails_left (spWOwns_fp _ rx4.ins rx4.ws) $$ Hxe with ⟨Hxe, %hfp4⟩
        icases nodeBorrowD _ hg4.1.1 rx4.ws rx4.ins _ hlive4 $$ [Hpv Hxe] with ⟨Hio, Hioback⟩
        · iframe
        icases spInodesOwn_dataF rx4.ins _ hlen4 $$ Hio with ⟨Hdat, Hdatback⟩
        wp_apply hWrite x
          ({ rx4.nv with pgid' := W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int) } : node)
          (DFrac.own 1) rx4.ins (DFrac.own 1)
          ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.key)
          ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.value) _ _ pp
          (pageOf (freshPage id (uint.nat cnt) W''.ps)) ((freshPage id (uint.nat cnt) W''.ps).drop 16) hpcar
          (by rw [hpo3]) (by rw [hpo2]) hlen65 (by rw [hbk, List.length_map, hil4])
          (by rw [hbvv, List.length_map, hil4])
          (by rw [hbk]; intro i hi; exact spGetD_pos _ hkpos i (by rw [List.length_map, ← hil4]; exact hi))
          (by rw [hbk, hbvv, hil4, spKvLen]; unfold spLayoutW at hlay4; omega)
          (by
            rw [hbk, hbvv, hil4, spKvLen, List.length_drop, hfl]
            have h1 := hlay4e; have h2 := hcp; unfold spLayoutW at h1
            generalize uint.nat cnt * W''.ps = m at h2 ⊢
            omega)
          (fun hbr => by
            rw [hpo1]
            have hb4 : rx4.nv.isLeaf' = false := hbr
            have hl4 : rx4.nv.isLeaf' = rx.nv.isLeaf' := by rw [hnv4f, hrx3]
            have hl : rc.nv.isLeaf' = false := by
              rw [← spCurPartLeaf bl n rc _ xs par Bs ws0 i0 _ _ _ Ts Ks hst.2.1 hst.2.2.2.2 (sint.nat iv) xe
                hxe rs rx (by rw [hxe1]; exact hrs) hdnk, ← hl4]
              exact hb4
            refine spBranchPgids rx4.ins rx4.ws ((chunksOf rc xs).getD (sint.nat iv) []) id hfp4 hil4 hwsc
              (fun w hw => ?_)
            have hwr : w ∈ rn.ws := by have := hmemx w hw; rw [← hrc] at this; exact this
            have hrnb : rn.nv.isLeaf' = false := by
              have e : rc.nv.isLeaf' = rn.nv.isLeaf' := by rw [← hrc]
              rw [← e]; exact hl
            have hin := hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2 n rn w hlp.2.2.1 hrnb hwr
            have hsub : spillPages W' T' ⊆ spillPages W'' T3 := by
              have e : spillPages W'' T3 = spillPages W'' T'' := by unfold spillPages; rw [hbuf3]
              rw [e, ← hPs]; exact hpp.2.2.2.2.2.1
            obtain ⟨pg', hpg'⟩ := Option.isSome_iff_exists.1 hin
            have hpg3 := GMap.lookup_weaken hpg' hsub
            have hbn : T3.bufs !! id = none := by
              have h := hg3.2.2.2.2.2.2.2.2.2.2.1.1 id
              rw [hpmid] at h
              cases hb : T3.bufs !! id with
              | none => rfl
              | some b => rw [hb] at h; exact absurd (h.2 rfl) (by simp)
            have hnone := spillPages_none W'' T3 id hwid hbn
            intro e; rw [e, hnone] at hpg3; cases hpg3)
          $$ [Hxn Hxi Hdat Hhd Hrest] as ⟨Hxn, Hxi, Hdat, Hhd, Hrest⟩
        · iframe
        try wp_auto
        -- close the state: the borrowed bytes back, the page written, the part spilled
        ihave Hio := Hdatback $$ Hdat
        icases Hioback $$ Hio with ⟨Hpv, Hxe⟩
        ihave Hbufs := Hbufsback $$ %_ %_ Hhd Hrest
        icases spName_eq (fun b => bufsOwn (GF := GF) { T4 with bufs := <[id := b]> T4.bufs }) _ $$ Hbufs
          with ⟨%wb, %hwb, Hbufs⟩
        obtain ⟨rx5, hrx5⟩ : ∃ r : NRec, r = { rx4 with nv := { rx4.nv with
            pgid' := W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), spilled' := true } } :=
          ⟨_, rfl⟩
        have hB5 : (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).bs !! bl =
            some (setN B4 x rx5) := GMap.lookup_insert _ _ _
        ihave HR := (spillR_at I γd γ { W'' with data := data' } txl txid
          (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) ρ4 F3 K'' bl _ hB5).2 $$
          [Hdb Hd Hfl Hpv Hwr Hman Hdbf Hmet Hpgs Hsts Hchs Hwf2 Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns
            Hxn Hxi Hxe Hxch Hxcc Hxk Hc Ho Hg HF]
        · have e2 : ghostOK (GF := GF) γ { W'' with data := data' }
              (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) =
              ghostOK γ { W'' with data := data' } { T4 with bufs := <[id := wb]> T4.bufs } := rfl
          have e3 : othersOwn (GF := GF) { W'' with data := data' }
              (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).bs bl K'' =
              othersOwn { W'' with data := data' } T4.bs bl K'' := othersOwn_insert _ T4.bs bl _ K''
          have e1 : bufsOwn (GF := GF) (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) =
              bufsOwn { T4 with bufs := <[id := wb]> T4.bufs } := rfl
          rw [e1, e2, e3]
          ihave Hg := spGhostOK_write γ _ T4 id _ wb hbf4 $$ Hg
          dsimp only [setB]
          iframe Hdb Hm Hpm Hbufs Ho Hg HF
          isplitl [Hd Hfl Hpv]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          isplitl [Hwr Hman Hdbf Hmet Hpgs Hsts Hchs Hwf2]
          · unfold TxW_rest_root; iframe; ipureintro; exact Htn
          isplitl [Hbv Hib Hnm Hbm Hpo Hns Hxn Hxi Hxe Hxch Hxcc Hxk]
          · unfold bktOwnX setN
            rw [show pageOwn { W'' with data := data' } { B4 with ns := <[x := rx5]> B4.ns } =
              pageOwn { W'' with data := data' } B4 from rfl]
            iframe Hbv Hib Hnm Hbm Hpo
            iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B4.ns) (i := x)
              (x := rx5) (Φ := fun l r => nodeOwnX (GF := GF) { W'' with data := data' } l r)).2
            iframe Hns
            unfold nodeOwnX
            rw [hrx5]
            iframe
          · unfold capsB setN
            icases (BigSepM.bigSepM_delete (M := GMap Loc)
              (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)
              (show Std.get? B4.ns x = some rx4 from hx4)).1 $$ Hc with ⟨Hcn, Hc⟩
            iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := B4.ns) (i := x)
              (x := rx5) (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)).2
            rw [hrx5]
            iframe
        have hkx := spCurPartKey bl n rc xs par Bs ws0 i0 hst.2.1 (sint.nat iv) xe hxe rs rx
          (by rw [hxe1]; exact hrs) hdnk (by rw [← hrc]; exact hl17.2.2.2.2.2.2.1)
        obtain ⟨-, -, -, -, -, hkey4, -, hks4, hkn4⟩ := spDnK_facts rx3 rx4 hdn4
        have hk5 : rx5.nv.key' ≠ slice.nil → 0 < rx5.key.length ∧ rx5.ksrc ≠ Src.stale := fun h => by
          have h4 : rx4.nv.key' ≠ slice.nil := by rw [hrx5] at h; exact h
          have h3 : rx3.nv.key' ≠ slice.nil := fun e => h4 (hkn4 e)
          have hx' : rx.nv.key' ≠ slice.nil := by rw [hrx3] at h3; exact h3
          obtain ⟨a, b⟩ := hkx hx'
          rw [hrx5]
          exact ⟨by rw [hkey4, hrx3]; exact a, hks4 (by rw [hrx3]; exact b)⟩
        have hd4 : derefOK bl rx4 := by
          obtain ⟨r, hr, hd⟩ := hok4 x hxS; rw [hx4] at hr; cases hr; exact hd
        have h5 : rx5.ins.length = rx5.ws.length := by rw [hrx5]; exact hil4
        have hd5 : derefOK bl rx5 := by
          obtain ⟨d1, -, d3, -⟩ := hd4
          refine ⟨by rw [hrx5]; exact d1, h5, by rw [hrx5]; exact d3, ?_⟩
          by_cases hkn : rx5.nv.key' = slice.nil
          · exact Or.inl hkn
          · exact Or.inr ⟨(hk5 hkn).2, Or.inr (hk5 hkn).1⟩
        -- the part written: its page's length, id and overflow kept
        have hwok : writeOK ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.key)
            ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.value) rx4.ins :=
          ⟨hlen65, by rw [hbk, List.length_map, hil4], by rw [hbvv, List.length_map, hil4],
            by rw [hbk]; intro i hi; exact spGetD_pos _ hkpos i (by rw [List.length_map, ← hil4]; exact hi),
            by rw [hbk, hbvv, hil4, spKvLen]; unfold spLayoutW at hlay4; omega⟩
        have hroom : 16 * rx4.ins.length + kvLen
            ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.key)
            ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.value) rx4.ins.length ≤
            ((freshPage id (uint.nat cnt) W''.ps).drop 16).length := by
          rw [hbk, hbvv, hil4, spKvLen, List.length_drop, hfl]
          have h1 := hlay4e; have h2 := hcp; unfold spLayoutW at h1
          generalize uint.nat cnt * W''.ps = m at h2 ⊢
          omega
        have hwbe : wb = writtenPage (pageOf (freshPage id (uint.nat cnt) W''.ps)) rx4.nv.isLeaf'
            ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.key)
            ((borrowEs rx4.ws ({ W'' with data := data' } : WView).q).map NodeEntry.value) rx4.ins
            ((freshPage id (uint.nat cnt) W''.ps).drop 16) := by rw [hwb]; rfl
        obtain ⟨-, hwl, hwid', -, -, hwov, -⟩ := writtenPage_facts (pageOf (freshPage id (uint.nat cnt) W''.ps))
          rx4.nv.isLeaf' _ _ rx4.ins ((freshPage id (uint.nat cnt) W''.ps).drop 16) hwok
        have hwlen : wb.length = (freshPage id (uint.nat cnt) W''.ps).length := by
          rw [hwbe, hwl]; have := hroom; rw [List.length_drop] at this ⊢; omega
        have hwpid : pageId wb = pageId (freshPage id (uint.nat cnt) W''.ps) := by
          rw [hwbe, hwid']
          show uint.nat (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) = _
          rw [hfid]; unfold uint.nat; word
        have hwpov : pageOverflow wb = pageOverflow (freshPage id (uint.nat cnt) W''.ps) := by
          rw [hwbe, hwov]
          show uint.nat (W32 ((pageOverflow (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) = _
          have := rb_pageOverflow_lt (freshPage id (uint.nat cnt) W''.ps)
          unfold uint.nat; word
        have hg5 : spillG (hG := hG) { W'' with data := data' } txl txid
            (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) ρ4 F3 := by
          have hgw := spSpillG_write _ txl txid T4 ρ4 F3 id _ wb hg4 hbf4 hwlen hwpid hwpov
          refine spSpillG_setN _ txl txid _ ρ4 F3 bl B4 x rx4 rx5 hgw hB4 hx4 (by rw [hrx5]) (by rw [hrx5])
            (fun h => by rw [hrx5]; exact h) (fun h => ?_)
          by_cases hkn : rx5.nv.key' = slice.nil
          · rw [hrx5] at hkn ⊢; exact ⟨h.1, h.2.1, h.2.2.1, Or.inl hkn⟩
          · obtain ⟨a, b⟩ := hk5 hkn
            rw [hrx5] at a b ⊢; exact ⟨h.1, h.2.1, h.2.2.1, Or.inr ⟨b, Or.inr a⟩⟩
        wp_join iprop(∃ (T6 : WTx) (B6 : BRec),
            "HR" ∷ spillR I γd γ { W'' with data := data' } txl txid T6 ρ4 F3 K'' ∗
            "tx" ∷ tx_ptr ↦ txl ∗ "node" ∷ node_ptr ↦ x ∗
            "%Hj" ∷ ⌜T6.bs !! bl = some B6 ∧ spillG (hG := hG) { W'' with data := data' } txl txid T6 ρ4 F3 ∧
              spillFrame (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) T6 (· = bl) ∧
              T6.bufs = <[id := wb]> T4.bufs ∧ T6.pm = T4.pm ∧ T6.mv = T4.mv ∧
              (rx4.nv.parent' = null → B6 = setN B4 x rx5) ∧
              (rx4.nv.parent' ≠ null → spParentPut x rx4.nv.parent'
                (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) (setN B4 x rx5) B6) ∧
              liveNodesX B6 S'' ∧ (∀ l ∈ S'', ∃ r, B6.ns !! l = some r ∧ derefOK bl r) ∧
              (∀ l r, B6.ns !! l = some r → l ∉ S'' → noViewRec r)⌝)
          with [HR tx node]
        · -- no parent
          have hp0 : rx4.nv.parent' = null := by simpa using Hif
          iexists _, _
          iframe
          ipureintro
          have hlv5 := liveNodesX_setN_in bl B4 S'' x rx4 rx5 hlv4 hok4 hx4 hxS (by rw [hrx5]) (by rw [hrx5]) hd5
          refine ⟨hB5, hg5, spillFrame_reflN _ _, rfl, rfl, rfl, fun _ => rfl, fun h => absurd hp0 h, hlv5.1,
            hlv5.2, fun l r hl hlS => ?_⟩
          have hlx : l ≠ x := fun e => hlS (e ▸ hxS)
          have e : (setN B4 x rx5).ns !! l = B4.ns !! l := GMap.lookup_insert_ne _ _ (Ne.symm hlx)
          rw [e] at hl; exact hnv4 l r hl hlS
        · -- a parent: the part put into it, the part's key set
          have hpar : rx4.nv.parent' ≠ null := Hif
          obtain ⟨hnvx, hpxe⟩ := spCurPartNv bl n rc xs par Bs ws0 i0 hst.2.1 (sint.nat iv) xe hxe rs rx
            (by rw [hxe1]; exact hrs) hdnk
          have hparx : rx4.nv.parent' = par := by
            have e : rx4.nv.parent' = rx.nv.parent' := by rw [hnv4f, hrx3]
            rw [e, hnvx]; exact hpxe
          have hparn : par ≠ null := by rw [← hparx]; exact hpar
          obtain ⟨rpq, hrpq, hKq, -, hlq, hilq, hsq, hbq, hnotq, -⟩ := hpp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparn
          have hpx' : par ≠ x := fun e => hnotq (by
            rw [e, ← hxe1]; exact List.mem_map_of_mem (List.mem_of_getElem? hxe))
          have hr3 : B3.ns !! par = some rpq := by rw [hoth par hpx', hrpq]
          obtain ⟨rp4, hrp4, -⟩ := hok4 par (hparS'' hparn)
          obtain ⟨r3, hr3', hdnp⟩ := hdn4all par rp4 hrp4
          rw [hr3] at hr3'; cases hr3'
          obtain ⟨hlp4, hilp4, hsp4, hbp4⟩ := spDnK_par bl _ rp4 hdnp hlq hilq hsq hbq
          obtain ⟨rp, hrp, hpx, hKp, hrpb, hrpl, hrpL, hrps⟩ : ∃ rp, (setN B4 x rx5).ns !! rx4.nv.parent' = some rp ∧
              rx4.nv.parent' ≠ x ∧ K'' rx4.nv.parent' = false ∧ rp.nv.bucket' = bl ∧
              rp.ins.length = rp.ws.length ∧ wsLive rp.ws ∧ wsSorted rp.ws := by
            rw [hparx]
            refine ⟨rp4, ?_, hpx', hKq, hbp4, hilp4, hlp4, hsp4⟩
            show (<[x := rx5]> B4.ns) !! par = some rp4
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hpx')]; exact hrp4
          have hx5 : (setN B4 x rx5).ns !! x = some rx5 := GMap.lookup_insert _ _ _
          have hrpd : Std.get? (Std.delete (setN B4 x rx5).ns x) rx4.nv.parent' = some rp := by
            show (GMap.delete x (setN B4 x rx5).ns) !! _ = some rp
            rw [GMap.lookup_delete_ne _ (Ne.symm hpx)]; exact hrp
          icases (spillR_at I γd γ { W'' with data := data' } txl txid
            (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) ρ4 F3 K'' bl _ hB5).1 $$ HR
            with ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
          isimp only [bktOwnX] at Hb
          icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
          icases (BigSepM.bigSepM_delete (M := GMap Loc)
            (Φ := fun l r => nodeOwnX (GF := GF) { W'' with data := data' } l r)
            (show Std.get? (setN B4 x rx5).ns x = some rx5 from hx5)).1 $$ Hns with ⟨Hxo, Hns⟩
          icases (BigSepM.bigSepM_delete (M := GMap Loc)
            (Φ := fun l r => nodeOwnX (GF := GF) { W'' with data := data' } l r) hrpd).1 $$ Hns
            with ⟨Hpo', Hns⟩
          isimp only [nodeOwnX] at Hxo
          icases Hxo with ⟨Hxn, Hxi, Hxe, Hxch, Hxcc, Hxk⟩
          isimp only [nodeOwnX] at Hpo'
          icases Hpo' with ⟨Hpn, Hpi, Hpe, Hpch, Hpcc, Hpk⟩
          try wp_auto
          have hrcne : rc.nv.parent' ≠ null → 0 < rc.ws.length := fun h => by
            have e1 : rc.ws = rn.ws := by rw [← hrc]
            have e2 : rc.nv.parent' = rn.nv.parent' := by rw [← hrc]
            rw [e1]; exact hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 n rn hlp.2.2.1 (by rw [← e2]; exact h)
          have hl0 : 0 < rx5.ins.length := by
            rw [hrx5]; show 0 < rx4.ins.length
            rw [hil4, hwl4f, hws3, hxl]
            exact spPartNonempty bl n rc _ xs _ _ _ Ts Bs Ks par hst.2.2.2.2 hilR hrcne xe
              (List.mem_of_getElem? hxe) (by rw [hpxe]; exact hparn)
          obtain ⟨it0, hit0⟩ : ∃ it, rx5.ins[0]? = some it := ⟨_, List.getElem?_eq_getElem hl0⟩
          ihave %Hxl := ownSlice_len _ _ _ $$ Hxi
          wp_join iprop(∃ (k : GoSlice), "key" ∷ key_ptr ↦ k ∗ "Hxn" ∷ x ↦ rx5.nv ∗
              "Hxi" ∷ rx5.nv.inodes' ↦* rx5.ins ∗ "node" ∷ node_ptr ↦ x ∗
              "%Hk" ∷ ⌜k = if rx5.nv.key' = slice.nil then it0.key' else rx5.nv.key'⌝)
            with [key Hxn Hxi node]
          · icases ownSlice_elem_acc 0 it0 rx5.nv.inodes' (DFrac.own 1) rx5.ins (by decide)
              (by simpa using hit0) $$ Hxi with ⟨Hit, Hitback⟩
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
              sint.Z (W64 0) < sint.Z rx5.nv.inodes'.len from
              ⟨by decide, by have := Hxl.1; have := Hxl.2; have := hl0; word⟩)),
              show sint.Z (W64 0) = 0 from rfl]
            try wp_auto
            wp_apply hKey (sliceIndexRef Inode 0 rx5.nv.inodes') it0 (DFrac.own 1) $$ [Hit] as Hit
            · iframe
            try wp_auto
            ihave Hxi := Hitback $$ Hit
            rw [list_set_lookup_self _ _ it0 (by simpa using hit0)]
            isplitr
            · ipureintro; rfl
            iexists it0.key'
            iframe
            ipureintro
            rw [if_pos Hif]
          · iexists rx5.nv.key'
            iframe
            ipureintro
            rw [if_neg Hif]
          iintro ⟨%k, key, Hxn, Hxi, node, %Hk⟩
          try wp_auto
          icases ownSlice_elem_acc 0 it0 rx5.nv.inodes' (DFrac.own 1) rx5.ins (by decide)
            (by simpa using hit0) $$ Hxi with ⟨Hit, Hitback⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
            sint.Z (W64 0) < sint.Z rx5.nv.inodes'.len from
            ⟨by decide, by have := Hxl.1; have := Hxl.2; have := hl0; word⟩)),
            show sint.Z (W64 0) = 0 from rfl]
          try wp_auto
          wp_apply hKey (sliceIndexRef Inode 0 rx5.nv.inodes') it0 (DFrac.own 1) $$ [Hit] as Hit
          · iframe
          try wp_auto
          -- the put: what it reads lent
          have hc5 : ({ W'' with data := data' } : WView).data.locCar ≠ 0 := hg5.1.1
          have h5 : rx5.ins.length = rx5.ws.length := by rw [hrx5]; exact hil4
          obtain ⟨w0, hw0⟩ : ∃ w, rx5.ws[0]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hw04 : rx4.ws[0]? = some w0 := by rw [hrx5] at hw0; exact hw0
          have hw0s : w0.ks ≠ Src.stale := (hlive4 w0 (List.mem_of_getElem? hw04)).1
          have hos : ¬ rx5.nv.key' = slice.nil → rx5.ksrc ≠ Src.stale := fun h => (hk5 h).2
          isimp only [wView] at Hv
          icases Hv with ⟨Hd, #Hps5, #Hlg5, Hfl, #Hdl5, %Hlgv, Hpv⟩
          icases spPut_lend { W'' with data := data' } hc5 rx5.ins rx5.ws it0 w0 hit0 hw0 hw0s rp.ins rp.ws
            hrpL hrpl rx5.nv.key' rx5.ksrc rx5.key (rx5.nv.key' = slice.nil) hos $$ [Hpv Hxe Hpe Hxk]
            with ⟨%es, %s1, %s2, %s3, %dnk, %dok, %hlend, Hes, Hnk, Hok, Hlback⟩
          · iframe
          have hroot5 : ((setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).bs !!
              structFieldRef Tx go!"root" txl).isSome := hg5.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          icases spTx_halves { W'' with data := data' } txl bl _ K'' _ _ hroot5 $$ [Hbv Ho Ht]
            with ⟨%rv, Htx, Hbv1, Htxback⟩
          · iframe
          isimp only [capsB] at Hc
          icases (BigSepM.bigSepM_delete (M := GMap Loc)
            (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)
            (show Std.get? (setN B4 x rx5).ns rx4.nv.parent' = some rp from hrp)).1 $$ Hc with ⟨Hpcap, Hc⟩
          isimp only [hKp, Bool.false_eq_true, ↓reduceIte, capOwn] at Hpcap
          have htx5 : (setN B4 x rx5).bv.tx' = txl := by
            show B4.bv.tx' = txl
            rw [hbv4, hbv3, hpp.2.2.2.2.2.2.1, hst.2.2.2.1.1, hB3bv]; exact htx
          have hpgl : uint.Z rx5.nv.pgid' < uint.Z T4.mv.pgid' := by
            rw [hrx5]
            show uint.Z (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) < uint.Z T4.mv.pgid'
            omega
          have hnkl : 0 < w0.key.length :=
            hkpos w0.key (List.mem_map_of_mem (List.mem_of_getElem? hw04))
          have hokl : 0 < (if rx5.nv.key' = slice.nil then w0.key else rx5.key).length := by
            split
            · exact hnkl
            · exact (hk5 ‹_›).1
          have hpp5 : rx5.nv.parent' = rx4.nv.parent' := by rw [hrx5]
          subst Hk
          wp_apply hPut rx5.nv.parent' rp.nv rp.ins es (setN B4 x rx5).bv (DFrac.own halfQ)
            ({ T4.t with root' := rv } : Tx) (DFrac.own halfQ) T4.mv (DFrac.own 1)
            _ _ dok it0.key' w0.key dnk slice.nil [] (DFrac.own 1) rx5.nv.pgid' (W32 0)
            ((wMatch_sorted _ _ hlend.1).2 hrps) hpgl hokl hnkl
            $$ [Hpn Hpi Hpcap Hes Hbv1 Htx Hm Hok Hnk]
            as %idx %s' ⟨%Hidx, Hbv1, Htx, Hm, Hok, Hpn, Hs', Hscap, Hes, Hold⟩
          · rw [hrpb, htx5, hpp5]
            iframe
            iapply ownSlice_nil
          try wp_auto
          -- the lent back: the parent's entries with the part's, the part's first key shared
          have hil : rp.ins.length = es.length := hrpl.trans (wMatch_length hlend.1)
          ihave Hl := Hlback $$ %(sint.nat idx)
            %(decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) =
              (if rx5.nv.key' = slice.nil then w0.key else rx5.key)))
            %rx5.nv.pgid' %(fun h => by rw [hil]; exact (of_decide_eq_true h).1) Hes Hold Hok
          icases Hl with ⟨Hpv, Hxe, Hk3, Hpe⟩
          ihave %Hk3l := spSrcOwn_len _ _ _ _ $$ Hk3
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
            sint.Z (W64 0) < sint.Z rx5.nv.inodes'.len from
            ⟨by decide, by have := Hxl.1; have := Hxl.2; have := hl0; word⟩)),
            show sint.Z (W64 0) = 0 from rfl]
          try wp_auto
          wp_apply hKey (sliceIndexRef Inode 0 rx5.nv.inodes') it0 (DFrac.own 1) $$ [Hit] as Hit
          · iframe
          try wp_auto
          have hk28 : w0.key.length ≤ 2 ^ 28 := by
            have hm : ownFresh w0 ∈ ((chunksOf rc xs).getD (sint.nat iv) []).map ownFresh := by
              rw [← hwsc]; exact List.mem_map_of_mem (List.mem_of_getElem? hw04)
            obtain ⟨c, hc, hce⟩ := List.mem_map.1 hm
            have := helR c (hmemx c hc)
            have hk : c.key = w0.key := by have := congrArg WEntry.key hce; exact this
            rw [← hk]; omega
          have hkpos : sint.Z (W64 0) < sint.Z it0.key'.len := by
            have h1 := Hk3l hlend.2.2.2.1
            have := hnkl
            unfold uint.nat at h1
            word
          rw [decide_eq_true hkpos]
          wp_apply hAssert $$ []
          try wp_auto
          -- close the state: the part's key its first key, the parent's entries with the part's
          ihave Hxi := Hitback $$ Hit
          rw [list_set_lookup_self _ _ it0 (by simpa using hit0)]
          rw [show (setN B4 x rx5).bv = B4.bv from rfl,
            show (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).t = T4.t from rfl]
          have htx4 : B4.bv.tx' = txl := htx5
          rw [htx4]
          ihave Hbv1 : bl ↦{DFrac.own halfQ} B4.bv $$ [Hbv1]
          · rw [← hrpb]; iexact Hbv1
          ihave Hback := Htxback $$ Htx Hbv1
          icases Hback with ⟨Hbv, Ho, Ht⟩
          have hkn6 : it0.key' ≠ slice.nil := by
            intro h; rw [h] at hkpos; exact Int.lt_irrefl _ hkpos
          obtain ⟨bx, hbx⟩ : ∃ b : Bool, b = decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) =
              (if rx5.nv.key' = slice.nil then w0.key else rx5.key)) := ⟨_, rfl⟩
          rw [← hbx]
          obtain ⟨rx6, hrx6⟩ : ∃ r : NRec,
              r = NRec.mk ({ rx5.nv with key' := it0.key' } : node) rx5.ins
                (rx5.ws.set 0 ({ w0 with ks := s1 } : WEntry)) rx5.cs w0.key s3 :=
            ⟨_, rfl⟩
          obtain ⟨rp6, hrp6⟩ : ∃ r : NRec,
              r = NRec.mk ({ rp.nv with inodes' := s' } : node)
                (putList rp.ins (sint.nat idx) bx (Inode.mk (W32 0) rx5.nv.pgid' it0.key' slice.nil))
                (putList rp.ws (sint.nat idx) bx
                  (⟨W32 0, rx5.nv.pgid', w0.key, [], s2, Src.own (DFrac.own 1)⟩ : WEntry)) rp.cs rp.key rp.ksrc :=
            ⟨_, rfl⟩
          ihave Hxo : nodeOwnX (GF := GF) { W'' with data := data' } x rx6 $$ [Hxn Hxi Hxe Hxch Hxcc Hk3]
          · rw [hrx6]; unfold nodeOwnX; dsimp only; rw [if_neg hkn6]; iframe
          ihave Hpo6 : nodeOwnX (GF := GF) { W'' with data := data' } rx4.nv.parent' rp6 $$
              [Hpn Hs' Hpe Hpch Hpcc Hpk]
          · rw [hrp6, hpp5]; unfold nodeOwnX; dsimp only; iframe
          ihave Hns := spBigSepM_ins2 (fun l r => nodeOwnX (GF := GF) { W'' with data := data' } l r)
            (setN B4 x rx5).ns x rx4.nv.parent' rx6 rp6 (Ne.symm hpx) $$ [Hxo Hpo6 Hns]
          · iframe
          have hxc : Std.get? (Std.delete (setN B4 x rx5).ns rx4.nv.parent') x = some rx5 := by
            show (GMap.delete _ (setN B4 x rx5).ns) !! x = some rx5
            rw [GMap.lookup_delete_ne _ hpx]; exact hx5
          icases (BigSepM.bigSepM_delete (M := GMap Loc)
            (Φ := fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r) hxc).1 $$ Hc with ⟨Hxc, Hc⟩
          ihave Hc := spBigSepM_ins2' (fun l r => if K'' l then iprop(emp) else capOwn (GF := GF) r)
            (setN B4 x rx5).ns x rx4.nv.parent' rx6 rp6 (Ne.symm hpx) $$ [Hxc Hscap Hc]
          · rw [hKp, hrx6, hrp6]
            unfold capOwn
            dsimp only
            simp only [Bool.false_eq_true, ↓reduceIte]
            iframe
          rw [show ({ T4.t with root' := rv } : Tx).meta' = T4.t.meta' from rfl]
          have hB6 : (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
              (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)).bs !! bl =
              some (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6) := GMap.lookup_insert _ _ _
          ihave HR := (spillR_at I γd γ { W'' with data := data' } txl txid
            (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
              (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)) ρ4 F3 K'' bl _ hB6).2 $$
            [Hdb Hd Hfl Hpv Ht Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns Hc Ho Hg HF]
          · have e3 : othersOwn (GF := GF) { W'' with data := data' }
                (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                  (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)).bs bl K'' =
                othersOwn { W'' with data := data' }
                  (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).bs bl K'' :=
              othersOwn_insert _ _ bl _ K''
            have eT : (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)).t = T4.t := rfl
            have eM : (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)).mv = T4.mv := rfl
            have eP : (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)).pm = T4.pm := rfl
            have eB : bufsOwn (GF := GF) (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)) =
                bufsOwn (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) := rfl
            have eG : ghostOK (GF := GF) γ { W'' with data := data' }
                (setB (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) bl
                (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6)) =
                ghostOK γ { W'' with data := data' } (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) := rfl
            have eP1 : (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).pm = T4.pm := rfl
            have eM1 : (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)).mv = T4.mv := rfl
            rw [e3, eT, eM, eP, eB, eG, eP1]
            iframe Hdb Hm Hpm Hbufs Ho Hg HF Ht
            isplitl [Hd Hfl Hpv]
            · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
            isplitl [Hbv Hib Hnm Hbm Hpo Hns]
            · unfold bktOwnX
              rw [show pageOwn { W'' with data := data' } (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6) =
                pageOwn { W'' with data := data' } (setN B4 x rx5) from rfl]
              iframe
            · unfold capsB
              iframe
          isplitr
          · ipureintro; rfl
          iexists _, _
          iframe
          ipureintro
          have hparS : rx4.nv.parent' ∈ S'' := by rw [hparx]; exact hparS'' hparn
          have hd4 : derefOK bl rx4 := by
            obtain ⟨r, hr, hd⟩ := hok4 x hxS; rw [hx4] at hr; cases hr; exact hd
          have hd5 : derefOK bl rx5 := by
            obtain ⟨d1, -, d3, -⟩ := hd4
            refine ⟨by rw [hrx5]; exact d1, h5, by rw [hrx5]; exact d3, ?_⟩
            by_cases hkn : rx5.nv.key' = slice.nil
            · exact Or.inl hkn
            · exact Or.inr ⟨(hk5 hkn).2, Or.inr (hk5 hkn).1⟩
          have hrp4' : B4.ns !! rx4.nv.parent' = some rp := by
            have h := hrp
            rw [show (setN B4 x rx5).ns !! rx4.nv.parent' = B4.ns !! rx4.nv.parent' from
              GMap.lookup_insert_ne _ _ (Ne.symm hpx)] at h
            exact h
          have hdp : derefOK bl rp := by
            obtain ⟨r, hr, hd⟩ := hok4 _ hparS; rw [hrp4'] at hr; cases hr; exact hd
          have hw0v : w0.vs ≠ Src.stale := (hlive4 w0 (List.mem_of_getElem? hw04)).2
          have hd6 : derefOK bl rx6 := by
            rw [hrx6]
            exact spDerefOK_set0 bl rx5 hd5 it0.key' ({ w0 with ks := s1 } : WEntry) ⟨hlend.2.1, hw0v, hnkl⟩ w0.key hnkl s3 hlend.2.2.2.1
          have hdp6 : derefOK bl rp6 := by
            rw [hrp6]
            exact spDerefOK_put bl rp hdp s' _ bx _ _ ⟨hlend.2.2.1, nofun, hnkl⟩
          have hlv5 := liveNodesX_setN_in bl B4 S'' x rx4 rx5 hlv4 hok4 hx4 hxS (by rw [hrx5]) (by rw [hrx5]) hd5
          have hlv5p := liveNodesX_setN_in bl (setN B4 x rx5) S'' rx4.nv.parent' rp rp6 hlv5.1 hlv5.2 hrp hparS
            (by rw [hrp6]) (by rw [hrp6]) hdp6
          have hx5p : (setN (setN B4 x rx5) rx4.nv.parent' rp6).ns !! x = some rx5 := by
            show (<[rx4.nv.parent' := rp6]> (setN B4 x rx5).ns) !! x = some rx5
            rw [GMap.lookup_insert_ne _ _ hpx]; exact hx5
          have hlv6 := liveNodesX_setN_in bl _ S'' x rx5 rx6 hlv5p.1 hlv5p.2 hx5p hxS (by rw [hrx6]) (by rw [hrx6]) hd6
          have hg6' := spillG_setB { W'' with data := data' } txl txid _ ρ4 F3 bl (setN B4 x rx5) (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6) hg5 hB5 rfl rfl
            (Or.inr ⟨S'', hlv6⟩)
          have hes : es.length = rp.ws.length := (wMatch_length hlend.1).symm
          have hek : ∀ i, entryKey es i = wKey rp.ws i := wMatch_key _ _ hlend.1
          have hokk : spPartOldKey rx5 = (if rx5.nv.key' = slice.nil then w0.key else rx5.key) := by
            unfold spPartOldKey; rw [spWHead_of _ _ hw0]
          have hlv5w : wsLive rx5.ws := by rw [hrx5]; exact hlive4
          refine ⟨hB6, hg6', spillFrame_setB _ bl _ (by rw [hB5]; rfl), rfl, rfl, rfl,
            fun h => absurd h hpar, fun _ => ?_, hlv6.1, hlv6.2, fun l r hl hlS => ?_⟩
          rotate_left
          · have hlx : l ≠ x := fun e => hlS (e ▸ hxS)
            have hlp : l ≠ rx4.nv.parent' := fun e => hlS (e ▸ hparS)
            have e : (setN (setN (setN B4 x rx5) rx4.nv.parent' rp6) x rx6).ns !! l = B4.ns !! l := by
              show (<[x := rx6]> (<[rx4.nv.parent' := rp6]> (<[x := rx5]> B4.ns))) !! l = _
              rw [GMap.lookup_insert_ne _ _ (Ne.symm hlx), GMap.lookup_insert_ne _ _ (Ne.symm hlp),
                GMap.lookup_insert_ne _ _ (Ne.symm hlx)]
            rw [e] at hl; exact hnv4 l r hl hlS
          refine ⟨rfl, rfl, rfl, rfl, fun y hy1 hy2 => ?_, rx5, rx6, rp, rp6, sint.nat idx, hx5, hrp,
            GMap.lookup_insert _ _ _, ?_, by rw [hrx6], by rw [hrx6], by rw [hrx6],
            by rw [hrx6, spWHead_of _ _ hw0], by rw [hrx6]; exact spFresh_set0 rx5.ws w0 hw0 s1,
            by rw [hrx6]; exact spLive_set0 _ _ hlv5w ⟨hlend.2.1, hw0v⟩, by rw [hrx6]; exact hlend.2.2.2.1,
            by rw [hrx6]; exact hkn6, by rw [hrp6], by rw [hrp6], by rw [hrp6], by rw [hrp6],
            by rw [hrp6]; exact spPutList_length _ _ _ _ _ _ hrpl,
            by rw [hrp6]; exact spLive_put _ _ _ _ hrpL ⟨hlend.2.2.1, nofun⟩,
            by rw [← hes]; exact Hidx.2.1,
            fun k hk => by rw [← hek, hokk]; exact Hidx.2.2.1 k hk,
            fun h => by rw [← hek, hokk]; exact Hidx.2.2.2 (by rw [hes]; exact h), ?_⟩
          · show (<[x := rx6]> (<[rx4.nv.parent' := rp6]> (setN B4 x rx5).ns)) !! y = (setN B4 x rx5).ns !! y
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hy1), GMap.lookup_insert_ne _ _ (Ne.symm hy2)]
          · show (<[x := rx6]> (<[rx4.nv.parent' := rp6]> (setN B4 x rx5).ns)) !! rx4.nv.parent' = some rp6
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hpx)]; exact GMap.lookup_insert _ _ _
          · rw [hrp6, hbx, hes, hek, hokk]
            show (putList rp.ws _ _ _).map ownFresh = (putList rp.ws _ _ _).map ownFresh
            rw [spPutList_map, spPutList_map, spWHead_of _ _ hw0, hrx5]
            rfl
        iintro ⟨%T6, %B6, HR, tx, node, %Hj⟩
        obtain ⟨hT6, hg6, hfr6, hbuf6, hpm6, hmv6, hn6, hp6, hlvB6, hokB6, hnvB6⟩ := Hj
        icases spSpillR_stats I γd γ _ txl txid T6 ρ4 F3 K'' $$ HR with ⟨Hst, Hstback⟩
        try wp_auto
        wp_apply hInc _ T6.t.stats' (W64 1) $$ [Hst] as %st' ⟨%hst', Hst⟩
        · iframe
        ihave HR := Hstback $$ %st' Hst
        try wp_auto
        -- the part one more of the parts
        wp_for_post
        iframe
        iexists (iv + W64 1), { W'' with data := data' }, { T6 with t := { T6.t with stats' := st' } }, ρ4, F3,
          K'', B6, ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key)], x
        iframe
        have hbn3 : T''.bufs !! id = none := by
          have h := hg3.2.2.2.2.2.2.2.2.2.2.1.1 id
          rw [hpmid] at h
          rw [← hbuf3]
          cases hb : T3.bufs !! id with
          | none => rfl
          | some b => rw [hb] at h; exact absurd (h.2 rfl) (by simp)
        have hb7 : T''.bufs ⊆ ({ T6 with t := { T6.t with stats' := st' } } : WTx).bufs := by
          show T''.bufs ⊆ T6.bufs
          rw [hbuf6, hT4]
          show T''.bufs ⊆ <[id := wb]> (<[id := freshPage id (uint.nat cnt) W''.ps]> T0.bufs)
          rw [hbuf0, hbuf3]
          intro k v h
          have hne : id ≠ k := fun e => by rw [e] at hbn3; rw [hbn3] at h; cases h
          rw [GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert_ne _ _ hne]; exact h
        have hPP := spSpillPages_mono W'' { W'' with data := data' } T''
          { T6 with t := { T6.t with stats' := st' } } rfl hb7
        have hnm6 : B6.nm = B''.nm := by
          have h5 : (setN B4 x rx5).nm = B''.nm := by show B4.nm = B''.nm; rw [hnm4, hnm3]
          by_cases hpn : rx4.nv.parent' = null
          · rw [hn6 hpn]; exact h5
          · rw [(hp6 hpn).2.2.1]; exact h5
        have hcl : (chunksOf rc xs).length = xs.length := by
          unfold chunksOf; rw [spWsChunks_length, List.length_map]
        have hpsl : ps.length < (chunksOf rc xs).length := by
          rw [hcl]; have h1 := Hsll.1; rw [List.length_map] at h1; rw [hpl, h1]
          have := hiv; have := hlt2; have := Hsll.2; word
        have hch : (chunksOf rc xs)[ps.length]? = some ((chunksOf rc xs).getD ps.length []) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpsl]; rfl
        have hx7 : uint.nat (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) = uint.nat id := by
          rw [hfid]; unfold uint.nat; word
        have hpg7 : spillPages { W'' with data := data' } { T6 with t := { T6.t with stats' := st' } } !!
            uint.nat id = some wb :=
          spSpillPages_buf_at _ _ id wb hwid (by show T6.bufs !! id = some wb; rw [hbuf6]; exact GMap.lookup_insert _ _ _)
        have hp2 : (wHead rx5.ws).key = (wHead ((chunksOf rc xs).getD ps.length [])).key := by
          rw [hrx5, hpl]; exact spWHead_key _ _ hwsc
        have hlf : rc.nv.isLeaf' = r.nv.isLeaf' := by rw [← hrc]; show rn.nv.isLeaf' = _; rw [hl13]
        have hh : (rc.nv.isLeaf' = true → ht n = 0) ∧ (rc.nv.isLeaf' = false → ht n = ht n - 1 + 1) :=
          ⟨fun h => hht0 (hlf ▸ h), fun h => by have := hht1 (hlf ▸ h); omega⟩
        ihave Hpc : pieceResP (par ≠ null) γ
            (spillPages { W'' with data := data' } { T6 with t := { T6.t with stats' := st' } })
            (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n)
            (ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key)])
            (hiAt (chunksOf rc xs) (bnd n).2 ((ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int),
              (wHead rx5.ws).key)]).length - 1)) ∗
          chunkToks γ (spillPages { W'' with data := data' } { T6 with t := { T6.t with stats' := st' } }) B6
            rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
            (ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key)]).length
          $$ [Hpcs Hct Htok]
        · by_cases hce : (chunksOf rc xs).getD ps.length [] = []
          · -- the bucket's root, an empty leaf
            obtain ⟨hpn0, hleaf0, hchs, hps0, hfw, hidw, hwfw, hcntw⟩ : par = null ∧ rc.nv.isLeaf' = true ∧
                chunksOf rc xs = [[]] ∧ ps = [] ∧ pageFlags wb = leafPageFlag ∧ pageId wb = uint.nat id ∧
                leafWF wb wb.length ∧ pageCount wb = 0 := by
              have hw4 : rx4.ws = [] := by
                have h := congrArg List.length hwsc
                rw [List.length_map, List.length_map, ← hpl, hce] at h
                exact List.length_eq_zero_iff.1 h
              have hxe0 : xe.2.2 = [] :=
                List.length_eq_zero_iff.1 (by rw [← hxl, ← hws3, ← hwl4f, hw4]; rfl)
              have hpxe := (spCurPartNv bl n rc xs par Bs ws0 i0 hst.2.1 (sint.nat iv) xe hxe rs rx
                (by rw [hxe1]; exact hrs) hdnk).2
              have hrcne : rc.nv.parent' ≠ null → 0 < rc.ws.length := fun h => by
                have e1 : rc.ws = rn.ws := by rw [← hrc]
                have e2 : rc.nv.parent' = rn.nv.parent' := by rw [← hrc]
                rw [e1]; exact hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 n rn hlp.2.2.1 (by rw [← e2]; exact h)
              have hbr2 : rc.nv.isLeaf' = false → 2 ≤ rc.ws.length := fun h => by
                have e1 : rc.ws = rn.ws := by rw [← hrc]
                have e2 : rc.nv.isLeaf' = rn.nv.isLeaf' := by rw [← hrc]
                rw [e1]; exact (hl17.2.2.2.2.2.2.2.2.2 (by rw [← e2]; exact h)).2.1
              obtain ⟨hpn0, hleaf0, hchs, hxs1⟩ := spEmptyRoot bl n rc _ xs _ _ _ Ts Bs Ks par hst.2.2.2.2
                hilR hrcne hbr2 xe (List.mem_of_getElem? hxe) hxe0 hpxe
              have hl4' : rx4.nv.isLeaf' = true := by
                have hl4 : rx4.nv.isLeaf' = rx.nv.isLeaf' := by rw [hnv4f, hrx3]
                rw [hl4, spCurPartLeaf bl n rc _ xs par Bs ws0 i0 _ _ _ Ts Ks hst.2.1 hst.2.2.2.2 (sint.nat iv) xe
                  hxe rs rx (by rw [hxe1]; exact hrs) hdnk]; exact hleaf0
              obtain ⟨-, -, -, hfl', hcnt', -⟩ := writtenPage_facts (pageOf (freshPage id (uint.nat cnt) W''.ps))
                rx4.nv.isLeaf' _ _ rx4.ins ((freshPage id (uint.nat cnt) W''.ps).drop 16) hwok
              refine ⟨hpn0, hleaf0, hchs, List.length_eq_zero_iff.1 (by have := hpsl; rw [hcl, hxs1] at this; omega),
                by rw [hwbe, hfl', hl4']; rfl, by rw [hwpid, hfid], ?_, by rw [hwbe, hcnt', hil4, hw4]; rfl⟩
              rw [hwbe, hl4']
              exact writtenPage_leafWF _ _ _ rx4.ins _ hwok
                (fun i j _ hj => by rw [hil4, hw4] at hj; simp at hj)
            rw [hchs, hps0, hleaf0, List.nil_append]
            iapply spPiece_empty (par ≠ null) (fun h => h hpn0) γ (spillPages W'' T'')
              (spillPages { W'' with data := data' } { T6 with t := { T6.t with stats' := st' } }) B'' B6
              (if true = true then leafPageFlag else branchPageFlag) (ht n) (kd n) (ht n - 1) (bnd n).2
              (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key) wb (uint.nat id)
              hx7 hpg7 hfw hidw (by unfold uint.nat; have := id.isLt; omega) hwfw hcntw rfl (hh.1 hleaf0)
            iframe
          · have hwsc' : rx4.ws.map ownFresh = ((chunksOf rc xs).getD ps.length []).map ownFresh := by
              rw [hpl]; exact hwsc
            have hl4r : rx4.nv.isLeaf' = rc.nv.isLeaf' := by
              have hl4 : rx4.nv.isLeaf' = rx.nv.isLeaf' := by rw [hnv4f, hrx3]
              rw [hl4, spCurPartLeaf bl n rc _ xs par Bs ws0 i0 _ _ _ Ts Ks hst.2.1 hst.2.2.2.2 (sint.nat iv) xe
                hxe rs rx (by rw [hxe1]; exact hrs) hdnk]
            have hsrt : wsSorted rc.ws := by rw [← hrc]; exact hl17.2.2.2.1
            have hkbR : ∀ w ∈ rc.ws, 0 < w.key.length ∧ keyIn (bnd n).1 (bnd n).2 w.key := by
              rw [← hrc]; exact hl17.2.2.2.2.1
            have hbr2 : rc.nv.isLeaf' = false → 2 ≤ rc.ws.length := fun h => by
              have e1 : rc.ws = rn.ws := by rw [← hrc]
              have e2 : rc.nv.isLeaf' = rn.nv.isLeaf' := by rw [← hrc]
              rw [e1]; exact (hl17.2.2.2.2.2.2.2.2.2 (by rw [← e2]; exact h)).2.1
            obtain ⟨hsc, hkc⟩ := spChunkKeysOf bl n rc _ xs _ _ _ Ts Bs Ks par ws0 i0 hst.2.1 hst.2.2.2.2 hilR
              hsrt (bnd n).1 (bnd n).2 hkbR ps.length hce
            have hlen4 : rx4.ws.length = ((chunksOf rc xs).getD ps.length []).length := by
              have h := congrArg List.length hwsc'; rw [List.length_map, List.length_map] at h; exact h
            have hidr : uint.nat (pageOf (freshPage id (uint.nat cnt) W''.ps)).id' = uint.nat id := by
              rw [← hwid', ← hwbe, hwpid, hfid]
            have hw : spPieceWritten wb rc.nv.isLeaf' ((chunksOf rc xs).getD ps.length []) (uint.nat id) := by
              apply spPieceWritten_fresh _ _ rx4.ws _ _ ?_ hwsc'
              rw [hwbe, hbk, hbvv, ← hl4r]
              exact spPieceWritten_wp _ _ rx4.ins rx4.ws _ (uint.nat id) hidr
                (by unfold uint.nat; have := id.isLt; omega) hil4
                (by rw [hlen4]; exact List.length_pos_iff.2 hce) (by rw [← hbk, ← hbvv]; exact hwok) hfp4
                (fun i j hij hj => by
                  rw [← wKey_fresh rx4.ws, hwsc', wKey_fresh]
                  exact hsc i j hij (by rw [← hlen4]; exact hj))
            have hk : ∀ w ∈ (chunksOf rc xs).getD ps.length [], 0 < w.key.length ∧
                keyIn (some (wHead rx5.ws).key) (hiAt (chunksOf rc xs) (bnd n).2 ps.length) w.key := by
              rw [hp2]; exact hkc
            have hnmBs : Bs.nm = B'.nm := by
              rcases hst.2.2.2.2 with ⟨-, -, hBs, -⟩ | ⟨pv', pcs', st, -, -, -, -, -, hBs, -⟩
              · rw [hBs, ← hB3]; rfl
              · rw [hBs, ← hB3]; rfl
            have hnmf : rc.nv.isLeaf' = false →
                ∀ w ∈ (chunksOf rc xs).getD ps.length [], B''.nm !! w.pgid = none := by
              intro hl w hw
              have hlr : rn.nv.isLeaf' = false := by
                have e2 : rc.nv.isLeaf' = rn.nv.isLeaf' := by rw [← hrc]
                rw [← e2]; exact hl
              have hwr : w ∈ rn.ws := by
                have := spChunks_sub _ rc.ws ps.length w hw; rw [← hrc] at this; exact this
              rw [hpp.2.2.2.2.2.2.2.2.1, hnmBs]
              cases hc : B'.nm !! w.pgid with
              | none => rfl
              | some c =>
                obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwr
                obtain ⟨rc', hrc', -, hpg', -, -, hcs, -⟩ := (hl17.2.2.2.2.2.2.2.2.2 hlr).2.2.2.1 i w c
                  (by rw [List.getElem?_eq_getElem hi, hiw]) hc
                obtain ⟨rc'', hrc'', -, -, -, -, -, -, hnm''⟩ := hall c hcs
                rw [hrc'] at hrc''; cases hrc''
                rw [hpg', hc] at hnm''; cases hnm''
            have hbr : rc.nv.isLeaf' = false → 2 ≤ ((chunksOf rc xs).getD ps.length []).length ∧
                ∀ w ∈ (chunksOf rc xs).getD ps.length [], B''.nm !! w.pgid = none := fun hl =>
              ⟨spChunkLen2 bl n rc _ xs _ _ _ Ts Bs Ks par ws0 i0 hst.2.1 hst.2.2.2.2 hilR hbr2 ps.length
                (by rw [← hcl]; exact hpsl) hl, hnmf hl⟩
            iapply spPiece_step (par ≠ null) γ (spillPages W'' T'')
              (spillPages { W'' with data := data' } { T6 with t := { T6.t with stats' := st' } }) B'' B6
              rc.nv.isLeaf' (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) (kd n) (ht n - 1)
              (chunksOf rc xs) (bnd n).2 ps
              (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key) wb
              ((chunksOf rc xs).getD ps.length []) (uint.nat id) hPP hnm6 hch hx7 hpg7 hw hp2 rfl
              hh hk hbr
            iframe
        icases Hpc with ⟨Hpcs, Hct⟩
        iframe
        rw [if_neg (show ¬ (ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int),
          (wHead rx5.ws).key)] = [] ∧ rc.nv.pgid' ≠ W64 0) by simp)]
        ipureintro
        have hiv1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
          have := hlt2; have := hiv; have := Hsll.2; word
        refine ⟨trivial, ?_, by rw [List.length_append, hpl, hiv1]; rfl,
          by have := hlt2; have := hiv; have := Hsll.2; word⟩
        -- the part done: `partsP` one part longer
        have hxeP : xs[ps.length]? = some xe := by rw [hpl]; exact hxe
        have hpid : W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int) = id := hpo1
        have hT4bs : T4.bs = T0.bs := by rw [hT4]; rfl
        have hT4mv : T4.mv.txid' = T0.mv.txid' := by rw [hT4]; rfl
        have hT4t : T4.t = { T0.t with stats' := T4.t.stats' } := by rw [hT4]; rfl
        have h0 : spillFrame T'' T0 (· = bl) :=
          spillFrame_transN T'' T3 T0 _ _ hfr3 (spFrame_deref T3 T0 hT0 _) (fun _ h => h)
        have hfrT : spillFrame T'' { T6 with t := { T6.t with stats' := st' } } (· = bl) := by
          refine spFrame_glue T'' T0 (setB { T4 with bufs := <[id := wb]> T4.bufs } bl (setN B4 x rx5)) _ bl h0
            (spillFrame_transN _ T6 _ _ _ hfr6 (spFrame_stats T6 st' _) (fun _ h => h)) (fun c hc => ?_)
            (fun c => ?_) hT4mv (by rw [hmv0]; exact hmvle) hb7 hT4t
          · show (<[bl := setN B4 x rx5]> T4.bs) !! c = T0.bs !! c
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hc), hT4bs]
          · show (T0.bs !! c).isSome ↔ ((<[bl := setN B4 x rx5]> T4.bs) !! c).isSome
            by_cases e : c = bl
            · subst e; rw [GMap.lookup_insert, hB4']; simp
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), hT4bs]
        obtain ⟨hnvx, hpxe⟩ := spCurPartNv bl n rc xs par Bs ws0 i0 hst.2.1 (sint.nat iv) xe hxe rs rx
          (by rw [hxe1]; exact hrs) hdnk
        have hpar4 : rx4.nv.parent' = par := by
          have e : rx4.nv.parent' = rx.nv.parent' := by rw [hnv4f, hrx3]
          rw [e, hnvx]; exact hpxe
        have hl4r : rx4.nv.isLeaf' = rc.nv.isLeaf' := by
          have hl4 : rx4.nv.isLeaf' = rx.nv.isLeaf' := by rw [hnv4f, hrx3]
          rw [hl4, spCurPartLeaf bl n rc _ xs par Bs ws0 i0 _ _ _ Ts Ks hst.2.1 hst.2.2.2.2 (sint.nat iv) xe
            hxe rs rx (by rw [hxe1]; exact hrs) hdnk]
        have hrcne : rc.nv.parent' ≠ null → 0 < rc.ws.length := fun h => by
          have e1 : rc.ws = rn.ws := by rw [← hrc]
          have e2 : rc.nv.parent' = rn.nv.parent' := by rw [← hrc]
          rw [e1]; exact hlp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 n rn hlp.2.2.1 (by rw [← e2]; exact h)
        have hne5 : par ≠ null → 0 < rx5.ins.length := fun hp => by
          rw [hrx5]; show 0 < rx4.ins.length
          rw [hil4, hwl4f, hws3, hxl]
          exact spPartNonempty bl n rc _ xs _ _ _ Ts Bs Ks par hst.2.2.2.2 hilR hrcne xe
            (List.mem_of_getElem? hxe) (by rw [hpxe]; exact hp)
        have hx5B : (setN B4 x rx5).ns !! x = some rx5 := GMap.lookup_insert _ _ _
        have hB6f : B6.bv = B4.bv ∧ B6.ib = B4.ib ∧ B6.nm = B4.nm ∧ B6.bm = B4.bm := by
          by_cases hpn : rx4.nv.parent' = null
          · rw [hn6 hpn]; exact ⟨rfl, rfl, rfl, rfl⟩
          · obtain ⟨a, b, c, d, -⟩ := hp6 hpn; exact ⟨a, b, c, d⟩
        -- the part in B6
        obtain ⟨rxN, hxN, hnvN, hinsN, hcsN, hwsN, hdN⟩ : ∃ r, B6.ns !! x = some r ∧
            r.nv = { rx5.nv with key' := r.nv.key' } ∧ r.ins = rx5.ins ∧ r.cs = rx5.cs ∧
            r.ws.map ownFresh = rx5.ws.map ownFresh ∧ derefOK bl r := by
          by_cases hpn : rx4.nv.parent' = null
          · rw [hn6 hpn]; exact ⟨rx5, hx5B, rfl, rfl, rfl, rfl, hd5⟩
          · obtain ⟨-, -, -, -, -, ra, rb, -, -, -, hra, -, hrb, -, hnvb, hinsb, hcsb, hkeyb, hwsb, hlvb, hksb,
              hknb, -⟩ := hp6 hpn
            rw [hx5B] at hra; cases hra
            refine ⟨rb, hrb, hnvb, hinsb, hcsb, hwsb, ?_⟩
            obtain ⟨d1, -, d3, -⟩ := hd5
            have hwl : rb.ws.length = rx5.ws.length := by simpa using congrArg List.length hwsb
            refine ⟨by rw [hnvb]; exact d1, by rw [hinsb, h5, hwl], fun w hw => ?_, Or.inr ⟨hksb, Or.inr ?_⟩⟩
            · have hm : ownFresh w ∈ rx5.ws.map ownFresh := by rw [← hwsb]; exact List.mem_map_of_mem hw
              obtain ⟨w0, hw0, he⟩ := List.mem_map.1 hm
              have hk : w0.key = w.key := by have := congrArg WEntry.key he; exact this
              exact ⟨(hlvb w hw).1, (hlvb w hw).2, by rw [← hk]; exact (d3 w0 hw0).2.2⟩
            · rw [hkeyb]
              have hp' : par ≠ null := by rw [← hpar4]; exact hpn
              have hl := hne5 hp'
              rw [h5] at hl
              cases hw5 : rx5.ws with
              | nil => rw [hw5] at hl; simp at hl
              | cons a l => exact (d3 a (by rw [hw5]; exact List.mem_cons_self ..)).2.2
        -- its children: none
        have hcsrs : rs.cs = [] := by
          have h1 := hst.2.1.2.2.2.2.2.2.2.1 (sint.nat iv) xe hxe
          rw [hxe1, hrs] at h1; cases h1
          unfold partRec; split
          · exact hrcs
          · rfl
        have hcsx : rxN.cs = [] := by
          obtain ⟨-, -, -, -, hcs1, -⟩ := spDnK_facts rs rx hdnk
          obtain ⟨-, -, -, -, hcs4, -⟩ := spDnK_facts rx3 rx4 hdn4
          rw [hcsN, hrx5]; show rx4.cs = []; rw [hcs4, hrx3]; show rx.cs = []; rw [hcs1, hcsrs]
        -- the nodes but the part and the parent: kept (dereferenced at the allocation)
        have hothB : ∀ y r, y ≠ x → (par ≠ null → y ≠ par) → B''.ns !! y = some r →
            ∃ r', B6.ns !! y = some r' ∧ dnK r r' := by
          intro y r hy hyp hr
          obtain ⟨r4, h4, hd⟩ := hfw4 y r (by rw [hoth y hy]; exact hr)
          refine ⟨r4, ?_, hd⟩
          have e : (setN B4 x rx5).ns !! y = B4.ns !! y := GMap.lookup_insert_ne _ _ (Ne.symm hy)
          by_cases hpn : rx4.nv.parent' = null
          · rw [hn6 hpn, e]; exact h4
          · obtain ⟨-, -, -, -, ho, -⟩ := hp6 hpn
            rw [ho y hy (by rw [hpar4]; exact hyp (by rw [← hpar4]; exact hpn)), e]; exact h4
        have hdomB : ∀ y, (B6.ns !! y).isSome → (B''.ns !! y).isSome := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; rw [hrx]; rfl
          have e : (setN B4 x rx5).ns !! y = B4.ns !! y := GMap.lookup_insert_ne _ _ (Ne.symm hyx)
          have h4 : (B4.ns !! y).isSome := by
            by_cases hpn : rx4.nv.parent' = null
            · rw [hn6 hpn, e] at hy; exact hy
            · obtain ⟨-, -, -, -, ho, -, -, rpa, -, -, -, hrpa, -⟩ := hp6 hpn
              by_cases hyp : y = rx4.nv.parent'
              · rw [← e, hyp, hrpa]; rfl
              · rw [ho y hyx hyp, e] at hy; exact hy
          obtain ⟨r4, hr4⟩ := Option.isSome_iff_exists.1 h4
          obtain ⟨r3, hr3, -⟩ := hdn4all y r4 hr4
          rw [← hoth y hyx, hr3]; rfl
        -- the parent: the part's entry put in
        have hparP : par ≠ null → ∀ rp, B''.ns !! par = some rp → ∃ rp', B6.ns !! par = some rp' ∧
            parentWs ws0 i0 (ps ++ [(W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int),
              (wHead rx5.ws).key)]) rp'.ws ∧ wsSorted rp'.ws ∧ wsLive rp'.ws ∧
            rp'.ins.length = rp'.ws.length ∧
            rp'.nv = { rp.nv with inodes' := rp'.nv.inodes', key' := rp'.nv.key' } ∧ rp'.cs = rp.cs ∧
            rp'.key = rp.key ∧ (rp.nv.key' = slice.nil → rp'.nv.key' = slice.nil) ∧
            (rp.nv.key' ≠ slice.nil → 0 < rp.key.length → rp'.nv.key' ≠ slice.nil) ∧
            (rp'.ksrc = rp.ksrc ∨ rp'.ksrc = Src.own (DFrac.own 1)) := by
          intro hp rpo hrpo
          have hpn : rx4.nv.parent' ≠ null := by rw [hpar4]; exact hp
          obtain ⟨-, -, -, -, -, ra, rb, rpa, rpb, idx, hra, hrpa, hrb, hrpb, -, -, -, -, -, -, -, -,
            hnvp, hcsp, hkeyp, hksp, hilp, hlvp, hid1, hid2, hid3, hwsp⟩ := hp6 hpn
          rw [hx5B] at hra; cases hra
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, P17, -⟩ := _root_.id hpp
          obtain ⟨rpq, hrpq, -, hpwq, -, -, hsq, -, hnotq, -⟩ := P17 hp
          rw [hrpo] at hrpq; cases hrpq
          have hpx : rx4.nv.parent' ≠ x := by
            rw [hpar4]; intro e; apply hnotq; rw [e, ← hxe1]
            exact List.mem_map_of_mem (List.mem_of_getElem? hxe)
          have hrpa4 : B4.ns !! rx4.nv.parent' = some rpa := by
            have h := hrpa
            rw [show (setN B4 x rx5).ns !! rx4.nv.parent' = B4.ns !! rx4.nv.parent' from
              GMap.lookup_insert_ne _ _ (Ne.symm hpx)] at h
            exact h
          obtain ⟨r3, hr3, hdnp⟩ := hdn4all _ rpa hrpa4
          rw [hoth _ hpx, hpar4, hrpo] at hr3; cases hr3
          obtain ⟨-, -, hwsd, hnvd, hcsd, hkeyd, -, -, hknd⟩ := spDnK_facts rpo rpa hdnp
          have hpw := spParentWs_fresh ws0 i0 ps rpo.ws rpa.ws hwsd.symm hpwq
          have hsa := spSorted_fresh rpo.ws rpa.ws hwsd.symm hsq
          -- the keys: the part's first key in the node's bounds, the node's in the parent entry's
          have hp2m : (wHead rx5.ws).key ∈ rc.ws.map WEntry.key := by
            have hl := hne5 hp
            rw [h5] at hl
            have hm : wHead rx5.ws ∈ rx5.ws := by
              cases hw5 : rx5.ws with
              | nil => rw [hw5] at hl; simp at hl
              | cons a l => exact List.mem_cons_self ..
            have hm' : ownFresh (wHead rx5.ws) ∈ ((chunksOf rc xs).getD (sint.nat iv) []).map ownFresh := by
              rw [← hwsc]; have : rx5.ws = rx4.ws := by rw [hrx5]
              rw [← this]; exact List.mem_map_of_mem hm
            obtain ⟨c, hc, hce⟩ := List.mem_map.1 hm'
            have hk : c.key = (wHead rx5.ws).key := by have := congrArg WEntry.key hce; exact this
            rw [← hk]; exact List.mem_map_of_mem (hmemx c hc)
          have hkbR : ∀ w ∈ rc.ws, 0 < w.key.length ∧ keyIn (bnd n).1 (bnd n).2 w.key := by
            rw [← hrc]; exact hl17.2.2.2.2.1
          obtain ⟨wq, hwq, hwqk⟩ := List.mem_map.1 hp2m
          have hkin := (hkbR wq hwq).2
          rw [hwqk] at hkin
          have hbd : ∀ (hrcp : rc.nv.parent' ≠ null), (∀ w ∈ ws0.take i0, go.GoStringLt w.key (wHead rx5.ws).key) ∧
              (∀ w ∈ ws0.drop (i0 + 1), go.GoStringLt (wHead rx5.ws).key w.key) := by
            intro hrcp
            obtain ⟨-, rpB, hrpB, hsB, i1, w1, hw1, hk1, hbnd⟩ := hpar3b hrcp
            obtain ⟨hpe, hws0, hi0⟩ := spParentEntry bl n rc _ xs _ _ _ Ts Bs Ks par ws0 i0 hst.2.1 hst.2.2.2.2
              hrcp (by rw [hrpB]; rfl) (by rw [hrpB]; exact hsB) i1 w1 (by rw [hrpB]; exact hw1) hk1
            simp only [hrpB, Option.getD_some] at hws0
            subst hws0 hi0
            rw [← hpe] at hbnd
            have hs0 := hsB
            refine ⟨fun w hw => ?_, fun w hw => ?_⟩
            · obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
              have hk' : k < i0 := by simp at hk; omega
              have hi0l : i0 < rpB.ws.length := (List.getElem?_eq_some_iff.1 hw1).1
              have hlo := hbnd.1 (wKey rpB.ws i0) (by
                unfold entryBnd childLo; rw [if_neg (by omega)])
              obtain ⟨x0, hx0, hx0l⟩ := hlo
              have hge := hkin.1 x0 hx0
              have hwk : w.key = wKey rpB.ws k := by
                rw [← hkw]; unfold wKey; rw [List.getElem_take, List.getElem?_eq_getElem (by omega)]; rfl
              rw [hwk]
              exact spLt_le (spLt_le (hs0 k i0 hk' hi0l) hx0l) hge
            · obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
              have hkl : i0 + 1 + k < rpB.ws.length := by simp at hk; omega
              have hhi := hbnd.2 (wKey rpB.ws (i0 + 1)) (by
                unfold entryBnd childHi; rw [if_pos (by omega)])
              obtain ⟨x1, hx1, hx1l⟩ := hhi
              have hlt := hkin.2 x1 hx1
              have hwk : w.key = wKey rpB.ws (i0 + 1 + k) := by
                rw [← hkw]; unfold wKey; rw [List.getElem_drop, List.getElem?_eq_getElem hkl]; rfl
              rw [hwk]
              have h1 := spLt_le hlt hx1l
              rcases Nat.eq_zero_or_pos k with h0 | h0
              · subst h0; exact h1
              · exact goStringLt_trans h1 (hs0 (i0 + 1) (i0 + 1 + k) (by omega) hkl)
          have hkn0 : rc.nv.parent' ≠ null → 0 < rc.key.length ∧ rc.nv.key' ≠ slice.nil := fun hrcp => by
            have hkn := (hpar3b hrcp).1
            have e1 : rc.nv.key' = rn.nv.key' := by rw [← hrc]
            have e2 : rc.key = rn.key := by rw [← hrc]
            rcases hl17.2.2.2.2.2.2.1 with h | ⟨h, -⟩
            · rw [← e1] at h; exact absurd h hkn
            · rw [e2]; exact ⟨h, hkn⟩
          obtain ⟨hk0, hkj⟩ := spPartKeys bl n rc xs par Bs ws0 i0 hst.2.1 (sint.nat iv) xe hxe rs rx
            (by rw [hxe1]; exact hrs) hdnk
          obtain ⟨-, -, -, -, -, hkey4', -, -, hkn4'⟩ := spDnK_facts rx3 rx4 hdn4
          have hfirst : ps = [] → (∃ w, ws0[i0]? = some w ∧ w.key = spPartOldKey rx5) ∨ (ws0 = [] ∧ i0 = 0) := by
            -- the first part: the node's own entry, or a new parent's first
            intro hps0
            have hiv0 : sint.nat iv = 0 := by rw [← hpl, hps0]; rfl
            obtain ⟨rp0', -, -, hcase⟩ := hst.2.1.2.2.2.2.2.2.1 hp
            rcases hcase with ⟨hrcp, w, hw, hwk, -⟩ | ⟨-, h0, h1⟩
            · left; refine ⟨w, hw, ?_⟩
              obtain ⟨hkl, hknn⟩ := hkn0 hrcp
              obtain ⟨a, b⟩ := hk0 hiv0 hknn hkl
              have h3 : rx3.nv.key' ≠ slice.nil ∧ rx3.key = rx.key := by rw [hrx3]; exact ⟨a, rfl⟩
              obtain ⟨a4, b4⟩ := spDnK_keyNN rx3 rx4 hdn4 h3.1 (by rw [h3.2, b]; exact hkl)
              have hkn5 : rx5.nv.key' ≠ slice.nil := by rw [hrx5]; exact a4
              unfold spPartOldKey; rw [if_neg hkn5, hwk]
              rw [hrx5]; show rc.key = rx4.key; rw [b4, h3.2, b]
            · right; exact ⟨h0, h1⟩
          have hlater : ps ≠ [] → spPartOldKey rx5 = (wHead rx5.ws).key := by
            -- a later part: no key
            intro hps
            have hpos : 0 < sint.nat iv := by
              rw [← hpl]; exact List.length_pos_iff.2 hps
            have hx3 : rx3.nv.key' = slice.nil := by rw [hrx3]; exact hkj hpos
            have hkn5 : rx5.nv.key' = slice.nil := by rw [hrx5]; exact hkn4' hx3
            unfold spPartOldKey; rw [if_pos hkn5]
          have hlo : ∀ w ∈ ws0.take i0, go.GoStringLt w.key (wHead rx5.ws).key := by
            intro w hw
            by_cases hrcp : rc.nv.parent' = null
            · obtain ⟨rp0', -, -, hcase⟩ := hst.2.1.2.2.2.2.2.2.1 hp
              rcases hcase with ⟨h, -⟩ | ⟨-, h0, -⟩
              · exact absurd hrcp h
              · rw [h0] at hw; simp at hw
            · exact (hbd hrcp).1 w hw
          have hhi : ∀ w ∈ ws0.drop (i0 + 1), go.GoStringLt (wHead rx5.ws).key w.key := by
            intro w hw
            by_cases hrcp : rc.nv.parent' = null
            · obtain ⟨rp0', -, -, hcase⟩ := hst.2.1.2.2.2.2.2.2.1 hp
              rcases hcase with ⟨h, -⟩ | ⟨-, h0, -⟩
              · exact absurd hrcp h
              · rw [h0] at hw; simp at hw
            · exact (hbd hrcp).2 w hw
          have hes : ∀ q ∈ ps, go.GoStringLt q.2 (wHead rx5.ws).key := by
            -- the parts before: lower first keys
            intro q hq
            obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem hq
            have hq2 := hpp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j q (by rw [← hjq]; exact List.getElem?_eq_getElem hj)
            rw [hq2, hp2]
            have hsrt : wsSorted rc.ws := by rw [← hrc]; exact hl17.2.2.2.1
            exact spChunkHeads_lt bl n rc _ xs _ _ _ Ts Bs Ks par ws0 i0 hst.2.1 hst.2.2.2.2 hilR hsrt
              (bnd n).1 (bnd n).2 hkbR (by have := hpsl; rw [hcl] at this; omega) j ps.length hj
              (by rw [← hcl]; exact hpsl)
          obtain ⟨hpw', hs'⟩ := spParentWs_step ws0 i0 ps rpa.ws rpb.ws
            (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key)
            ⟨W32 0, W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int), (wHead rx5.ws).key, [],
              Src.own (DFrac.own 1), Src.own (DFrac.own 1)⟩ idx (spPartOldKey rx5) hpw hsa ⟨hid1, hid2, hid3⟩
            hwsp ⟨rfl, rfl, rfl, rfl, nofun, nofun⟩ hfirst hlater hlo hhi hes
          refine ⟨rpb, by rw [← hpar4]; exact hrpb, hpw', hs', hlvp, hilp, by rw [hnvp, hnvd],
            hcsp.trans hcsd, hkeyp.trans hkeyd, fun h => by rw [hnvp]; exact hknd h,
            fun h hl => by rw [hnvp]; exact (spDnK_keyNN rpo rpa hdnp h hl).1, ?_⟩
          rw [hksp]; exact spDnK_ksrc rpo rpa hdnp
        -- the bucket's names: the new page's is not one
        have hnmBs : Bs.nm = B'.nm := by
          rcases hst.2.2.2.2 with ⟨-, -, hBs, -⟩ | ⟨pv', pcs', st, -, -, -, -, -, hBs, -⟩
          · rw [hBs, ← hB3]; rfl
          · rw [hBs, ← hB3]; rfl
        have hf4 : B''.nm !! (W64 ((pageId (freshPage id (uint.nat cnt) W''.ps) : Nat) : Int)) = none := by
          rw [hpp.2.2.2.2.2.2.2.2.1, hnmBs, hpid]
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl18, -⟩ := hlp
          cases hc : B'.nm !! id with
          | none => rfl
          | some l =>
            rcases hl18.2.2.1 id l hc with h | h
            · rw [h] at hid2; exact absurd hid2 (by decide)
            · have hpg : W'.pages = W''.pages := hpp.2.2.2.1.symm
              rw [hpg, hwid] at h; cases h
        exact spPartsP_step bl txl txid n rc xs par ws0 i0 (bnd n).1 (bnd n).2 W' Ts Bs Ks W'' T'' ρ'' F'' K''
          B'' ps hpp _ _ ρ4 F3 B6 _ xe hxeP hst.2.1.2.1 (spillG_stat _ txl txid T6 ρ4 F3 st' hg6) hT6 hfrT rfl rfl
          hPP (hB6f.1.trans (hbv4.trans hbv3)) (hB6f.2.1.trans (hib4.trans hib3))
          (hB6f.2.2.1.trans (hnm4.trans hnm3)) (hB6f.2.2.2.trans (hbm4.trans hbm3)) rxN (by rw [hxe1]; exact hxN)
          (by rw [hnvN, hrx5]) hcsx (by rw [hnvN]; exact hd5.1) hdN.2.1 hdN (by rw [hnvN, hrx5])
          (by rw [hnvN]; rw [hrx5]; exact hpar4)
          (by rw [hwsN, hpl]; rw [show rx5.ws = rx4.ws by rw [hrx5]]; exact hwsc)
          (by rw [hnvN, hrx5]; exact hl4r) (fun hp => by rw [hinsN]; exact hne5 hp) hp2
          (by rw [hpid]; exact hbn3) (by rw [hx7]; exact hwid)
          (by rw [hpid]; show (T6.bufs !! id).isSome; rw [hbuf6, GMap.lookup_insert]; rfl) hf4
          (by rw [hx7]; exact hid2) (by rw [hxe1]; exact hothB) hdomB hparP
          ⟨S'', hlvB6, hokB6, hxsS, hparS'', hnvB6⟩
      · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
          cases err with
          | nil => exact absurd rfl he
          | ok e => exact ⟨e, rfl⟩
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ
        iapply spErrPost
        · exact he
        · exact hpar1
        iexact Herr
    · rw [decide_eq_false hlt2]
      try wp_auto
      simp only [decide_eq_true_eq, intoVal_eq_iff, Bool.false_eq_true, ite_false]
      try wp_auto
      -- after the parts: `n.parent.spill()` for a new parent (pgid 0), else return nil
      try simp only [decide_eq_true_eq, intoVal_eq_iff, Bool.false_eq_true, ite_false]
      try wp_auto
      have hpx : ps.length = xs.length := by
        have h1 := Hsll.1; rw [List.length_map] at h1
        have h2 := hpp.2.2.2.2.2.2.2.2.2.2.1
        have := Hsll.2; have := hiv; have := hlt2
        rw [hpl] at h2 ⊢; rw [h1] at h2 ⊢; word
      obtain ⟨rn5, hrn5, hpar5, hcs5, hparq⟩ := spPartsExit bl txl txid n rc xs par ws0 i0 (bnd n).1 (bnd n).2
        W' Ts Bs Ks W'' T'' ρ'' F'' K'' B'' ps hpp hst.2.1 hpx
      have hX : SpExit (hG := hG) N top I W txl txid T ρ F K bl B bnd kd ht n r sp sub W' T' ρ' F' K' B'
          rn ic sp' sub' rc B3 T3 xs Ts Bs Ks par ws0 i0 W'' T'' ρ'' F'' K'' B'' ps rn5 :=
        ⟨hf, hg, hB, hHt, hht0, hht1, hn, hK, hL, hch, htopc, hkt, hthr, hps, hel, hne, hP1, hP1n, hP2,
          hP3, htok, hpar0, hplf, hpar1, hnn, hlp, htrp, hall, hdrop, hrc.symm, hB3.symm, hT3.symm, hxsf,
          ⟨hst.1, hst.2.1, hst.2.2.1⟩, hPs, hpp, hpx, hrn5, hpar5, hst.2.2.2.2, htopn,
          fun htt => by
            obtain ⟨p, hu, hpnd, hdom, hpv⟩ := htopv htt
            obtain ⟨-, -, hB', hrn, -⟩ := htt0 htt
            obtain ⟨hu', hdom', hpv'⟩ := spTopP B n r ys p hn hperm hu hdom hpv
            rw [hB', hrn]; exact ⟨p, hu', hpnd, hdom', hpv'⟩,
          fun htt => by
            obtain ⟨-, -, -, hrn, -⟩ := htt0 htt
            rw [hrn]; exact (htopc htt).2,
          fun j x rx hj hx hrx => by
            obtain ⟨-, rx', p, hrx', -, -, -, -, -, -, -, -, hws, hlf⟩ := hpp.2.2.2.2.2.2.2.2.2.2.2.1 j x hj hx
            rw [hrx] at hrx'; cases hrx'; exact ⟨hws, hlf⟩,
          h3nn⟩
      icases spillR_node I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' n rn5 hpp.2.1 hrn5 $$ HR
        with ⟨Hnn, Hnb, Hnback⟩
      try wp_auto
      by_cases hpn : rn5.nv.parent' = null
      · -- no parent: the part is the bucket's root
        try rw [decide_eq_true hpn]
        try simp only [hpn, decide_true, eq_self_iff_true, decide_eq_true_eq, Bool.not_true]
        try wp_auto
        try rw [if_pos trivial]
        try wp_auto
        ihave HR := Hnback $$ Hnn Hnb
        icases spPost_root γd γ hX hpn $$ [HR Hpcs Hct Hpg] with ⟨%hr0, Hfin⟩
        · iframe
        iapply HΦ
        rw [if_pos hr0]
        iexact Hfin
      · try rw [decide_eq_false hpn]
        try simp only [hpn, decide_false]
        try wp_auto
        try rw [if_neg not_false]
        try wp_auto
        obtain ⟨rq, hrq, hqn⟩ : ∃ rq, B''.ns !! rn5.nv.parent' = some rq ∧ rn5.nv.parent' ≠ n := by
          rw [hpar5] at hpn ⊢; exact hparq hpn
        ihave HR := Hnback $$ Hnn Hnb
        icases spillR_node I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' rn5.nv.parent' rq hpp.2.1 hrq $$ HR
          with ⟨Hqn, Hqb, Hqback⟩
        try wp_auto
        ihave HR := Hqback $$ Hqn Hqb
        by_cases hq0 : rq.nv.pgid' = W64 0
        · -- a new parent: spill it
          try rw [decide_eq_true hq0]
          try simp only [hq0, decide_true]
          try wp_auto
          try rw [if_pos trivial]
          try wp_auto
          icases spExit_keep γd γ hX $$ HR with ⟨%hko, HR⟩
          icases spSpillRNilKids I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' n rn5 hpp.2.1 hrn5 hcs5 $$ HR
            with ⟨Hnn, Hnback⟩
          try wp_auto
          ihave HR := Hnback $$ Hnn
          rw [show ({ rn5.nv with children' := slice.nil } : node).parent' = rn5.nv.parent' from rfl]
          have hT7 : (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })).bs !! bl =
              some (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) := GMap.lookup_insert _ _ _
          ihave Hrt : rtoks γ (spillPages W'' (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })))
              (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) (none, none)
              (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) rq $$ [Hpcs Hct Hpg]
          · iapply spNewParent_toks γ hX hpn rq hrq hq0
            iframe
          obtain ⟨hr0, hm, hg7, hq7, hqp, hql, hqK, hqL, hqc, ⟨p, hup, hnd, hdom, hnv⟩, hthr7, hps7, hel7, hne7,
            hP17, hP27, hP37⟩ := spNewParent_pre hX hpn rq hrq hq0
          cases htt : top
          · wp_apply (htop htt (rq.ws.length + 1) I γd γ W'' txl txid _ ρ'' F'' K'' bl _ _ (ht n)
              rn5.nv.parent' rq p hf hg7 hT7 (Nat.lt_succ_self _) hq7 hq0 hqp hql hqK hqL hqc hup hnd hnv hdom
              hthr7 hps7 hel7 hne7 hP17 hP27 hP37) $$ [HR Hrt] as %err Hfin
            · iframe
            try wp_auto
            iapply HΦ
            rw [if_pos hr0]
            iapply spNewParent_post γd γ hX hpn rq hrq hq0 err hko
            iexact Hfin
          · wp_apply (htopB htt (rq.ws.length + 1) (hm htt) I γd γ W'' txl txid _ ρ'' F'' K'' bl _ _ (ht n)
              rn5.nv.parent' rq p hf hg7 hT7 (Nat.lt_succ_self _) hq7 hq0 hqp hql hqK hqL hqc hup hnd hnv hdom
              hthr7 hps7 hel7 hne7 hP17 hP27 hP37) $$ [HR Hrt] as %err Hfin
            · iframe
            try wp_auto
            iapply HΦ
            rw [if_pos hr0]
            iapply spNewParent_post γd γ hX hpn rq hrq hq0 err hko
            iexact Hfin
        · -- the existing parent: return
          try rw [decide_eq_false hq0]
          try simp only [hq0, decide_false]
          try wp_auto
          try rw [if_neg not_false]
          try wp_auto
          icases spPost_sub γd γ hX hpn rq hrq hq0 $$ [HR Hpcs Hct Hpg] with ⟨%hr0, Hsub⟩
          · iframe
          iapply HΦ
          rw [if_neg hr0]
          iexact Hsub
end proof

end bbolt
end EtcdGrove
end Perennial
