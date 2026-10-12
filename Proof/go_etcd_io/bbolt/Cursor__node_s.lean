module
public import Spec.go_etcd_io.bbolt.Cursor__node_s
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.elemRef__isLeaf_w
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Proof.go_etcd_io.bbolt.ShapeCursor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.node()` with the shape: `Cursor.node.wp_proof`'s loop, its invariant also holding the
shape (`bktShape_nodeRes` at each materialization), the positions kept (`bktExt`), and the
facts of a key routed down the path (`kroute`: within the current node's bounds; `pathKey`). -/
theorem Cursor.node.wp_sproof (hA : Assert.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.wspec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hnode : Bucket.node.spec (GF := GF) (hG := hG))
    (hchild : node.childAt.spec (GF := GF) (hG := hG)) :
    Cursor.node.sspec (GF := GF) (hG := hG) := by
  intro γ cl cv path W hwm bl B txl st pmap pm dqp Hbl HOK Hpath
  obtain ⟨HvOK, Hclean, Htx, Hpmv⟩ := HOK
  wp_start as ⟨Hcl, Hs, Hctx, Hst, Hsh⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have Hroot := posOK_root W hwm bl B Hclean
  obtain ⟨pid', rt, ks, Hlast, Hra, Hpos', Hkids, Hi0⟩ := wpath_last W hwm bl B Hclean path B.ib.root' Hpath Hroot
  have Hne : path ≠ [] := by intro h; subst h; simp at Hlast
  have Hpos : 0 < path.length := List.length_pos_iff.2 Hne
  have Hkp0 := kpath_of_wpath W B path _ Hpath
  wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z cv.stack'.len by word)]
  wp_apply hA
  try wp_auto
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = path.length - 1 := by word
  have Hli : path[path.length - 1]? = some rt := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (cv.stack'.len - W64 1) ∧
    sint.Z (cv.stack'.len - W64 1) < sint.Z cv.stack'.len from ⟨by word, by word⟩))]
  try wp_auto
  icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rt _ _ path (by word)
    (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr, Hsback⟩
  try wp_auto
  have Hset : path.set (sint.Z (cv.stack'.len - W64 1)).toNat rt = path := by
    have hlt : path.length - 1 < path.length := by omega
    have hget : path[path.length - 1] = rt := by
      rw [List.getElem?_eq_getElem hlt] at Hli; exact Option.some.inj Hli
    rw [Hix, ← hget]; exact List.set_getElem_self hlt
  by_cases Hrn : rt.node' = null
  · rw [decide_eq_true Hrn]
    try wp_auto
    ihave Hs := Hsback $$ %rt Hr
    rw [Hset]
    obtain ⟨r0, rest, Hpe⟩ : ∃ r0 rest, path = r0 :: rest := by
      cases path with
      | nil => exact absurd rfl Hne
      | cons a b => exact ⟨a, b, rfl⟩
    have Hhead := wpath_head W B _ r0 rest (Hpe ▸ Hpath)
    have Hp0 : path[(sint.Z (W64 0)).toNat]? = some r0 := by rw [Hpe]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cv.stack'.len
      from ⟨by decide, by word⟩))]
    icases ownSlice_elem_acc (sint.Z (W64 0)) r0 _ _ path (by decide) Hp0 $$ Hs with ⟨Hr0, Hs0back⟩
    try wp_auto
    wp_join iprop(∃ (n0 : Loc) (B0 : BRec) (st0 : TxStats), n_ptr ↦ n0 ∗ c_ptr ↦ cl ∗ cl ↦ cv ∗
        wctx W bl B0 txl pmap pm dqp ∗ structFieldRef Tx go!"stats" txl ↦ st0 ∗
        sliceIndexRef elemRef (sint.Z (W64 0)) cv.stack' ↦ r0 ∗ bktShape γ W B0 ∗
        ⌜bktClean W hwm bl B0 ∧ bktGrows B B0 ∧ resolve B0 B.ib.root' = some n0 ∧
          (B0.ns !! n0).isSome ∧ kpath W B0 B.ib.root' path ∧ bktExt W B B0 ∧
          (∀ k v, entryIn W B k v → entryIn W B0 k v)⌝)
      at next with [n c Hcl Hctx Hst Hr0 Hsh] as ⟨%n0, %B0, %st0, n, c, Hcl, Hctx, Hst, Hr0, Hsh, %Hj⟩
    · by_cases Hr0n : r0.node' = null
      · rw [decide_eq_true Hr0n]
        try wp_auto
        obtain ⟨Hres0, -, pg, Hpa0⟩ : resolve B B.ib.root' = none ∧ r0.node' = null ∧
            ∃ pg, wpageAt W B B.ib.root' = some (r0.page', pg) := by
          rcases Hhead.1 with ⟨l, h1, h2, -⟩ | h
          · exact absurd (h2 ▸ Hr0n) (resolve_ne_null W hwm bl B Hclean _ l h1)
          · exact h
        have Hrn0 := rootNode_null W hwm bl B Hclean Hres0
        obtain ⟨Hlen, Hinl⟩ := rootPage_facts W hwm bl B Hclean Hres0 _ pg Hpa0
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cv.stack'.len
          from ⟨by decide, by word⟩))]
        try wp_auto
        isimp only [wctx] at Hctx
        icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
        isimp only [bktOwn] at Hbk
        icases Hbk with ⟨Hbl, Hib, Hnm, Hbm, Hpo, Hns⟩
        isimp only [wView] at Hv
        icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
        icases wpageAt_acc (GF := GF) W B B.ib.root' r0.page' pg HvOK.1 Hpa0 Hinl
          (by intro h; rw [h] at Hlen; simp at Hlen) $$ [Hpv Hpo] with ⟨%dq, %Hcar, Hpg, Hpgback⟩
        · iframe
        have Hsrc := rootSrcOK W hwm bl B pm HvOK Hclean Hpmv Hres0 _ pg Hpa0 Hcar
        icases (page_header_bytes (hG := hG) _ dq pg Hlen Hcar).1 $$ Hpg with ⟨Hhd, Hrest⟩
        wp_apply hId _ (pageOf pg) dq $$ [Hhd] as Hhd
        · iframe
        ihave Hpg := (page_header_bytes (hG := hG) _ dq pg Hlen Hcar).2 $$ [Hhd Hrest]
        · iframe
        ihave Hpv := Hpgback $$ Hpg
        icases Hpv with ⟨Hpv, Hpo⟩
        rw [nodeSrcOK_id W B pm _ _ pg _ Hsrc, Hbl]
        try wp_auto
        wp_apply hnode W bl B txl st pmap pm dqp B.ib.root' null r0.page' pg _ HvOK Htx
          (fun l h => (Hclean.2.2.2.2.1 _ l h).1) (fun _ => ⟨Hsrc, Or.inl rfl⟩)
          $$ [Hbl Hib Hnm Hbm Hpo Hns Hdata Hpv Hfli Hst Hpf Hpm Hdb]
          as %l %B' %st' ⟨Hbk, Hv, Hst, Hpf, Hpm, Hdb, %Hres⟩
        · isplitl [Hbl Hib Hnm Hbm Hpo Hns]
          · unfold bktOwn; iframe
          isplitl [Hdata Hpv Hfli]
          · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
          iframe
        try wp_auto
        isplitl []
        · ipureintro; rfl
        obtain ⟨Hc', Hg', Hr', Hs', Hk'⟩ := rootStep W hwm bl B HvOK Hclean path Hpath Hres0 _ pg Hpa0
          l B' st st' Hres
        have Hext := ext_rootRes W hwm bl B Hclean Hres0 _ pg Hpa0 l B' st st' _ Hres
        ihave Hsh := bktShape_nodeRes γ W hwm bl B pm B.ib.root' null r0.page' pg _ l B' st st' HvOK Hclean
          (fun _ => ⟨Hsrc, Or.inl ⟨rfl, Hrn0, rfl⟩⟩) Hres $$ Hsh
        icases Hsh with ⟨Hsh, %Hf⟩
        iexists l, B', st'
        iframe
        isplitl [Hbk Hv Hpf Hpm Hdb]
        · unfold wctx; iframe
        ipureintro
        exact ⟨Hc', Hg', Hr', Hs', Hk', Hext, Hf.1⟩
      · rw [decide_eq_false Hr0n]
        try wp_auto
        obtain ⟨l0, Hres0, Hn0, -⟩ : ∃ l, resolve B B.ib.root' = some l ∧ r0.node' = l ∧ r0.page' = null := by
          rcases Hhead.1 with h | ⟨-, h, -⟩
          · exact h
          · exact absurd h Hr0n
        obtain ⟨r0r, Hr0r⟩ := resolve_ns W hwm bl B Hclean _ l0 Hres0
        isplitl []
        · ipureintro; rfl
        iexists r0.node', B, st
        iframe
        ipureintro
        refine ⟨Hclean, bktGrows_refl B, Hn0 ▸ Hres0, by rw [Hn0, Hr0r]; rfl,
          kpath_of_wpath W B path _ Hpath, bktExt_refl W B, fun _ _ h => h⟩
    obtain ⟨Hc0, Hg0, Hrs0, Hsm0, Hkp0', Hext0, Hent0⟩ := Hj
    ihave Hsh := bktShape_keys γ W B0 $$ Hsh
    icases Hsh with ⟨Hsh, %Hkeys0⟩
    ihave Hs := Hs0back $$ Hr0
    rw [list_set_lookup_self path _ r0 Hp0]
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) ≤ sint.Z (cv.stack'.len - W64 1) ∧ sint.Z (cv.stack'.len - W64 1) ≤ sint.Z cv.stack'.cap
      from ⟨by decide, by word, by word⟩))]
    icases (ownSlice_split_all (cv.stack'.len - W64 1) cv.stack' _ path ⟨by word, by word⟩).1 $$ Hs
      with ⟨Hpre, Hsuf⟩
    try wp_auto
    ihave %Hprel := ownSlice_len _ _ _ $$ Hpre
    have Hkn : sint.nat (cv.stack'.len - W64 1) = path.length - 1 := by word
    ihave IH : (∃ (j : w64) (nk : Loc) (Bk : BRec) (stk : TxStats) (pidk : w64) (rv : elemRef),
        "i" ∷ i_ptr ↦ j ∗ "ref" ∷ ref_ptr ↦ rv ∗ "n" ∷ n_ptr ↦ nk ∗
        "Hctx" ∷ wctx W bl Bk txl pmap pm dqp ∗ "Hst" ∷ structFieldRef Tx go!"stats" txl ↦ stk ∗
        "Hsh" ∷ bktShape γ W Bk ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z (cv.stack'.len - W64 1) ∧ bktClean W hwm bl Bk ∧
          bktGrows B Bk ∧ resolve Bk pidk = some nk ∧ (Bk.ns !! nk).isSome ∧
          kpath W Bk pidk (path.drop (sint.nat j)) ∧
          (∀ k v, entryIn W B k v → entryIn W Bk k v) ∧
          (∀ k, kroute W B k B.ib.root' path → ∃ bnd, bktKeysB W Bk bnd ∧
            keyIn (bnd nk).1 (bnd nk).2 k ∧ kroute W Bk k pidk (path.drop (sint.nat j))) ∧
          (∀ k P, pathKey W B k P B.ib.root' path → pathKey W Bk k P pidk (path.drop (sint.nat j)))⌝ : IProp GF)
      $$ [i ref n Hctx Hst Hsh]
    · iexists W64 0, n0, B0, st0, B.ib.root', zero_val elemRef
      simp only [named, show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
      iframe
      ipureintro
      refine ⟨by decide, by word, Hc0, Hg0, Hrs0, Hsm0, Hkp0', Hent0, fun k hk => ?_,
        fun k P hp => pathKey_ext W B B0 Hext0 k P path _ Hkp0 hp⟩
      obtain ⟨bnd, hb⟩ := Hkeys0
      have hib : B0.ib = B.ib := Hg0.2.1
      have hn0 : n0 = B0.bv.rootNode' :=
        resolve_root W hwm bl B0 Hc0 n0 (by rw [hib]; exact Hrs0)
      obtain ⟨rn, hrn⟩ := Option.isSome_iff_exists.1 Hsm0
      refine ⟨bnd, hb, ?_, kroute_ext W B B0 Hext0 k path _ hk⟩
      rw [hn0, bnd_root W B0 bnd hb rn (hn0 ▸ hrn)]
      exact keyIn_none k
    wp_for IH
    wp_if_destruct
    · obtain ⟨Hj0, Hjk, Hck, Hgk, Hrk, Hsk, Hkp, Hentk, Hkrk, Hpkk⟩ := Hj
      have Hjl : sint.nat j + 1 < path.length := by word
      have Hjk' : (sint.Z j).toNat < sint.nat (cv.stack'.len - W64 1) := by word
      obtain ⟨r', r2, rs, Hdr, Hdr1, Hr'⟩ := drop_cons2 path (sint.nat j) Hjl
      rw [Hdr] at Hkp
      obtain ⟨rk, Hrk'⟩ := resolve_ns W hwm bl Bk Hck pidk nk Hrk
      obtain ⟨Hleaf, Hidx, w, Hw, Hkp2, Hnn, p, pg, Hsrcw⟩ :=
        pathStep W hwm bl Bk pm HvOK Hck Hpmv pidk nk rk Hrk Hrk' r' r2 rs Hkp
      have Hrt : (List.take (sint.nat (cv.stack'.len - W64 1)) path)[(sint.Z j).toNat]? = some r' := by
        rw [List.getElem?_take_of_lt Hjk']; exact Hr'
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧
        sint.Z j < sint.Z (cv.stack'.len - W64 1 - W64 0) from ⟨Hj0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ r' Hj0 $$ [Hpre] as Hpre
      · iframe; ipureintro; exact Hrt
      try wp_auto
      isimp only [wctx] at Hctx
      icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
      icases bktOwn_node_acc W bl Bk nk rk Hrk' $$ Hbk with ⟨Hnd, Hback⟩
      isimp only [nodeOwn] at Hnd
      icases Hnd with ⟨Hn0, Hrest⟩
      try wp_auto
      rw [Hleaf]
      wp_apply hA
      try wp_auto
      ihave Hbk := Hback $$ %rk [Hn0 Hrest]
      · unfold nodeOwn; iframe
      rw [bktOwn_insert_same W bl Bk nk rk Hrk']
      try wp_auto
      have Htxk : Bk.bv.tx' = txl := (bktGrows_tx B Bk Hgk).trans Htx
      wp_apply hchild W bl Bk txl stk pmap pm dqp nk rk r'.index' w p pg Src.view HvOK Htxk Hrk'
        (Hck.2.2.2.2.2.2.2.1 nk rk Hrk').1 Hleaf Hidx Hw Hnn (fun h => (Hsrcw h).2)
        $$ [Hbk Hv Hst Hpf Hpm Hdb] as %l %B' %st' ⟨Hbk, Hv, Hst, Hpf, Hpm, Hdb, %Hres⟩
      · iframe
      try wp_auto
      have Hnk : nk ≠ null := resolve_ne_null W hwm bl Bk Hck pidk nk Hrk
      obtain ⟨Hc', Hg', Hkids', Hres', Hs'⟩ := childStep W hwm bl Bk HvOK Hck nk rk Hrk' Hleaf _ w Hw
        Hnk p pg Src.view l B' stk st' (fun h => ⟨(Hsrcw h).1, rfl⟩) Hres
      have Hext := ext_childRes W hwm bl Bk Hck nk rk Hrk' Hleaf w Hnk p pg Src.view l B' stk st'
        (fun h => (Hsrcw h).1) Hres
      ihave Hsh := bktShape_nodeRes γ W hwm bl Bk pm w.pgid nk p pg Src.view l B' stk st' HvOK Hck
        (fun h => ⟨(Hsrcw h).2, Or.inr ⟨_, rk, w, Hrk', Hleaf, Hw, rfl, h⟩⟩) Hres $$ Hsh
      icases Hsh with ⟨Hsh, %Hf⟩
      wp_for_post
      iframe
      iexists j + W64 1, l, B', st', w.pgid, r'
      iframe
      isplitl [Hbk Hv Hpf Hpm Hdb]
      · simp only [named]; unfold wctx; iframe
      ipureintro
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have Hroot' : Bk.ib.root' ≠ W64 0 := by
        intro h0; have := Hck.2.2.2.2.2.2.1 h0 nk rk Hrk'; rw [Hleaf] at this; cases this
      have Hkd : kidsAt W Bk pidk = some (false, rk.ws.map WEntry.pgid) := by
        unfold kidsAt; rw [Hrk]; simp [Hrk', Hleaf]
      have Hks : keysAt W Bk pidk = some (rk.ws.map WEntry.key) := by
        unfold keysAt; rw [Hrk]; simp [Hrk']
      have Hcw : ∀ cs c, kidsAt W Bk pidk = some (false, cs) → cs[(sint.Z r'.index').toNat]? = some c →
          c = w.pgid := by
        intro cs c h1 h2
        rw [Hkd] at h1; cases h1
        rw [List.getElem?_map, Hw] at h2; cases h2; rfl
      refine ⟨by word, by word, Hc', bktGrows_trans _ _ _ Hgk Hg', Hres', Hs', ?_,
        fun k v h => Hf.1 k v (Hentk k v h), fun k hk => ?_, fun k P hp => ?_⟩
      · rw [Hj1, Hdr1]
        exact kpath_mono W Bk B' Hkids' _ _ Hkp2
      · obtain ⟨bnd, hb, hin, hkr⟩ := Hkrk k hk
        rw [Hdr] at hkr
        obtain ⟨kss, cs, c, hks, hrt, hkd, hc, hrest⟩ := hkr
        have hcw := Hcw cs c hkd hc
        subst hcw
        rw [Hks] at hks; cases hks
        obtain ⟨bnd', hb', hag⟩ := Hf.2 bnd hb
        obtain ⟨rk', hrk', hws', hlf'⟩ := ns_childRes Bk bl w.pgid nk p pg Src.view l B' stk st' rk Hnk
          Hrk' Hres nk rk Hrk'
        have hnm' : B'.nm !! w.pgid = some l := by
          have := Hres'; unfold resolve at this
          rw [if_neg (show B'.ib.root' ≠ W64 0 by rw [Hg'.2.1]; exact Hroot')] at this
          exact this
        have hbl := bnd_child W hwm bl B' Hc' bnd' hb' nk rk' hrk' (by rw [hlf']; exact Hleaf) _ w
          (by rw [hws']; exact Hw) l hnm'
        refine ⟨bnd', hb', ?_, ?_⟩
        · rw [hbl, hag nk (by rw [Hrk']; rfl), hws']
          exact keyIn_route _ rk.ws _ k hin hrt
        · rw [Hj1, Hdr1]
          exact kroute_ext W Bk B' Hext k _ _ hrest
      · have hpk := Hpkk k P hp
        rw [Hdr] at hpk
        obtain ⟨cs, c, hkd, hc, hrest⟩ := hpk
        have hcw := Hcw cs c hkd hc
        subst hcw
        rw [Hj1, Hdr1]
        exact pathKey_ext W Bk B' Hext k P _ _ Hkp2 hrest
    · obtain ⟨Hj0, Hjk, Hck, Hgk, Hrk, Hsk, Hkp, Hentk, Hkrk, Hpkk⟩ := Hj
      have Hje : sint.nat j + 1 = path.length := by word
      obtain ⟨x, Hdx⟩ := drop_last1 path (sint.nat j) Hje
      rw [Hdx] at Hkp
      obtain ⟨rk, Hrk'⟩ := resolve_ns W hwm bl Bk Hck pidk nk Hrk
      have Hleaf := pathEnd W Bk pidk nk rk Hrk Hrk' x Hkp
      isimp only [wctx] at Hctx
      icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
      icases bktOwn_node_acc W bl Bk nk rk Hrk' $$ Hbk with ⟨Hnd, Hback⟩
      isimp only [nodeOwn] at Hnd
      icases Hnd with ⟨Hn0, Hrest⟩
      try wp_auto
      rw [Hleaf]
      wp_apply hA
      try wp_auto
      ihave Hbk := Hback $$ %rk [Hn0 Hrest]
      · unfold nodeOwn; iframe
      rw [bktOwn_insert_same W bl Bk nk rk Hrk']
      ihave Hs := (ownSlice_split_all (cv.stack'.len - W64 1) cv.stack' _ path ⟨by word, by word⟩).2
        $$ [Hpre Hsuf]
      · iframe
      ispecialize HΦ $$ %nk %Bk %stk
      iapply HΦ
      iframe
      isplitl [Hbk Hv Hpf Hpm Hdb]
      · unfold wctx; iframe
      ipureintro
      refine ⟨Hck, Hgk, ⟨rk, Hrk', Hleaf⟩, Hentk, fun k hk => ?_, fun k P hp r hr => ?_⟩
      · obtain ⟨bnd, hb, hin, -⟩ := Hkrk k hk
        exact ⟨bnd, hb, hin⟩
      · have hpk := Hpkk k P hp
        rw [Hdx] at hpk
        exact hpk.1 nk r Hrk hr
  · rw [decide_eq_false Hrn, Bool.not_false]
    try wp_auto
    obtain ⟨l, Hres, Hn, -⟩ : ∃ l, resolve B pid' = some l ∧ rt.node' = l ∧ rt.page' = null := by
      rcases Hra with h | ⟨-, h, -⟩
      · exact h
      · exact absurd h Hrn
    unfold kidsAt at Hkids
    rw [Hres] at Hkids
    obtain ⟨nrec, Hrec, Hrk⟩ := Option.map_eq_some_iff.1 Hkids
    simp only [Prod.mk.injEq] at Hrk
    isimp only [wctx] at Hctx
    icases Hctx with ⟨Hbk, Hv, Hpf, Hpm, Hdb⟩
    icases bktOwn_node_acc W bl B l nrec Hrec $$ Hbk with ⟨Hnd, Hback⟩
    isimp only [nodeOwn] at Hnd
    icases Hnd with ⟨Hn0, Hrest⟩
    wp_apply hisLeaf _ rt (DFrac.own 1) nrec.nv (DFrac.own 1) (DFrac.own 1) [] (fun h => absurd h Hrn)
      $$ [Hr Hn0] as ⟨Hr, Hn0⟩
    · simp only [Hrn, ↓reduceIte]; rw [Hn]; iframe
    simp only [Hrn, ↓reduceIte, Hrk.1]
    try wp_auto
    ihave Hs := Hsback $$ %rt Hr
    rw [Hset]
    rw [Hn]
    ihave Hbk := Hback $$ %nrec [Hn0 Hrest]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l nrec Hrec]
    ihave Hsh := bktShape_keys γ W B $$ Hsh
    icases Hsh with ⟨Hsh, %Hkeys⟩
    ispecialize HΦ $$ %l %B %st
    iapply HΦ
    iframe
    isplitl [Hbk Hv Hpf Hpm Hdb]
    · unfold wctx; iframe
    ipureintro
    refine ⟨Hclean, bktGrows_refl B, ⟨nrec, Hrec, Hrk.1⟩, fun _ _ h => h, fun k hk => ?_,
      fun k P hp r hr => ?_⟩
    · obtain ⟨bnd, hb⟩ := Hkeys
      refine ⟨bnd, hb, ?_⟩
      have := wpath_bnd W hwm bl B Hclean bnd hb k path _ Hpath hk Hroot (fun nk hnk => by
        have hn := resolve_root W hwm bl B Hclean nk hnk
        obtain ⟨rn, hrn⟩ := resolve_ns W hwm bl B Hclean _ nk hnk
        rw [hn, bnd_root W B bnd hb rn (hn ▸ hrn)]
        exact keyIn_none k) rt Hlast Hrn
      rw [Hn] at this; exact this
    · exact wpath_pathKey W B k P path _ Hpath hp rt Hlast Hrn r (by rw [Hn]; exact hr)

end proof

end bbolt
end EtcdGrove
end Perennial
