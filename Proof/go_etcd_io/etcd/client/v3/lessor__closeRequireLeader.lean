/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean` (item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__closeRequireLeader
public import Spec.google_golang_org.grpc.metadata.FromOutgoingContext

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

/-! ## Pure lemmas: the compaction of `ka.chs` -/

/-- A channel `closeRequireLeader` keeps (not set to `nil`). -/
def kaChLive (c : Loc) : Bool := !decide (c = null)

theorem crl_set_repl' {A : Type _} (pre : List A) (k M : Nat) (z x : A) (hA : pre.length = k)
    (hk : k < M) :
    (pre ++ List.replicate (M - k) z).set k x = (pre ++ [x]) ++ List.replicate (M - (k + 1)) z := by
  obtain ⟨j, hj⟩ : ∃ j, M - k = j + 1 := ⟨M - (k + 1), by omega⟩
  rw [hj, show M - (k + 1) = j by omega, ← hA]
  exact set_length_append_replicate pre j z x

theorem crl_filter_take_succ (pre : List Loc) (n : Nat) (h : n < pre.length) :
    (pre.take (n + 1)).filter kaChLive =
      (pre.take n).filter kaChLive ++ (if kaChLive (pre[n]'h) then [pre[n]'h] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.filter_append]
  cases hc : kaChLive (pre[n]'h) <;> simp [hc]

/-- The first scan's `pre` (the channels scanned, a closed one set to `nil`): each channel left is
the one at its index in `chs`. -/
def crlPreOk (pre chs : List Loc) : Prop :=
  ∀ (j : Nat) (x : Loc), pre[j]? = some x → x ≠ null → chs[j]? = some x

theorem crlPreOk_keep (pre chs : List Loc) (n : Nat) (h : n < chs.length) (hp : pre.length = n)
    (H : crlPreOk pre chs) : crlPreOk (pre ++ [chs[n]'h]) chs := by
  intro j x hj hx
  rcases Nat.lt_or_ge j pre.length with hl | hl
  · rw [List.getElem?_append_left hl] at hj; exact H j x hj hx
  · rw [List.getElem?_append_right hl] at hj
    rcases Nat.lt_or_ge (j - pre.length) 1 with h1 | h1
    · have h0 : j - pre.length = 0 := by omega
      rw [h0] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [show j = n by omega]
      exact List.getElem?_eq_getElem h
    · rw [List.getElem?_eq_none (by simp; omega)] at hj
      cases hj

theorem crlPreOk_null (pre chs : List Loc) (H : crlPreOk pre chs) : crlPreOk (pre ++ [null]) chs := by
  intro j x hj hx
  rcases Nat.lt_or_ge j pre.length with hl | hl
  · rw [List.getElem?_append_left hl] at hj; exact H j x hj hx
  · rw [List.getElem?_append_right hl] at hj
    rcases Nat.lt_or_ge (j - pre.length) 1 with h1 | h1
    · have h0 : j - pre.length = 0 := by omega
      rw [h0] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact absurd hj.symm hx
    · rw [List.getElem?_eq_none (by simp; omega)] at hj
      cases hj

/-- Nothing closed: the scan's `pre` is `chs`. -/
theorem crlPreOk_all (pre chs : List Loc) (hl : pre.length = chs.length)
    (hf : pre.filter kaChLive = pre) (H : crlPreOk pre chs) : pre = chs := by
  apply List.ext_getElem? 
  intro j
  rcases hj : pre[j]? with _ | x
  · rw [List.getElem?_eq_none_iff] at hj
    exact (List.getElem?_eq_none (by omega)).symm
  · have hmem : x ∈ pre := List.mem_of_getElem? hj
    rw [← hf] at hmem
    have hx : x ≠ null := by
      have := (List.mem_filter.1 hmem).2
      simpa [kaChLive] using this
    exact (H j x hj hx).symm

theorem crl_filter_take_le (pre : List Loc) (n : Nat) :
    ((pre.take n).filter kaChLive).length ≤ (pre.filter kaChLive).length :=
  ((List.take_sublist n pre).filter kaChLive).length_le

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A channel with its token is not `nil`. -/
theorem chanTok_not_null (ch : Loc) : chanTok (GF := GF) ch ⊢ chanTok ch ∗ ⌜ch ≠ null⌝ := by
  iintro Htok
  unfold chanTok
  icases Htok with ⟨%γ, %γc, #Hch, #Hinv, Hg⟩
  ihave %Hnn := isChan_not_null $$ Hch
  isplitl
  · iexists γ, γc
    iframe #
    iframe
  · ipureintro; exact Hnn

/-- **A channel kept** (not closed): its token moves from the channels not yet scanned to the
kept ones. -/
theorem crl_keep (pre chs : List Loc) (n : Nat) (h : n < chs.length) :
    ⊢ ([∗list] c ∈ pre.filter kaChLive, chanTok (GF := GF) c) -∗
      ([∗list] c ∈ chs.drop n, chanTok (GF := GF) c) -∗
    ([∗list] c ∈ (pre ++ [chs[n]'h]).filter kaChLive, chanTok (GF := GF) c) ∗
      ([∗list] c ∈ chs.drop (n + 1), chanTok (GF := GF) c) ∗
      ⌜(pre ++ [chs[n]'h]).filter kaChLive = pre.filter kaChLive ++ [chs[n]'h]⌝ := by
  iintro Htp Htd
  rw [List.drop_eq_getElem_cons h]
  icases BigSepL.bigSepL_cons.1 $$ Htd with ⟨Htok, Htd⟩
  icases chanTok_not_null _ $$ Htok with ⟨Htok, %Hnn⟩
  have hf : (pre ++ [chs[n]'h]).filter kaChLive = pre.filter kaChLive ++ [chs[n]'h] := by
    rw [List.filter_append]; simp [kaChLive, Hnn]
  rw [hf]
  iframe Htd
  isplitl
  · iapply BigSepL.bigSepL_snoc.2
    iframe
  · ipureintro; rfl

/-- **A channel closed**: its token, from the channels not yet scanned. -/
theorem crl_take (chs : List Loc) (n : Nat) (h : n < chs.length) :
    ([∗list] c ∈ chs.drop n, chanTok (GF := GF) c) ⊢
    chanTok (GF := GF) (chs[n]'h) ∗ ([∗list] c ∈ chs.drop (n + 1), chanTok (GF := GF) c) := by
  rw [List.drop_eq_getElem_cons h]
  exact BigSepL.bigSepL_cons.1

theorem crl_filter_null (pre : List Loc) :
    (pre ++ [null]).filter kaChLive = pre.filter kaChLive := by
  simp [List.filter_append, kaChLive]

set_option hygiene false in
/-- The scan's step past a channel it keeps (`continue`): the loop invariant at `n + 1`. -/
local macro "crl_keep_tac" : tactic => `(tactic| (
  have Hlt2 : sint.nat n < chs.length := by omega
  icases crl_keep pre chs (sint.nat n) Hlt2 $$ Htp Htd with ⟨Htp, Htd, %Hf⟩
  wp_for_post
  iframe
  iexists n + W64 1, _, r, _, pre ++ [chs[sint.nat n]'Hlt2]
  rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, ← append_drop_eq_snoc pre chs (sint.nat n) Hlt2]
  iframe
  ipureintro
  rw [Hf]
  simp only [List.length_append, List.length_singleton]
  refine ⟨crlPreOk_keep pre chs (sint.nat n) Hlt2 Hn.2.2.1 Hpre, by word, by word, by omega, by word,
    by omega⟩))

/-- **`rpctypes`' fact gives the metadata key and value** `closeRequireLeader` compares with. -/
theorem requireLeaderKeys_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢
      (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ k) ∗
      (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ k) := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hkl, #Hhl, -, -, -, -, -, -⟩
  isplitl
  · iexact Hkl
  · iexact Hhl

set_option maxHeartbeats 0 in
theorem lessor.closeRequireLeader.wp_proof
    (wp_FromOutgoing : metadata.FromOutgoingContext.spec (GF := GF) (hG := hG)) :
    lessor.closeRequireLeader.spec (GF := GF) (hG := hG) := by
  intro l addr
  wp_start as #Hl
  iunfold lessorAt at Hl
  icases Hl with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hmd : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata $$ []
  · iPkgInit
  ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave ⟨⟨%kl, #Hkl⟩, ⟨%hl, #Hhl⟩⟩ := requireLeaderKeys_of_init $$ Hrp
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) =>
      iprop(∃ k0 : Loc, "HM" ∷ ([∗map] _id ↦ ka ∈ mm, kaOwn (GF := GF) γr ka) ∗ "ka" ∷ ka_ptr ↦ k0))
    _ _ _ mref mm (DFrac.own 1) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [HM ka]
  · iexists _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
    iNamed HP
    icases (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
      (m := mm) Hmv).1 $$ HM with ⟨Hka, HM⟩
    iunfold kaOwn at Hka
    icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd, %γkd, Hchs, Hchsl, Hchscap,
      Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd, Hpend, Htoks, #Hctxok, #Hpair⟩
    (try wp_auto)
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => gi
    ihave %Hcl := ownSlice_len $$ Hctxsl
    ihave %Hchl := ownSlice_len $$ Hchsl
    ihave IH : iprop(∃ (n iv r : w64) (c0 : GoInterface) (pre : List Loc),
        "i" ∷ i_ptr ↦ n ∗ "gi" ∷ igo ↦ iv ∗ "c" ∷ ctx_ptr ↦ c0 ∗ "reqIdxs" ∷ reqIdxs_ptr ↦ r ∗
        "Hchsl" ∷ chsS ↦* (pre ++ chs.drop (sint.nat n)) ∗
        "Htp" ∷ ([∗list] c ∈ pre.filter kaChLive, chanTok (GF := GF) c) ∗
        "Htd" ∷ ([∗list] c ∈ chs.drop (sint.nat n), chanTok (GF := GF) c) ∗
        "%Hpre" ∷ ⌜crlPreOk pre chs⌝ ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ctxs.length ∧ pre.length = sint.nat n ∧
          0 ≤ sint.Z r ∧ sint.nat r + (pre.filter kaChLive).length = sint.nat n⌝)
      $$ [i gi ctx reqIdxs Hchsl Htoks]
    · iexists W64 0, _, W64 0, _, []
      simp only [named, List.filter_nil, List.nil_append, List.length_nil]
      iframe
      isplitl
      · iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; refine ⟨fun j x h => by simp at h, by word, by word, by word, by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < ctxs.length := by word
      have Hc : ctxs[sint.nat n]? = some (ctxs[sint.nat n]'Hlt) := List.getElem?_eq_getElem Hlt
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ctxsS.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      wp_apply wp_load_slice_index ctxsS (sint.Z n) _ (DFrac.own 1) (ctxs[sint.nat n]'Hlt) Hn.1
        $$ [Hctxsl] as Hctxsl
      · iframe; ipureintro; exact Hc
      (try wp_auto)
      ihave #Hco := BigSepL.bigSepL_lookup (Φ := fun _ c => kaCtxOk (GF := GF) c) Hc $$ Hctxok
      iunfold kaCtxOk at Hco
      icases Hco with ⟨%ci, %cdi, %Hcieq, #Hci⟩
      rw [Hcieq]
      (try wp_auto)
      wp_apply wp_FromOutgoing ci cdi $$ [$Hmd $Hci] as %md %ok Hres
      icases Hres with (%Hok | ⟨%mdm, Hmdm, Hvs⟩)
      · subst Hok
        (try wp_auto)
        crl_keep_tac
      cases ok
      · (try wp_auto)
        crl_keep_tac
      (try wp_auto)
      wp_apply wp_map_lookup1 go.string _ md mdm kl (DFrac.own 1) $$ [$Hmdm] as Hmdm
      (try wp_auto)
      rcases Hks : mdm !! kl with _ | sl
      · simp only [Option.getD_none]
        (try wp_auto)
        crl_keep_tac
      simp only [Option.getD_some]
      ihave ⟨%vs, Hvsl⟩ := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs)) Hks $$ Hvs
      ihave %Hvsl' := ownSlice_len $$ Hvsl
      wp_if_destruct
      · (try wp_auto)
        crl_keep_tac
      have Hvlt : 0 < vs.length := by word
      rw [ite_eq_left ⟨by word, by word⟩]
      wp_apply wp_load_slice_index sl (sint.Z (W64 0)) vs (DFrac.own 1) (vs[0]'Hvlt) (by word)
        $$ [Hvsl] as Hvsl
      · iframe; ipureintro; exact List.getElem?_eq_getElem Hvlt
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        crl_keep_tac
      -- a context that requires a leader: close its channel, set it to `nil`
      have Hlt2 : sint.nat n < chs.length := by omega
      have Hpl : pre.length = sint.nat n := Hn.2.2.1
      have Hcl2 : (pre ++ chs.drop (sint.nat n)).length = chs.length := by
        simp only [List.length_append, List.length_drop]; omega
      ihave %Hchl2 := ownSlice_len $$ Hchsl
      (try wp_auto)
      rw [ite_eq_left ⟨Hn.1, by word⟩]
      wp_apply wp_load_slice_index chsS (sint.Z n) _ (DFrac.own 1) (chs[sint.nat n]'Hlt2) Hn.1
        $$ [Hchsl] as Hchsl
      · iframe; ipureintro; exact getElem?_append_drop_self pre chs _ Hlt2 Hpl
      icases crl_take chs (sint.nat n) Hlt2 $$ Htd with ⟨Htok, Htd⟩
      (try wp_auto)
      wp_apply wp_chanTok_close (chs[sint.nat n]'Hlt2) $$ [$Htok]
      (try wp_auto)
      rw [ite_eq_left ⟨Hn.1, by word⟩]
      wp_apply wp_store_slice_index (V := GoChan) chsS (sint.Z n) _ _ $$ [$Hchsl] as Hchsl
      · ipureintro; constructor <;> word
      rw [show (sint.Z n).toNat = sint.nat n from rfl, set_append_drop_self pre chs (sint.nat n) _ Hlt2 Hpl]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _, r + W64 1, _, pre ++ [null]
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, crl_filter_null]
      iframe
      ipureintro
      simp only [List.length_append, List.length_singleton]
      refine ⟨crlPreOk_null pre chs Hpre, by word, by word, by omega, by word, by word⟩
    have HnL : sint.nat n = chs.length := by word
    rw [HnL, List.drop_length, List.append_nil]
    wp_if_destruct
    · -- nothing closed: `ka.chs` unchanged
      have Hf : pre.filter kaChLive = pre :=
        List.filter_eq_self.2 (List.length_filter_eq_length_iff.1 (by word))
      rw [Hf]
      have Hpc : pre = chs := crlPreOk_all pre chs (by omega) Hf Hpre
      ihave #Hpair2 : kaPaired (GF := GF) γr pre ctxs $$ []
      · rw [Hpc]; iexact Hpair
      (try wp_auto)
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists v
      simp only [named]
      iframe
      iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
        (m := mm) Hmv).2
      iframe HM
      unfold kaOwn
      iexists chsS, ctxsS, pre, ctxs, dl, nk, kd, γkd
      iframe
      iframe #
      ipureintro; omega
    have Hr : sint.nat r + (pre.filter kaChLive).length = chs.length := by omega
    (try wp_auto)
    wp_apply wp_slice_make2 (V := GoChan) (chsS.len - r) $$ [] as %nchS ⟨Hnchl, Hnchcap⟩
    · ipureintro; word
    have HM' : sint.nat (chsS.len - r) = (pre.filter kaChLive).length := by word
    rw [HM']
    ihave %Hnchlen := ownSlice_len $$ Hnchl
    rw [List.length_replicate] at Hnchlen
    (try wp_auto)
    wp_apply wp_slice_make2 (V := GoInterface) nchS.len $$ [] as %nctS ⟨Hnctl, Hnctcap⟩
    · ipureintro; word
    rw [← Hnchlen.1]
    ihave %Hnctlen := ownSlice_len $$ Hnctl
    rw [List.length_replicate] at Hnctlen
    (try wp_auto)
    rename_i igo2
    irename : (igo2 ↦ zero_val w64 : IProp GF) => gi2
    have HpL : pre.length = chs.length := by omega
    ihave IH : iprop(∃ (n2 iv2 k : w64) (cs : List GoInterface),
        "i" ∷ i_ptr ↦ n2 ∗ "gi2" ∷ igo2 ↦ iv2 ∗ "newIdx" ∷ newIdx_ptr ↦ k ∗
        "Hnchl" ∷ nchS ↦* ((pre.take (sint.nat n2)).filter kaChLive ++
          List.replicate ((pre.filter kaChLive).length - sint.nat k) (zero_val GoChan)) ∗
        "Hnctl" ∷ nctS ↦* (cs ++
          List.replicate ((pre.filter kaChLive).length - sint.nat k) (zero_val GoInterface)) ∗
        "Hcs" ∷ ([∗list] c ∈ cs, kaCtxOk (GF := GF) c) ∗
        "#Hcp" ∷ kaPaired (GF := GF) γr ((pre.take (sint.nat n2)).filter kaChLive) cs ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z n2 ∧ sint.nat n2 ≤ pre.length ∧
          ((pre.take (sint.nat n2)).filter kaChLive).length = sint.nat k ∧ cs.length = sint.nat k ∧
          0 ≤ sint.Z k⌝)
      $$ [i gi2 newIdx Hnchl Hnctl]
    · iexists W64 0, _, W64 0, []
      simp only [named, List.nil_append, List.length_nil]
      rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
      iframe
      isplitl
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · simp only [List.take_zero, List.filter_nil]
        iapply kaPaired_nil
      ipureintro; refine ⟨by word, by omega, rfl, rfl, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n2 < pre.length := by word
      rw [ite_eq_left ⟨Hk.1, by word⟩]
      wp_apply wp_load_slice_index chsS (sint.Z n2) _ (DFrac.own 1) (pre[sint.nat n2]'Hlt) Hk.1
        $$ [Hchsl] as Hchsl
      · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt
      (try wp_auto)
      rw [ite_eq_left ⟨Hk.1, by word⟩]
      wp_apply wp_load_slice_index chsS (sint.Z n2) _ (DFrac.own 1) (pre[sint.nat n2]'Hlt) Hk.1
        $$ [Hchsl] as Hchsl
      · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt
      have Hft := crl_filter_take_succ pre (sint.nat n2) Hlt
      (try wp_auto)
      wp_if_destruct
      · -- a closed channel: skipped
        have Hdead : kaChLive (pre[sint.nat n2]'Hlt) = false := by simp [kaChLive, Hif, chan.nil]
        rw [Hdead] at Hft
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at Hft
        (try wp_auto)
        wp_for_post
        iframe
        iexists n2 + W64 1, _, k, cs
        rw [show sint.nat (n2 + W64 1) = sint.nat n2 + 1 by word, Hft]
        iframe
        isplitr
        · iexact Hcp
        ipureintro; refine ⟨by word, by word, by omega, by omega, by omega⟩
      have Hlive : kaChLive (pre[sint.nat n2]'Hlt) = true := by
        simp only [chan.nil] at Hif; simp [kaChLive, Hif]
      rw [Hlive] at Hft
      simp only [↓reduceIte] at Hft
      have HkM : sint.nat k < (pre.filter kaChLive).length := by
        have h1 := crl_filter_take_le pre (sint.nat n2 + 1)
        rw [Hft, List.length_append, List.length_singleton] at h1
        omega
      have Hlt3 : sint.nat n2 < ctxs.length := by omega
      (try wp_auto)
      rw [ite_eq_left ⟨by word, by word⟩]
      (try wp_auto)
      rw [ite_eq_left ⟨by word, by word⟩]
      (try wp_auto)
      rw [ite_eq_left ⟨Hk.1, by word⟩]
      wp_apply wp_load_slice_index chsS (sint.Z n2) _ (DFrac.own 1) (pre[sint.nat n2]'Hlt) Hk.1
        $$ [Hchsl] as Hchsl
      · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt
      (try wp_auto)
      rw [ite_eq_left ⟨Hk.1, by word⟩]
      wp_apply wp_load_slice_index ctxsS (sint.Z n2) _ (DFrac.own 1) (ctxs[sint.nat n2]'Hlt3) Hk.1
        $$ [Hctxsl] as Hctxsl
      · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt3
      (try wp_auto)
      have HA := Hk.2.2.1
      wp_apply wp_store_slice_index (V := GoChan) nchS (sint.Z k) _ _ $$ [$Hnchl] as Hnchl
      · ipureintro
        simp only [List.length_append, List.length_replicate]
        constructor <;> word
      wp_apply wp_store_slice_index (V := GoInterface) nctS (sint.Z k) _ _ $$ [$Hnctl] as Hnctl
      · ipureintro
        simp only [List.length_append, List.length_replicate]
        constructor <;> word
      rw [show (sint.Z k).toNat = sint.nat k from rfl,
        crl_set_repl' _ (sint.nat k) _ _ _ HA HkM, crl_set_repl' _ (sint.nat k) _ _ _ Hk.2.2.2.1 HkM]
      ihave #Hco := BigSepL.bigSepL_lookup (Φ := fun _ c => kaCtxOk (GF := GF) c)
        (List.getElem?_eq_getElem Hlt3) $$ Hctxok
      -- the alignment: the channel kept, `pre[i]`, is `chs[i]`, registered with `ctxs[i]`, the
      -- context copied (at upstream's code, `ctxs[newIdx]`, this pair would not be registered)
      have Hpl3 : chs[sint.nat n2]? = some (pre[sint.nat n2]'Hlt) :=
        Hpre _ _ (List.getElem?_eq_getElem Hlt) (by simpa [kaChLive] using Hlive)
      ihave #Hkr := kaPaired_get γr chs ctxs (sint.nat n2) _ _ Hpl3
        (List.getElem?_eq_getElem Hlt3) $$ Hpair
      ihave #Hcp' := kaPaired_snoc γr _ cs _ _ (by rw [Hk.2.2.1, Hk.2.2.2.1]) $$ [$Hcp $Hkr]
      iclear Hcp
      (try wp_auto)
      wp_for_post
      iframe
      iexists n2 + W64 1, _, k + W64 1, cs ++ [ctxs[sint.nat n2]'Hlt3]
      rw [show sint.nat (n2 + W64 1) = sint.nat n2 + 1 by word,
        show sint.nat (k + W64 1) = sint.nat k + 1 by word, Hft]
      iframe
      isplit
      · iapply BigSepL.bigSepL_singleton.2
        iexact Hco
      isplitr
      · iexact Hcp'
      ipureintro
      simp only [List.length_append, List.length_singleton]
      refine ⟨by word, by word, by omega, by omega, by word⟩
    -- the compaction done: `ka.chs`, `ka.ctxs` replaced
    have Hn2 : sint.nat n2 = pre.length := by word
    have HkM : sint.nat k = (pre.filter kaChLive).length := by
      rw [← Hk.2.2.1, Hn2, List.take_length]
    rw [Hn2, List.take_length, HkM, Nat.sub_self]
    simp only [List.replicate_zero, List.append_nil]
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists v
    simp only [named]
    iframe
    iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
      (m := mm) Hmv).2
    iframe HM
    unfold kaOwn
    iexists nchS, nctS, pre.filter kaChLive, cs, dl, nk, kd, γkd
    iframe
    iframe #
    ipureintro; omega
  iintro HP Hm
  iNamed HP
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hreg]
  · inext; unfold lessorInv; iexists mref, mm, stv, scf, e; iframe; iframe #
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
