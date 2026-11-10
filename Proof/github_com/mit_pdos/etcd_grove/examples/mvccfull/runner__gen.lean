/- Lean-first (no Rocq counterpart). The proof of `runner.gen`: proved.

The outline: `pick` of `Mix.Op`; per kind, `genKey`, `genEnd`, `newVal`, `genLease`,
`genSubs`, `genRange`, `choose`, `pick` of `Mix.CompactAt`; the struct allocated, its slices
persisted (`opIs`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genSubs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section lemmas
variable [GooseExts]

theorem opValid_put {ks : List GoString} {s : MSt} {o : OpM} (hk : o.kind = kPut)
    (hkey : o.key ∈ ks) (hl : o.lease = W64 0 ∨ o.lease ∈ s.leases) : opValid ks s o := by
  unfold opValid; rw [hk]
  exact ⟨by decide, by decide, fun _ => ⟨hkey, hl⟩, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem opValid_plain {ks : List GoString} {s : MSt} {o : OpM} (K : w64) (hk : o.kind = K)
    (hK : K = kDelete ∨ K = kCommit ∨ K = kRead ∨ K = kLeases) : opValid ks s o := by
  unfold opValid; rw [hk]
  rcases hK with rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem opValid_txn {ks : List GoString} {s : MSt} {o : OpM} (hk : o.kind = kTxn)
    (hw : o.write = true → subsOk ks s.leases o.subs) : opValid ks s o := by
  unfold opValid; rw [hk]
  exact ⟨by decide, by decide, fun h => absurd h (by decide), fun _ => hw,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem opValid_grant {ks : List GoString} {s : MSt} {o : OpM} (hk : o.kind = kGrant)
    (h0 : 0 < sint.Z o.id) (hg : ∀ id ∈ s.granted, sint.Z id < sint.Z o.id) : opValid ks s o := by
  unfold opValid; rw [hk]
  exact ⟨by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun _ => ⟨h0, hg⟩, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem opValid_revoke {ks : List GoString} {s : MSt} {o : OpM} (hk : o.kind = kRevoke)
    (hid : o.id ∈ s.leases) : opValid ks s o := by
  unfold opValid; rw [hk]
  exact ⟨by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ => hid, fun h => absurd h (by decide)⟩

theorem opValid_compact {ks : List GoString} {s : MSt} {o : OpM} (hk : o.kind = kCompact)
    (hr : 1 ≤ sint.Z o.rev) : opValid ks s o := by
  unfold opValid; rw [hk]
  exact ⟨by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => hr⟩

theorem sint_pos_of (n : Nat) (h1 : 1 ≤ n) (h2 : n + 2 < 2 ^ 63) : 1 ≤ sint.Z (W64 (n : Int)) := by
  word

theorem zip_fst_snd {α β : Type} (xs : List (α × β)) :
    (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem one_plus_choose3 (cn : w64) (h : 0 ≤ sint.Z cn ∧ (0 < sint.Z (W64 3) → sint.Z cn < sint.Z (W64 3)) ∧
    (sint.Z (W64 3) ≤ 0 → cn = W64 0)) : 1 ≤ sint.Z (W64 1 + cn) ∧ sint.Z (W64 1 + cn) ≤ 3 := by
  have := h.2.1 (by decide)
  have : sint.Z (W64 3) = 3 := by decide
  have := h.1
  constructor <;> word

theorem sint_succ (n : w64) (h0 : 0 ≤ sint.Z n) (h1 : sint.Z n + 1 < 2 ^ 63) :
    sint.Z (n + W64 1) = sint.Z n + 1 := by word

theorem compact_rev_ok (r : Nat) (cr : w64) (hr : r + 2 < 2 ^ 63)
    (h : 0 ≤ sint.Z cr ∧ (0 < sint.Z (W64 (r : Int) + W64 1) → sint.Z cr < sint.Z (W64 (r : Int) + W64 1)) ∧
      (sint.Z (W64 (r : Int) + W64 1) ≤ 0 → cr = W64 0)) : 1 ≤ sint.Z (W64 1 + cr) := by
  have h1 : sint.Z (W64 (r : Int) + W64 1) = r + 1 := by word
  have := h.2.1 (by omega)
  have := h.1
  word

theorem sint_nat_lt (r : Nat) (hr : r + 2 < 2 ^ 63) : sint.Z (W64 (r : Int)) + 1 < 2 ^ 63 := by
  word

theorem w64_eq_zero_of (w : w64) (h : sint.Z w = 0) : w = W64 0 := by word

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The model of an op with no slices (a grant, a revoke, a compaction, a commit, a check). -/
def plainOp (v : op) : OpM :=
  ⟨v.kind', [], [], true, v.val', v.lease', ⟨[], [], true, zeroValDef⟩, v.write', v.shared', [], v.id',
    v.rev', v.wait'⟩

theorem opIs_plain (p : Loc) (v : op) (hk : v.key' = slice.nil) (he : v.end' = slice.nil)
    (hq : v.q' = zeroValDef) (hs : v.subs' = slice.nil) :
    (p ↦□ v : IProp GF) ⊢ opIs p (plainOp v) := by
  iintro #Hp
  iunfold opIs
  iexists v, []
  rw [hk, he, hq, hs]
  simp only [plainOp]
  iframe #
  isplitr; · iapply ownSlice_nil
  isplitr; · iapply ownSlice_nil
  isplitr
  · iunfold rangeIs
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSlice_nil
    ipureintro; exact ⟨rfl, rfl⟩
  isplitr; · iapply ownSlice_nil
  isplitr; · ipureintro; rfl
  isplitr; · rw [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
  ipureintro; simp

theorem runner.gen.wp_proof
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_newVal : runner.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : runner.genLease.spec (GF := GF) (hG := hG))
    (wp_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genSubs : runner.genSubs.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG)) :
    runner.gen.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh mp s sl nl nv hnl0 hnl1 hnlg hnv0 hnv1 hrev hc0 hc1 hrpos
  wp_start as ⟨#Hctx, Hrv, Hc, Hls, Hsl, Hnl, Hnv⟩
  iapply wp_fupd
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, #Hrc, -, -, -, -, -, -, -, -, ⟨%wo, #Hwo⟩, ⟨%wc, #Hwc⟩, -, -⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, -, Hks, -⟩
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hne⟩
  iunfold runnerCfg at Hrc
  icases Hrc with ⟨Hmix, -⟩
  iunfold runnerRangeMix at Hmix
  icases Hmix with ⟨#Hcfg, %wrr, #Hwrr⟩
  icases typedPointsto_split _ _ _ $$ Hcfg with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  icases typedPointsto_split _ _ _ $$ Mix with #Hmixf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmixf
  wp_auto
  wp_apply wp_pick cfg.Mix'.Op' wo DFrac.discard (W64 9) $$ [Hwo] as %sw ⟨-, %Hsw⟩
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · -- a put
    (try wp_auto)
    wp_apply wp_genKey x ks as %ksl ⟨%kk, Hk, %Hkk⟩
    · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
    imod ownSlice_persist $$ Hk with #Hk
    (try wp_auto)
    wp_apply wp_newVal x cfg nv hnv0 (by omega) $$ [Hnv] as %vl Hnv
    · iframe; iexact Hcfg
    (try wp_auto)
    wp_apply wp_genLease x mp sl s.leases $$ [Hls Hsl] as %l ⟨Hls, Hsl, %Hl⟩
    · iframe
    (try wp_auto)
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
    imodintro
    iapply HΦ
    iframe
    iexists ⟨kPut, kk, [], true, vl, l, ⟨[], [], true, zeroValDef⟩, false, false, [], 0, 0, false⟩
    iframe
    isplitl
    · iunfold opIs
      iexists _, []
      iframe #
      isplitr; · iapply ownSlice_nil
      isplitr
      · iunfold rangeIs
        isplitr; · iapply ownSlice_nil
        isplitr; · iapply ownSlice_nil
        ipureintro; exact ⟨rfl, rfl⟩
      isplitr; · iapply ownSlice_nil
      isplitr; · ipureintro; rfl
      isplitr; · rw [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ipureintro
    have hnvs := sint_succ nv hnv0 (by omega)
    exact ⟨opValid_put rfl Hkk Hl, (by simp [kGrant, plainOp]), by omega, by omega⟩
  · (try wp_auto)
    wp_if_destruct
    · -- a delete
      (try wp_auto)
      wp_apply wp_genKey x ks as %ksl ⟨%kk, Hk, %Hkk⟩
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
      imod ownSlice_persist $$ Hk with #Hk
      (try wp_auto)
      wp_apply wp_genEnd x ks as %esl ⟨%e, He, %He⟩
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
      imod ownSlice_persist $$ He with #He
      (try wp_auto)
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
      imodintro
      iapply HΦ
      iframe
      iexists ⟨kDelete, kk, e, decide (esl = slice.nil), [], 0, ⟨[], [], true, zeroValDef⟩, false,
        false, [], 0, 0, false⟩
      iframe
      isplitl
      · iunfold opIs
        iexists _, []
        iframe #
        isplitr
        · iunfold rangeIs
          isplitr; · iapply ownSlice_nil
          isplitr; · iapply ownSlice_nil
          ipureintro; exact ⟨rfl, rfl⟩
        isplitr; · iapply ownSlice_nil
        isplitr; · ipureintro; rfl
        isplitr; · rw [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
        ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ipureintro
      exact ⟨opValid_plain kDelete rfl (Or.inl rfl), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
    · (try wp_auto)
      wp_if_destruct
      · -- a transaction
        (try wp_auto)
        wp_apply wp_genKey x ks as %ksl ⟨%kk, Hk, %Hkk⟩
        · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
        imod ownSlice_persist $$ Hk with #Hk
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %cw -
        (try wp_auto)
        wp_if_destruct
        · -- a write transaction
          (try wp_auto)
          wp_apply wp_choose (W64 2) as %cs -
          (try wp_auto)
          wp_apply wp_genSubs x ks cfg mp (W64 (s.rev : Int)) (W64 s.crev) sl s.leases nv hnv0 hnv1
              (sint_nat_lt s.rev hrev) $$ [Hrv Hc Hls Hsl Hnv]
            as %ss ⟨Hrv, Hc, Hls, Hsl, %svs, %sms, %nv', #Hss, #Hsubs, Hnv, %Hsms⟩
          · iframe
            isplitl
            · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
            · iunfold runnerRangeMix; iframe #
          (try wp_auto)
          imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
          imodintro
          iapply HΦ
          iframe
          iexists ⟨kTxn, [], [], true, [], 0, ⟨kk, [], true, zeroValDef⟩, true, decide (cs = W64 0), sms,
            0, 0, false⟩
          iframe
          isplitl
          · iunfold opIs
            iexists _, svs
            iframe #
            isplitr; · iapply ownSlice_nil
            isplitr; · iapply ownSlice_nil
            isplitr
            · iunfold rangeIs
              iframe #
              isplitr; · iapply ownSlice_nil
              ipureintro; exact ⟨rfl, rfl⟩
            isplitr; · ipureintro; exact Hsms.1
            ipureintro; simp
          ipureintro
          exact ⟨opValid_txn rfl (fun _ => Hsms.2.2.2.1), (by simp [kGrant, plainOp]), Hsms.2.2.2.2.1, Hsms.2.2.2.2.2⟩
        · -- a read-only transaction
          (try wp_auto)
          wp_apply wp_choose (W64 3) as %cn %Hcn
          (try wp_auto)
          have hn3 := one_plus_choose3 cn Hcn
          ihave HI : (∃ (jj : w64) (ssl : GoSlice) (xs : List (subOp × SubM)),
              "j" ∷ j_ptr ↦ jj ∗
              "Hop" ∷ «$r0_ptr» ↦ (op.mk (W64 2) slice.nil slice.nil [] 0
                (rangeReq.mk ksl slice.nil zeroValDef) false false ssl 0 0 false) ∗
              "Hss" ∷ ssl ↦* xs.map Prod.fst ∗ "Hssc" ∷ ownSliceCap subOp ssl (DFrac.own 1) ∗
              "#Hxs" ∷ ([∗list] y ∈ xs, subIs y.1 y.2) ∗
              "HΦ" ∷ (∀ p : Loc, (mF go!"rev" mp ↦ (W64 (s.rev : Int)) ∗ mF go!"cmp" mp ↦ (W64 s.crev) ∗
                mF go!"leases" mp ↦ sl ∗ sl ↦* s.leases ∗
                ∃ (o : OpM) (nl' nv' : w64), opIs p o ∗ rF go!"nextLease" x ↦ nl' ∗
                  rF go!"vals" x ↦ nv' ∗
                  ⌜opValid ks s o ∧ (if o.kind = kGrant then o.id = nl + W64 1 ∧ nl' = nl + W64 1 else nl' = nl) ∧
                    sint.Z nv ≤ sint.Z nv' ∧ sint.Z nv' ≤ sint.Z nv + 3⌝) -∗ Φ #p) ∗
              "%Hinv" ∷ ⌜xs.length = sint.nat jj ∧ 0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z (W64 1 + cn)⌝ :
                IProp GF) $$ [j «$r0» HΦ]
          · iexists W64 0, slice.nil, []
            iframe
            simp only [List.map_nil]
            isplitl; · iapply ownSlice_nil
            isplitl; · iapply ownSliceCap_nil
            isplitr; · iapply BigSepL.bigSepL_nil.2; itrivial
            ipureintro
            have : sint.Z (W64 0) = 0 := by decide
            exact ⟨rfl, by omega, by omega⟩
          wp_for HI
          obtain ⟨hxl, hj0, hjn⟩ := Hinv
          by_cases Hlt : sint.Z jj < sint.Z (W64 1 + cn)
          · simp only [Hlt, decide_True_any, ↓reduceIte]
            have hj1 : sint.Z (jj + W64 1) = sint.Z jj + 1 :=
              sint_succ jj hj0 (by have := hn3.2; omega)
            have hj1n : sint.nat (jj + W64 1) = sint.nat jj + 1 := by
              have h4 : ∀ w : w64, sint.nat w = (sint.Z w).toNat := fun _ => rfl
              rw [h4, h4, hj1]; omega
            (try wp_auto)
            wp_apply wp_genRange x ks cfg (W64 (s.rev : Int)) (W64 s.crev)
              as %q ⟨%qk, %qe, Hqk, Hqe, %Hqkk, %Hqro⟩
            · isplitl
              · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
              · iunfold runnerRangeMix; iframe #
            imod ownSlice_persist $$ Hqk with #Hqk
            imod ownSlice_persist $$ Hqe with #Hqe
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %ssl1 ⟨Hssl1, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hss $Hssc $Hssl1] as %ssl' ⟨Hss, Hssc, -⟩
            (try wp_auto)
            wp_for_post
            let b : SubM := ⟨W64 2, [], [], true, [], 0, ⟨qk, qe, decide (q.end' = slice.nil), q.ro'⟩⟩
            ihave #Hnew : subIs (GF := GF) (subOp.mk (W64 2) slice.nil slice.nil [] 0 q) b $$ []
            · iunfold subIs
              isplitr; · iapply ownSlice_nil
              isplitr; · iapply ownSlice_nil
              isplitr
              · iunfold rangeIs
                iframe #
                ipureintro; exact ⟨rfl, rfl⟩
              ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
            iframe
            iexists jj + W64 1, ssl', xs ++ [(_, b)]
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
            isplitr
            · iapply BigSepL.bigSepL_snoc.2; iframe #
            ipureintro
            refine ⟨by simp only [List.length_append, List.length_singleton]; rw [hj1n, hxl], by omega,
              by omega⟩
          · simp only [Hlt, decide_False_any, decide_True_any, intoVal_eq_iff, decide_eq_self_any,
              Bool.false_eq_true, decide_false, ↓reduceIte]
            (try wp_auto)
            imod ownSlice_persist $$ Hss with #Hss
            (try wp_auto)
            imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hop with #Hop
            imodintro
            iapply HΦ
            iframe
            iexists ⟨kTxn, [], [], true, [], 0, ⟨kk, [], true, zeroValDef⟩, false, false,
              xs.map Prod.snd, 0, 0, false⟩
            iframe
            isplitl
            · iunfold opIs
              iexists _, xs.map Prod.fst
              iframe #
              isplitr; · iapply ownSlice_nil
              isplitr; · iapply ownSlice_nil
              isplitr
              · iunfold rangeIs
                iframe #
                isplitr; · iapply ownSlice_nil
                ipureintro; exact ⟨rfl, rfl⟩
              isplitr; · ipureintro; simp
              isplitr; · rw [zip_fst_snd]; iframe #
              ipureintro; simp
            ipureintro
            exact ⟨opValid_txn rfl (fun h => by cases h), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
      · (try wp_auto)
        wp_if_destruct
        · -- a grant
          (try wp_auto)
          have hnl1' : sint.Z (nl + W64 1) = sint.Z nl + 1 := sint_succ nl hnl0 hnl1
          have hg0 : 0 < sint.Z (nl + W64 1) := by omega
          have hg1 : ∀ id ∈ s.granted, sint.Z id < sint.Z (nl + W64 1) := by
            intro id hid; have := hnlg id hid; omega
          imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
          ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
          imodintro
          iapply HΦ
          iframe
          iframe #
          ipureintro
          exact ⟨opValid_grant rfl hg0 hg1, (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
        · (try wp_auto)
          wp_if_destruct
          · -- a revoke
            ihave %Hsn := ownSlice_len $$ Hsl
            wp_if_destruct
            · (try wp_auto)
              imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
              ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
              imodintro
              iapply HΦ
              iframe
              iframe #
              ipureintro
              exact ⟨opValid_plain kCommit rfl (Or.inr (Or.inl rfl)), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
            · (try wp_auto)
              have hpos : 0 < sint.Z sl.len := by
                have := Hsn.2
                have : sint.Z sl.len ≠ 0 := fun h => Hif (w64_eq_zero_of _ h)
                omega
              wp_apply wp_choose sl.len as %d %Hd
              have hdl : (sint.Z d).toNat < s.leases.length := by
                have h4 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
                have := Hsn.1; have := Hd.2.1 hpos; omega
              have hb : 0 ≤ sint.Z d ∧ sint.Z d < sint.Z sl.len := ⟨Hd.1, Hd.2.1 hpos⟩
              (try wp_auto)
              (try simp only [hb, _root_.and_self, ↓reduceIte])
              wp_apply wp_load_slice_index sl (sint.Z d) s.leases (DFrac.own 1)
                (s.leases[(sint.Z d).toNat]'hdl) Hd.1 $$ [Hsl] as Hsl
              · iframe; ipureintro; exact List.getElem?_eq_getElem hdl
              (try wp_auto)
              imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
              ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
              imodintro
              iapply HΦ
              iframe
              iframe #
              ipureintro
              exact ⟨opValid_revoke rfl (List.getElem_mem hdl), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
          · (try wp_auto)
            wp_if_destruct
            · -- a compaction
              (try wp_auto)
              wp_apply wp_choose (W64 (s.rev : Int) + W64 1) as %cr %Hcr
              (try wp_auto)
              wp_apply wp_choose (W64 2) as %cw -
              (try wp_auto)
              wp_apply wp_pick cfg.Mix'.CompactAt' wc DFrac.discard (W64 3) $$ [Hwc] as %sw2 ⟨-, %Hsw2⟩
              · iframe #
              (try wp_auto)
              wp_if_destruct
              · (try wp_auto)
                have h11 : 1 ≤ sint.Z (W64 1) := by decide
                wp_if_destruct
                · (try wp_auto)
                  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                  ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                  imodintro
                  iapply HΦ
                  iframe
                  iframe #
                  ipureintro
                  exact ⟨opValid_compact rfl h11, (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
                · (try wp_auto)
                  have hr1 : 1 ≤ sint.Z (W64 s.crev + W64 1) := by
                    have : sint.Z (W64 1) = 1 := by decide
                    omega
                  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                  ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                  imodintro
                  iapply HΦ
                  iframe
                  iframe #
                  ipureintro
                  exact ⟨opValid_compact rfl hr1, (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
              · (try wp_auto)
                wp_if_destruct
                · (try wp_auto)
                  by_cases hr0 : 1 ≤ s.rev
                  · have hr1 : 1 ≤ sint.Z (W64 (s.rev : Int)) := sint_pos_of _ hr0 (by omega)
                    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                    ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                    imodintro
                    iapply HΦ
                    iframe
                    iframe #
                    ipureintro
                    exact ⟨opValid_compact rfl hr1, (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
                  · exact absurd hrpos hr0
                · (try wp_auto)
                  have hcr1 : 1 ≤ sint.Z (W64 1 + cr) := compact_rev_ok s.rev cr hrev Hcr
                  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                  ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                  imodintro
                  iapply HΦ
                  iframe
                  iframe #
                  ipureintro
                  exact ⟨opValid_compact rfl hcr1, (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
            · (try wp_auto)
              wp_if_destruct
              · -- a commit
                (try wp_auto)
                imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                imodintro
                iapply HΦ
                iframe
                iframe #
                ipureintro
                exact ⟨opValid_plain kCommit rfl (Or.inr (Or.inl rfl)), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩
              · (try wp_auto)
                wp_if_destruct
                · -- a read
                  (try wp_auto)
                  wp_apply wp_genRange x ks cfg (W64 (s.rev : Int)) (W64 s.crev)
                    as %q ⟨%qk, %qe, Hqk, Hqe, %Hqkk, %Hqro⟩
                  · isplitl
                    · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
                    · iunfold runnerRangeMix; iframe #
                  imod ownSlice_persist $$ Hqk with #Hqk
                  imod ownSlice_persist $$ Hqe with #Hqe
                  (try wp_auto)
                  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                  imodintro
                  iapply HΦ
                  iframe
                  iexists ⟨kRead, [], [], true, [], 0, ⟨qk, qe, decide (q.end' = slice.nil), q.ro'⟩, false,
                    false, [], 0, 0, false⟩
                  iframe
                  isplitl
                  · iunfold opIs
                    iexists _, []
                    iframe #
                    isplitr; · iapply ownSlice_nil
                    isplitr; · iapply ownSlice_nil
                    isplitr
                    · iunfold rangeIs
                      iframe #
                      ipureintro; exact ⟨rfl, rfl⟩
                    isplitr; · iapply ownSlice_nil
                    isplitr; · ipureintro; rfl
                    isplitr; · rw [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; itrivial
                    ipureintro; simp
                  ipureintro
                  exact ⟨opValid_plain kRead rfl (Or.inr (Or.inr (Or.inl rfl))), (by simp [kGrant, plainOp]),
                    Int.le_refl _, by omega⟩
                · -- a lease check
                  (try wp_auto)
                  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hop
                  ihave #Hopi := opIs_plain _ _ rfl rfl rfl rfl $$ Hop
                  imodintro
                  iapply HΦ
                  iframe
                  iframe #
                  ipureintro
                  exact ⟨opValid_plain kLeases rfl (Or.inr (Or.inr (Or.inr rfl))), (by simp [kGrant, plainOp]), Int.le_refl _, by omega⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
