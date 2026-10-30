module
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.SpillReady
public import Proof.go_etcd_io.bbolt.SpillBucketAcc
public import Proof.go_etcd_io.bbolt.SpillBucketLemmas
public import Proof.go_etcd_io.bbolt.SpillBucketU
public import Spec.go_etcd_io.bbolt.Bucket__inlineable
public import Spec.go_etcd_io.bbolt.Bucket__free_x
public import Spec.go_etcd_io.bbolt.Bucket__write_x
public import Proof.go_etcd_io.bbolt.SpillBucketInl
public import Proof.go_etcd_io.bbolt.SpillNodeStep
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_w
public import Spec.go_etcd_io.bbolt.Cursor__seek_s
public import Spec.go_etcd_io.bbolt.Cursor__node_s
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.node__root
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage

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
variable [float_sem : go.FloatConvSemantics]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem spNest_nil (W : WView) (T : WTx) (B : BRec) :
    bktNested W T { B with bm := GMap.filter (fun k _ => decide (k ∉ ([] : List GoString))) B.bm } ↔
      bktNested W T B := by
  have e : GMap.filter (fun k _ => decide (k ∉ ([] : List GoString))) B.bm = B.bm := by
    apply GMap.ext; intro k
    show (B.bm !! k).filter _ = _
    cases B.bm !! k <;> simp
  rw [e]

open Classical in
/-- The loop's facts (see `spLoop`): the transaction `T1` (view `W1`, database `ρ1`, stash `F1`,
capless nodes `K1`) after the opened buckets `done` of `bl` (record `B1`, `B` at the start). -/
def spF (W : WView) (txl : Loc) (txid : w64) (T : WTx) (K : Loc → Bool) (Tr : WTx) (Kr : Loc → Bool)
    (bl : Loc) (B : BRec)
    (Bs : List Loc) (done : List GoString) (ex : List GoString) (W1 : WView) (T1 : WTx) (ρ1 : DBState)
    (F1 : GMap Nat (List w8)) (K1 : Loc → Bool) (B1 : BRec) : Prop :=
  spillG (hG := hG) W1 txl txid T1 ρ1 F1 ∧ W1 = { W with data := W1.data } ∧
  T1.bs !! bl = some B1 ∧ B1.bm = B.bm ∧ B1.bv = { B.bv with rootNode' := B1.bv.rootNode' } ∧
  B1.ib = B.ib ∧ (B1.bv.rootNode' = null → B.bv.rootNode' = null) ∧
  spillFrame T T1 (· ∈ Bs) ∧
  (∀ c C C', T.bs !! c = some C → T1.bs !! c = some C' → C'.bm = C.bm) ∧
  (∀ c C' l, c ∉ Bs → T1.bs !! c = some C' → (C'.ns !! l).isSome → K1 l = K l) ∧
  bktClean W1 (uint.nat T1.mv.pgid') bl B1 ∧ (∃ bnd, bktKeysB W1 B1 bnd) ∧
  bktNested W1 T1 { B1 with bm := GMap.filter (fun k _ => decide (k ∉ ex)) B1.bm } ∧
  leafPg0 B1 ∧ rblHt W1 B1 ∧
  (∀ l r, B1.ns !! l = some r → r.nv.unbalanced' = false ∧ r.nv.spilled' = false ∧
    K1 l = false ∧ ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
  (∀ k c d D, B.bm !! k = some c → k ∉ done → bktReach T c d → T1.bs !! d = some D →
    ∃ D0, Tr.bs !! d = some D0 ∧ bucketUX W Tr Kr d D0 ∧ spLive D0 D ∧
      ∀ l, (D0.ns !! l).isSome → K1 l = Kr l)

open Classical in
/-- The loop's invariant over the opened buckets `keys` of `bl` (record `B` at the start), the
first `i` done: the transaction (its bucket `bl`'s cache of opened buckets lent out: the map
range holds it), the results of the done ones (`kidRes`), the tokens of the others' trees. -/
def spLoop (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (K : Loc → Bool) (Tr : WTx) (Kr : Loc → Bool) (bl : Loc) (B : BRec) (Bs : List Loc) (child_ptr name_ptr : Loc)
    (keys : List GoString) (i : Nat) : IProp GF :=
  iprop(∃ (W1 : WView) (T1 : WTx) (ρ1 : DBState) (F1 : GMap Nat (List w8)) (K1 : Loc → Bool)
      (B1 : BRec) (cv : Loc) (nv : GoString),
    child_ptr ↦ cv ∗ name_ptr ↦ nv ∗
    (B.bv.buckets' ↦$ B.bm -∗ spillR I γd γ W1 txl txid T1 ρ1 F1 K1) ∗
    ([∗list] k ∈ keys.take i, kidRes γ W1 T1 B1 k) ∗
    ([∗list] k ∈ keys.drop i, ∃ c, ⌜B.bm !! k = some c⌝ ∗
      [∗list] d ∈ Bs.filter (fun d => decide (bktReach T c d)), ∃ C, ⌜T1.bs !! d = some C⌝ ∗
        bktToks γ W1 C) ∗
    bktToks γ W1 B1 ∗
    ⌜spF (hG := hG) W txl txid T K Tr Kr bl B Bs (keys.take i) [] W1 T1 ρ1 F1 K1 B1⌝)

/-- `Bucket.spill.spec`'s postcondition. -/
def spPost (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (K : Loc → Bool) (bl : Loc) (B : BRec) (Bs : List Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8))
            (K' : Loc → Bool) (B' : BRec),
          spillR I γd γ W' txl txid T' ρ' F' K' ∗
          ⌜spillG (hG := hG) W' txl txid T' ρ' F' ∧ spillFrame T T' (· ∈ Bs) ∧ W'.pages = W.pages ∧
            T'.bs !! bl = some B' ∧ B'.bm = B.bm ∧
            (∀ c C C', T.bs !! c = some C → T'.bs !! c = some C' → C'.bm = C.bm) ∧
            (∀ c C' l, c ∉ Bs → T'.bs !! c = some C' → (C'.ns !! l).isSome → K' l = K l)⌝ ∗
          ((⌜B.bv.rootNode' = null ∧ B'.bv = B.bv ∧ B'.ib = B.ib⌝ ∗ oldToks γ W B.ib) ∨
           (∃ (pid : w64) (top : Loc) (Q : GMap Nat (List w8)),
             ⌜B'.bv = { B.bv with rootNode' := top } ∧ B'.ib = { B.ib with root' := pid } ∧
               top ≠ null ∧ pid ≠ W64 0 ∧ (T'.bufs !! pid).isSome ∧ Q ⊆ spillPages W' T' ∧
               ∃ rt, B'.ns !! top = some rt ∧ rt.nv.pgid' = pid ∧ rt.nv.spilled' = true ∧
                 rt.nv.parent' = null ∧ rt.cs = []⌝ ∗
             wtreeQ γ Q (uint.nat pid) none none))) ∨
        (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid))

/-- `spPost` for the bucket with its nested buckets' values made persistent gives it for the
bucket. -/
theorem spPost_persist (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (K : Loc → Bool) (bl : Loc) (B : BRec) (Bs : List Loc) (err : GoInterface)
    (hbl : bl ∈ Bs) (hB : T.bs !! bl = some B) :
    spPost I γd γ W txl txid (setB T bl (spPB B)) K bl (spPB B) Bs err ⊢
      spPost I γd γ W txl txid T K bl B Bs err := by
  unfold spPost
  iintro (⟨%h, %W', %T', %ρ', %F', %K', %B', Hs, %Hf, Hr⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact h
    iexists W', T', ρ', F', K', B'
    iframe Hs
    have e1 : (spPB B).bv = B.bv := rfl
    have e2 : (spPB B).ib = B.ib := rfl
    isimp only [e1, e2] at Hr
    isplitr
    swap
    · iexact Hr
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hf
    refine ⟨h1, spillFrame_trans T _ T' _ _ (spillFrame_upd T bl _ _ hbl (by rw [hB]; rfl)) h2
      (fun _ h => h), h3, h4, h5, fun c C C' hC hC' => ?_, fun c C' l hc hC' hl => h7 c C' l hc hC' hl⟩
    by_cases e : c = bl
    · subst e
      rw [hB] at hC; cases hC
      exact h6 c (spPB C) C' (GMap.lookup_insert _ _ _) hC'
    · exact h6 c C C' (by show (<[bl := spPB B]> T.bs) !! c = _; rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hC) hC'
  · iright; iexact Herr

open Classical in
/-- The loop body's facts once the opened bucket `key` (at `cv0`, record `C2`) is done, before its
value `v` (if it changed) is put into `bl` (record `B2`; `v0` its entry's value before). -/
def spMidF (W : WView) (txl : Loc) (txid : w64) (T : WTx) (K : Loc → Bool) (Tr : WTx) (Kr : Loc → Bool)
    (bl : Loc) (B : BRec)
    (Bs : List Loc) (keys : List GoString) (i : Nat) (key : GoString) (cv0 : Loc) (W2 : WView)
    (T2 : WTx) (ρ2 : DBState) (F2 : GMap Nat (List w8)) (K2 : Loc → Bool) (B2 C2 : BRec)
    (v v0 : List w8) : Prop :=
  spF (hG := hG) W txl txid T K Tr Kr bl B Bs (keys.take (i + 1)) [key] W2 T2 ρ2 F2 K2 B2 ∧
  B.bm !! key = some cv0 ∧ T2.bs !! cv0 = some C2 ∧ entryIn W2 B2 key v0 ∧ 16 ≤ v0.length ∧
  (C2.bv.rootNode' = null → C2.ib = ibOf v0 ∧ bvalOK W2.pages (uint.nat T2.mv.pgid') v0 ∧
    (inBucketRoot v0 ≠ 0 → treeKeys W2.pages (inBucketRoot v0) none none)) ∧
  (C2.bv.rootNode' ≠ null → 16 ≤ v.length ∧ v.length ≤ 2 ^ 27 ∧ C2.ib.root' = (ibOf v).root' ∧
    (inBucketRoot v = 0 → inlineGood (inlinePage v)))

open Classical in
/-- The loop body's state once the opened bucket `key` is done (see `spMidF`). -/
def spMid (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (K : Loc → Bool) (Tr : WTx) (Kr : Loc → Bool) (bl : Loc) (B : BRec) (Bs : List Loc) (child_ptr name_ptr value_ptr : Loc)
    (keys : List GoString) (i : Nat) (key : GoString) (cv0 : Loc) (Φ : val → IProp GF) : IProp GF :=
  iprop(∃ (W2 : WView) (T2 : WTx) (ρ2 : DBState) (F2 : GMap Nat (List w8)) (K2 : Loc → Bool)
      (B2 C2 : BRec) (vs : GoSlice) (v v0 : List w8),
    child_ptr ↦ cv0 ∗ name_ptr ↦ key ∗ value_ptr ↦ vs ∗
    (∀ err, spPost I γd γ W txl txid T K bl B Bs err -∗ Φ #err) ∗
    spillR I γd γ W2 txl txid T2 ρ2 F2 K2 ∗
    ([∗list] k ∈ keys.take i, kidRes γ W2 T2 B2 k) ∗
    ([∗list] k ∈ keys.drop (i + 1), ∃ c, ⌜B.bm !! k = some c⌝ ∗
      [∗list] d ∈ Bs.filter (fun d => decide (bktReach T c d)), ∃ D, ⌜T2.bs !! d = some D⌝ ∗
        bktToks γ W2 D) ∗
    bktToks γ W2 B2 ∗
    (if C2.bv.rootNode' = null then oldToks γ W2 (ibOf v0)
      else iprop(vs ↦* v ∗ wbktQP γ (spillPages W2 T2) v)) ∗
    ⌜spMidF (hG := hG) W txl txid T K Tr Kr bl B Bs keys i key cv0 W2 T2 ρ2 F2 K2 B2 C2 v v0⌝)

theorem spill_rec (hinl : Bucket.inlineable.spec (GF := GF) (hG := hG))
    (hfree : Bucket.free.xspec (GF := GF) (hG := hG))
    (hwrite : Bucket.write.xspec (GF := GF) (hG := hG))
    (hcur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hseek : Cursor.seek.sspec (GF := GF) (hG := hG))
    (hnode : Cursor.node.sspec (GF := GF) (hG := hG))
    (hput : node.put.spec (GF := GF) (hG := hG))
    (hspill : node.spill.spec (GF := GF) (hG := hG))
    (hroot : node.root.spec (GF := GF) (hG := hG))
    (hPgid : Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSet : InBucket.SetRootPage.spec (GF := GF) (hG := hG))
    (n : Nat) :
    ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
      (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
      (Bs : List Loc) (dep : Loc → Nat),
    (∀ b C name c, T.bs !! b = some C → C.bm !! name = some c → dep c < dep b) → dep bl < n →
    I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → bmUnique T → T.bs !! bl = some B → Bs.Nodup →
    (∀ c, c ∈ Bs ↔ bktReach T bl c) →
    (∀ c C, c ∈ Bs → T.bs !! c = some C → bucketUX W T K c C) → W.ps < 2 ^ 20 → W.pages !! 0 = none →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
        [∗list] c ∈ Bs, ∃ C, ⌜T.bs !! c = some C⌝ ∗ bktToks γ W C }}
      (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"spill")) (Val #()))
    {{ (err : GoInterface), RET #err; spPost I γd γ W txl txid T K bl B Bs err }} := by
  induction n with
  | zero => intro I γd γ W txl txid T ρ F K bl B Bs dep _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
  intro I γd γ W txl txid T ρ F K bl B Bs dep hdep hn hFS hg hbu hB hnd hBs hU hps hp0
  rcases (hU bl B ((hBs bl).2 bktReach.root) hB).symm with ⟨hdn, hdr, hdbm, hdns⟩ | hU0
  · -- a degenerate bucket: no opened bucket, no root node
    wp_start as ⟨Hs, Htoks⟩
    icases (spillR_at I γd γ W txl txid T ρ F K bl B hB).1 $$ Hs with
      ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
    unfold bktOwnX
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_gen (fun (_ : List GoString) (_ : Nat) (m' : GMap GoString Loc) =>
      iprop(⌜m' = B.bm⌝)) $$ Hbm
    iintro %keys -
    isplitl []
    · ipureintro; rfl
    isplitr
    · iintro !> %i %key %cv0 %m' ⟨-, %Hm'⟩ %Hmm
      subst Hmm
      rw [hdbm] at Hm'
      exact absurd Hm' (by simp)
    isplitr
    · iintro !> %i %key %m' - %Hmm
      ipureintro; exact Hmm
    iintro %m' %Hmm Hbm
    subst Hmm
    wp_auto
    rw [decide_eq_true hdn]
    wp_auto
    iapply HΦ
    unfold spPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists W, T, ρ, F, K, B
    isplitl [Hdb Hv Ht Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns Hc Ho Hg HF]
    · iapply (spillR_at I γd γ W txl txid T ρ F K bl B hB).2
      unfold bktOwnX
      iframe
    isplitr
    · ipureintro
      exact ⟨hg, spillFrame_refl T _, rfl, hB, rfl, fun _ _ _ h1 h2 => by rw [h1] at h2; cases h2; rfl,
        fun _ _ _ _ _ _ => rfl⟩
    ileft
    isplitr
    · ipureintro; exact ⟨hdn, rfl, rfl⟩
    unfold oldToks
    rw [if_pos hdr]
    iempintro
  wp_start as ⟨Hs, Htoks⟩
  icases (spillR_at I γd γ W txl txid T ρ F K bl B hB).1 $$ Hs with
    ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
      iprop(⌜m' = B.bm⌝ ∗ spLoop I γd γ W txl txid T K Tr Kr bl B Bs child_ptr name_ptr keys i ∗
        (∀ err, spPost I γd γ W txl txid T K bl B Bs err -∗ Φ #err))) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hdb Hv Ht Hm Hpm Hbufs Hbv Hib Hnm Hpo Hns Hc Ho Hg HF Htoks child name HΦ]
  · obtain ⟨hc0, ⟨bnd0, hrbl⟩, hn0, hr0, hl0, hht0, hns0, -⟩ := hU0
    obtain ⟨bnd1, hkb⟩ := bktKeys_of_rbl W _ bl B bnd0 hg.1 hc0 hrbl hr0
    have hperm := bs_reach_split T dep hdep hbu bl B hB Bs hnd hBs keys Hkset Hknodup
    ihave Htoks := (BigSepL.bigSepL_perm (Φ := fun c => iprop(∃ C, ⌜T.bs !! c = some C⌝ ∗
      bktToks (GF := GF) γ W C)) hperm).1 $$ Htoks
    icases (BigSepL.bigSepL_cons (Φ := fun _ c => iprop(∃ C, ⌜T.bs !! c = some C⌝ ∗
      bktToks (GF := GF) γ W C))).1 $$ Htoks with ⟨⟨%C0, %hC0, Hbl⟩, Htoks⟩
    rw [hB] at hC0; cases hC0
    ihave Htoks := (BiEntails.of_eq (BigSepL.bigSepL_flatMap (Φ := fun c => iprop(∃ C, ⌜T.bs !! c = some C⌝ ∗
      bktToks (GF := GF) γ W C)) _)).1 $$ Htoks
    isplitr
    · ipureintro; rfl
    iframe HΦ
    unfold spLoop
    iexists W, T, ρ, F, K, B, _, _
    iframe child name
    isplitl [Hdb Hv Ht Hm Hpm Hbufs Hbv Hib Hnm Hpo Hns Hc Ho Hg HF]
    · iintro Hbm
      iapply (spillR_at I γd γ W txl txid T ρ F K bl B hB).2
      unfold bktOwnX
      iframe
    isplitl []
    · simp only [List.take_zero]
      iapply BigSepL.bigSepL_nil.2
      ipureintro; trivial
    simp only [List.drop_zero, List.take_zero]
    iframe Hbl
    isplitl [Htoks]
    · iapply (BigSepL.bigSepL_mono ?_) $$ Htoks
      intro i k hk
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((Hkset k).1 (List.mem_of_getElem? hk))
      simp only [hc]
      iintro H
      iexists c
      iframe H
      ipureintro; rfl
    ipureintro
    refine ⟨hg, by cases W; rfl, hB, rfl, rfl, rfl, id, spillFrame_refl T _,
      fun _ _ _ h1 h2 => by rw [h1] at h2; cases h2; rfl, fun _ _ _ _ _ _ => rfl, hc0, ⟨bnd1, hkb⟩, (spNest_nil W T B).2 hn0, hl0, hht0, hns0, ?_⟩
    intro k c d D hk _ hr hD
    refine ⟨by rw [hD]; rfl, hU d D ((hBs d).2 (bktReach_trans T bl c d ?_ hr)) hD⟩
    exact bktReach.child bl B k c bktReach.root hB hk
  isplitr
  · iintro !> %i %key %cv0 %m' ⟨%Hk, %Hm'⟩ ⟨%Hmm, HP, HΦ⟩ Hbm
    subst Hmm
    unfold spLoop
    icases HP with ⟨%W1, %T1, %ρ1, %F1, %K1, %B1, %cv, %nv, Hch, Hnmv, Hwand, Hkids, Hrest, Htb, %Hf⟩
    wp_auto
    obtain ⟨hg1, hW1, hB1, hbm1, hbv1, hib1, hrn1, hfr1, hbmp1, hK1, hc1, hk1, hn1, hl1, hht1, hns1,
      hrest1⟩ := Hf
    have hkeys : keys[i]? = some key := Hk
    have hcv0 : B.bm !! key = some cv0 := Hm'
    have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hkeys).1
    have hdrop : keys.drop i = key :: keys.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      rw [(List.getElem?_eq_some_iff.1 hkeys).2]
    have hknot : key ∉ keys.take i := by
      intro hm
      have hnd' : (keys.take i ++ keys.drop i).Nodup := by rw [List.take_append_drop]; exact Hknodup
      have := (List.nodup_append.1 hnd').2.2 key hm key (by rw [hdrop]; exact List.mem_cons_self)
      exact this rfl
    have hne : cv0 ≠ bl := by
      intro h; subst h; have := hdep _ B key _ hB hcv0; omega
    obtain ⟨C0, hC0⟩ : ∃ C0, T.bs !! cv0 = some C0 := by
      obtain ⟨-, -, -, hd4⟩ := hg.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact Option.isSome_iff_exists.1 ((hd4 bl B hB).2 key cv0 hcv0)
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 ((hfr1.1 cv0).1 (by rw [hC0]; rfl))
    obtain ⟨hCT, hUC⟩ := hrest1 key cv0 cv0 C hcv0 hknot bktReach.root hC
    have hKC : ∀ l r, C.ns !! l = some r → K1 l = false := by
      rcases hUC with ⟨-, -, -, -, -, -, hnsC, -⟩ | ⟨-, -, -, hns0⟩
      · exact fun l r h => (hnsC l r h).2.2.1
      · intro l r h; rw [hns0] at h; cases h
    have hps1 : W1.ps < 2 ^ 20 := by have : W1.ps = W.ps := by rw [hW1]
                                     omega
    have hpg1 : W1.pages = W.pages := by rw [hW1]
    have htxC : C.bv.tx' = txl := hg1.2.2.2.2.2.2.2.2.2.1 cv0 C hC
    have hdbl : T1.t.db' = W1.dbl := hg1.2.2.2.2.2.2.2.1
    have hrootC : C.bv.rootNode' = null ∨ (C.ns !! C.bv.rootNode').isSome := by
      rcases hUC with ⟨hcC, -⟩ | ⟨h, -⟩
      · by_cases h : C.bv.rootNode' = null
        · exact Or.inl h
        · right
          obtain ⟨-, r0, hr0, -⟩ := hcC.2.2.2.2.1 _ _ (hcC.2.2.2.1 h)
          rw [hr0]; rfl
      · exact Or.inl h
    ihave Hs := Hwand $$ Hbm
    icases (spillR_at I γd γ W1 txl txid T1 ρ1 F1 K1 cv0 C hC).1 $$ Hs with
      ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
    ihave Hbk := bktOwn_of_X W1 cv0 C K1 hKC $$ [Hb Hc]
    · iframe
    unfold TxW_rest_root
    icases Ht with ⟨Hwr, Hmg, Hdbf, Hmetaf, Hpages, Hstats, Hchf, HWF, %Htxn⟩
    ihave Hdbf : structFieldRef Tx go!"db" C.bv.tx' ↦ W1.dbl $$ [Hdbf]
    · rw [htxC, ← hdbl]; iexact Hdbf
    wp_apply hinl W1 cv0 C (DFrac.own 1) (by omega) hrootC $$ [Hbk Hdbf Hv]
      as ⟨Hbk, Hdbf, Hv⟩
    · iframe
    wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗
        spMid I γd γ W txl txid T K Tr Kr bl B Bs child_ptr name_ptr value_ptr keys i key cv0 Φ) ∨
      (∃ e : GoInterface, ⌜bv = returnVal #e ∧ e ≠ interface.nil⌝ ∗ spillErr I γd txl txid ∗
        (∀ err, spPost I γd γ W txl txid T K bl B Bs err -∗ Φ #err)))) with [-]
    · -- an inlineable child: freed and written inline
      classical
      have hinC := Hif
      rw [decide_eq_true hinC]
      · obtain ⟨hrnC, r0, hr0, hleaf0, hinsC⟩ := hinC
        have hUC' : bucketU W1 T1 K1 cv0 C := by
          rcases hUC with h | ⟨h, -⟩
          · exact h
          · exact absurd h hrnC
        obtain ⟨hcC, ⟨bndC, hrblC⟩, hnC, hrC, hlC, hhtC, hnsC, hthrC⟩ := hUC'
        have honly := spInl_ns W1 _ cv0 C hcC hrC r0 hr0 hleaf0
        obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ :=
          hcC.2.2.2.2.2.2.2.1 _ r0 hr0
        wp_auto
        -- the root's facts
        have hpgr : r0.nv.pgid' = C.ib.root' := by
          obtain ⟨-, r1, hr1, hp1⟩ := hcC.2.2.2.2.1 _ _ (hcC.2.2.2.1 hrnC)
          rw [hr0] at hr1; cases hr1; exact hp1
        have hpre : C.ib.root' ≠ W64 0 → C.bv.page' = null ∧
            resolve C C.ib.root' = some C.bv.rootNode' ∧ (∀ c l, C.nm !! c = some l → l ≠ null) ∧
            r0.nv.pgid' = C.ib.root' ∧ treeWF W1.pages (uint.nat T1.mv.pgid') (uint.nat C.ib.root') ∧
            T1.pm !! C.ib.root' = none := by
          intro h0
          have htw := n9 h0
          rw [hpgr] at htw
          obtain ⟨pg, hpg⟩ := treeWF_root _ _ _ htw
          refine ⟨hcC.2.2.2.2.2.1 h0, by unfold resolve; rw [if_neg h0]; exact hcC.2.2.2.1 hrnC,
            fun c l h => (hcC.2.2.2.2.1 c l h).1, hpgr, htw, ?_⟩
          exact spDirty_pm_none ρ1 W1 T1 _ pg hg1.2.2.2.2.2.2.2.2.2.2.1 hpg
        -- the child's resources
        isimp only [bktOwn] at Hbk
        icases Hbk with ⟨Hcbv, Hcib, Hcnm, Hcbm, Hcpo, Hcns⟩
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W1 l r)
          (show Std.get? C.ns C.bv.rootNode' = some r0 from hr0)).1 $$ Hcns with ⟨Hrn, Hcns⟩
        isimp only [nodeOwn] at Hrn
        icases Hrn with ⟨Hrnn, Hrins, Hrcap, Hrents, Hrch, Hrchc, Hrkey⟩
        -- its tokens: the root page's
        isimp only [hdrop] at Hrest
        icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨⟨%c', %hc', Hct⟩, Hrest⟩
        rw [hcv0] at hc'; cases hc'
        have hmemF : cv0 ∈ Bs.filter (fun d => decide (bktReach T cv0 d)) := by
          rw [List.mem_filter]
          refine ⟨(hBs cv0).2 (bktReach.child bl B key cv0 bktReach.root hB hcv0), ?_⟩
          simp only [decide_eq_true_eq]; exact bktReach.root
        obtain ⟨jF, hjF, hjF'⟩ := List.getElem_of_mem hmemF
        icases (BigSepL.bigSepL_lookup (Φ := fun _ d => iprop(∃ C, ⌜T1.bs !! d = some C⌝ ∗
          bktToks (GF := GF) γ W1 C)) (List.getElem?_eq_some_iff.2 ⟨hjF, hjF'⟩)) $$ Hct
          with ⟨%C', %hC', HtC⟩
        rw [hC] at hC'; cases hC'
        isimp only [bktToks, if_neg hrnC] at HtC
        icases (BigSepM.bigSepM_lookup (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W1 C r)
          (show Std.get? C.ns C.bv.rootNode' = some r0 from hr0)) $$ HtC with HtC
        isimp only [nodeToks] at HtC
        icases HtC with ⟨Htok, -⟩
        ihave Htok : (if C.ib.root' = W64 0 then emp else (uint.nat C.ib.root' ↪[γ] () : IProp GF)) $$ [Htok]
        · rw [hpgr]
          by_cases h0 : C.ib.root' = W64 0
          · simp only [if_pos h0]; iexact Htok
          · rw [if_neg h0, if_neg h0]
            obtain ⟨pg, hpg⟩ := treeWF_root _ _ _ (hpre h0).2.2.2.2.1
            iapply (pgToks_single γ W1.pages _ pg hpg).1; iexact Htok
        ihave Hdbf : structFieldRef Tx go!"db" txl ↦ W1.dbl $$ [Hdbf]
        · rw [← htxC]; iexact Hdbf
        have hmtx : T1.mv.txid' = txid := hg1.2.2.2.2.2.1
        icases (persistent_entails_left (dbWR_facts I γd W1 txl txid ρ1)) $$ Hdb with ⟨Hdb, %hdbF⟩
        wp_apply hfree I γd γ W1 (uint.nat T1.mv.pgid') txl txid ρ1 cv0 C T1.t.pages' T1.pm T1.t.meta' T1.mv
          (DFrac.own 1) F1 r0.nv hFS hg1.1 htxC hmtx hg1.2.2.2.2.2.2.2.2.2.2.2.2.1 hrnC n1 hleaf0 n8 hpre
          hg1.1.1 $$ [Hcbv Hcib Hcnm Hrnn Hv Hpages Hpm Hdbf Hmetaf Hm Hdb HF Htok]
          as ⟨%ρ2, %F2, Hcbv, Hcib, Hcnm, Hrnn, Hv, Hpages, Hpm, Hdbf, Hmetaf, Hm, Hdb, HF, %Hfr⟩
        · iframe
        -- `value = child.write()`
        icases persistent_entails_left (spWOwns_len W1 r0.ins r0.ws) $$ Hrents with ⟨Hrents, %hlx⟩
        have hlenf : ∀ (i : Nat) (it : Inode) (w : WEntry), r0.ins[i]? = some it → r0.ws[i]? = some w →
            uint.nat it.key'.len = w.key.length ∧ uint.nat it.value'.len = w.value.length := by
          intro i it w h1 h2
          have h := hlx i it w h1 h2
          have hw := n5 w (List.mem_of_getElem? h2)
          exact ⟨h.1 hw.1, h.2 hw.2⟩
        isimp only [wView] at Hv
        icases Hv with ⟨Hdata, #Hps, #Hlg, Hfl, #Hdl, %Hlgv, Hpv⟩
        icases nodeBorrowD W1 hg1.1.1 r0.ws r0.ins W1.q n5 $$ [Hpv Hrents] with ⟨Hio, Hioback⟩
        · iframe
        have hlenE : r0.ins.length = (borrowEs r0.ws W1.q).length := by rw [spBorrowEs_length]; exact n2
        icases spInodesOwn_dataF r0.ins _ hlenE $$ Hio with ⟨Hdat, Hdatback⟩
        obtain ⟨hbk, hbvv⟩ := spBorrowEs_kv r0.ws W1.q
        obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ :=
          spInl_write r0.ins r0.ws W1.ps hps1 n2 hlenf (hnsC _ r0 hr0).2.2.2 n4 hinsC
        simp only [← hbk, ← hbvv] at w2 w3 w4 w5 w6 w7
        wp_apply hwrite cv0 C.bv (DFrac.own 1) ({ C.ib with root' := W64 0 } : InBucket) (DFrac.own 1)
          ({ r0.nv with pgid' := W64 0 } : node) (DFrac.own 1) r0.ins (DFrac.own 1)
          ((borrowEs r0.ws W1.q).map NodeEntry.key) ((borrowEs r0.ws W1.q).map NodeEntry.value) _ _
          w1 w2 w3 w4 w5 w6 (fun h => by simp [hleaf0] at h)
          $$ [Hcbv Hcib Hrnn Hrins Hdat] as %val ⟨Hcbv, Hcib, Hrnn, Hrins, Hdat, Hval, Hvcap⟩
        · iframe
        -- the node, the view, the bucket back
        ihave Hio := Hdatback $$ Hdat
        icases Hioback $$ Hio with ⟨Hpv, Hrents⟩
        ihave Hv : wView W1 $$ [Hdata Hfl Hpv]
        · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
        have hC2 : (setB T1 cv0 (spInlC C r0)).bs !! cv0 =
            some (spInlC C r0) :=
          GMap.lookup_insert _ _ _
        ihave Hcb : bktOwn (GF := GF) W1 cv0 (spInlC C r0)
          $$ [Hcbv Hcib Hcnm Hcbm Hcpo Hcns Hrnn Hrins Hrcap Hrents Hrch Hrchc Hrkey]
        · rw [show bktOwn (GF := GF) W1 cv0 (spInlC C r0) = iprop(cv0 ↦ C.bv ∗
              C.bv.InBucket' ↦ ({ C.ib with root' := W64 0 } : InBucket) ∗ C.bv.nodes' ↦$ C.nm ∗
              C.bv.buckets' ↦$ C.bm ∗ pageOwn W1 C ∗ [∗map] l ↦ r ∈ (spInlC C r0).ns, nodeOwn W1 l r)
            from rfl]
          unfold spInlC
          iframe Hcbv Hcib Hcnm Hcbm Hcpo
          iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)
            (Φ := fun l r => nodeOwn (GF := GF) W1 l r)).2
          iframe Hcns
          unfold nodeOwn
          iframe
        icases (bktOwn_to_X W1 cv0 _ K1) $$ Hcb with ⟨Hcb, Hcc⟩
        ihave Hs : spillR I γd γ W1 txl txid (setB T1 cv0 (spInlC C r0)) ρ2 F2 K1
          $$ [Hdb Hv Hwr Hmg Hdbf Hmetaf Hpages Hstats Hchf HWF Hm Hpm Hbufs Hcb Hcc Ho Hg HF]
        · iapply (spillR_at I γd γ W1 txl txid _ ρ2 F2 K1 cv0 _ hC2).2
          rw [show (setB T1 cv0 (spInlC C r0)).bs =
            <[cv0 := (spInlC C r0)]> T1.bs from rfl,
            othersOwn_insert, bufsOwn_eq (setB T1 cv0 (spInlC C r0)) T1 rfl rfl,
            ghostOK_eq γ W1 (setB T1 cv0 (spInlC C r0)) T1 rfl]
          unfold TxW_rest_root
          simp only [setB]
          rw [hdbl]
          iframe
          ipureintro; exact Htxn
        -- the state after
        have hT2 : ∀ d, d ≠ cv0 → (setB T1 cv0 (spInlC C r0)).bs !! d = T1.bs !! d := by
          intro d hd
          show (<[cv0 := spInlC C r0]> T1.bs) !! d = _
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]
        have hcvBs : cv0 ∈ Bs := (hBs cv0).2 (bktReach.child bl B key cv0 bktReach.root hB hcv0)
        obtain ⟨Cn, v0, hCn, hev0, h16v0, -⟩ := (spNest_nil W1 T1 B1).1 hn1 key cv0 (by rw [hbm1]; exact hcv0)
        have hρ2 : (ρ2 = ρ1 ∧ F2 = F1) ∨ (∃ id k, ρ2 = { ρ1 with fl := ρ1.fl.freePages txid id k } ∧
            freedOK W1 ρ2.fl txid F2) := by
          obtain ⟨hf1, ⟨fl, hfl⟩, hz, hnz⟩ := Hfr
          by_cases h0 : C.ib.root' = W64 0
          · obtain ⟨a, b, -⟩ := hz h0; exact Or.inl ⟨a, b⟩
          · obtain ⟨pg, -, -, hpfl⟩ := hnz h0
            right
            refine ⟨C.ib.root', 1 + pageOverflow pg, ?_, hf1⟩
            rw [hfl] at hpfl ⊢
            simp only at hpfl
            rw [hpfl]
        have hg2 := spillG_inl W1 txl txid T1 ρ1 ρ2 F1 F2 cv0 C r0 hg1 hC hr0 hdbF.1 hρ2
        have hwbf := writtenBucket_facts ({ C.ib with root' := W64 0 } : InBucket)
          ((borrowEs r0.ws W1.q).map NodeEntry.key) ((borrowEs r0.ws W1.q).map NodeEntry.value) r0.ins
        have hlf' : ({ r0.nv with pgid' := W64 0 } : node).isLeaf' = true := hleaf0
        isimp only [hlf', hleaf0] at Hval
        have hwop : writeOK ((borrowEs r0.ws W1.q).map NodeEntry.key)
            ((borrowEs r0.ws W1.q).map NodeEntry.value) r0.ins := ⟨w1, w2, w3, w4, w5⟩
        have hgood := spInl_good ((borrowEs r0.ws W1.q).map NodeEntry.key)
          ((borrowEs r0.ws W1.q).map NodeEntry.value) r0.ins hwop
          (fun a b hab hb => by
            rw [hbk]
            have := n3 a b hab (by rw [← n2]; exact hb)
            simp only [wKey] at this
            simpa [List.getD_eq_getElem?_getD] using this)
          (fun a ha => by
            have hget : r0.ins[a]? = some (r0.ins.getD a (zero_val Inode)) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl
            exact spFlags_even _ (hinsC a _ hget).1)
        obtain ⟨hv16, hvroot, hvpage⟩ := hwbf
        rw [← hvpage] at hgood
        have hvlen : (writtenBucket ({ C.ib with root' := W64 0 } : InBucket) true
            ((borrowEs r0.ws W1.q).map NodeEntry.key) ((borrowEs r0.ws W1.q).map NodeEntry.value)
            r0.ins).length ≤ 2 ^ 27 := by
          obtain ⟨-, hl2, -⟩ := writtenPage_facts (Page.mk (W64 0) (W16 0) (W16 0) (W32 0)) true
            ((borrowEs r0.ws W1.q).map NodeEntry.key) ((borrowEs r0.ws W1.q).map NodeEntry.value) r0.ins [] hwop
          have e := congrArg List.length hvpage
          unfold inlinePage at e
          rw [List.length_drop] at e
          simp only [List.length_nil] at hl2
          omega
        ileft
        isplitr
        · ipureintro; rfl
        unfold spMid
        iexists W1, setB T1 cv0 (spInlC C r0), ρ2, F2, K1, B1, spInlC C r0, val,
          writtenBucket ({ C.ib with root' := W64 0 } : InBucket) true
            ((borrowEs r0.ws W1.q).map NodeEntry.key) ((borrowEs r0.ws W1.q).map NodeEntry.value) r0.ins,
          v0
        iframe Hch Hnmv value HΦ Hs Htb
        isplitl [Hkids]
        · rw [kidsRes_bufs γ W1 T1 (setB T1 cv0 (spInlC C r0)) B1 _ rfl rfl]; iexact Hkids
        isplitl [Hrest]
        · iapply (BigSepL.bigSepL_mono ?_) $$ Hrest
          intro j k hk
          have hkd : k ∈ keys.drop (i + 1) := List.mem_of_getElem? hk
          have hkne : k ≠ key := by
            intro e; subst e
            have hnd' : (keys.take (i + 1) ++ keys.drop (i + 1)).Nodup := by
              rw [List.take_append_drop]; exact Hknodup
            have hin : k ∈ keys.take (i + 1) := by
              rw [List.take_add_one, List.mem_append]; right; rw [hkeys]; simp
            exact (List.nodup_append.1 hnd').2.2 k hin k hkd rfl
          iintro ⟨%c, %hc, H⟩
          iexists c
          isplitr
          · ipureintro; exact hc
          iapply (BigSepL.bigSepL_mono ?_) $$ H
          intro j' d hd
          have hdm := List.mem_of_getElem? hd
          rw [List.mem_filter] at hdm
          have hreach : bktReach T c d := by simpa using hdm.2
          have hdne := spSib_ne T dep hdep hbu bl B hB key k cv0 c d hcv0 hc hkne hreach
          iintro ⟨%D, %hD, HD⟩
          iexists D
          iframe HD
          ipureintro; rw [hT2 d hdne]; exact hD
        have hrnC2 : (spInlC C r0).bv.rootNode' ≠ null := hrnC
        rw [if_neg hrnC2]
        isplitl [Hval]
        · iframe Hval
          unfold wbktQP
          isplitr
          · ipureintro; exact hv16
          rw [if_pos (by rw [hvroot]; rfl)]
          ipureintro; exact hgood
        ipureintro
        have hbmp2 : ∀ c Cx Cy, T.bs !! c = some Cx → (setB T1 cv0 (spInlC C r0)).bs !! c = some Cy →
            Cy.bm = Cx.bm := by
          intro c Cx Cy h1 h2
          by_cases e : c = cv0
          · subst e
            rw [hC2] at h2; cases h2
            obtain ⟨Cz, hz⟩ := Option.isSome_iff_exists.1 ((hfr1.1 c).1 (by rw [h1]; rfl))
            rw [hC] at hz; cases hz
            exact hbmp1 c Cx C h1 hC
          · rw [hT2 c e] at h2; exact hbmp1 c Cx Cy h1 h2
        have hn2 : bktNested W1 (setB T1 cv0 (spInlC C r0))
            { B1 with bm := GMap.filter (fun k _ => decide (k ∉ [key])) B1.bm } := by
          intro k c hk
          have hk' : (B1.bm !! k).filter (fun _ => decide (k ∉ [key])) = some c := hk
          cases e : B1.bm !! k with
          | none => rw [e] at hk'; cases hk'
          | some c' =>
            rw [e] at hk'
            simp only [Option.filter_some] at hk'
            split at hk'
            · rename_i hdk
              cases hk'
              have hkne : k ≠ key := by simpa using hdk
              obtain ⟨Cc, vc, hCc, rest⟩ := (spNest_nil W1 T1 B1).1 hn1 k c (by rw [e])
              have hcne : c ≠ cv0 := by
                intro hc0; subst hc0
                exact hkne (hbu bl B k bl B key c hB (by rw [← hbm1, e]) hB hcv0).2
              exact ⟨Cc, vc, by rw [hT2 c hcne]; exact hCc, rest⟩
            · cases hk'
        refine ⟨⟨hg2, hW1, by rw [hT2 bl (fun h => hne h.symm)]; exact hB1, hbm1, hbv1, hib1, hrn1,
          spillFrame_trans T T1 _ _ _ hfr1 (spillFrame_upd T1 cv0 _ _ hcvBs (by rw [hC]; rfl))
            (fun _ h => h), hbmp2, fun c Cy l hc h2 hl => ?_, hc1, hk1, hn2, hl1, hht1, hns1, ?_⟩,
          hcv0, hC2, hev0, h16v0, fun h => absurd h hrnC2, fun _ => ⟨hv16, hvlen, ?_, by
            intro _; exact hgood⟩⟩
        · have e : c ≠ cv0 := fun h => hc (h ▸ hcvBs)
          rw [hT2 c e] at h2
          exact hK1 c Cy l hc h2 hl
        · intro k c d D hk hkn hr hD
          have hkn' : k ∉ keys.take i := fun h => hkn (by
            rw [List.take_add_one, List.mem_append]; left; exact h)
          have hkne : k ≠ key := by
            intro e; subst e; exact hkn (by rw [List.take_add_one, List.mem_append]; right; rw [hkeys]; simp)
          have hdne := spSib_ne T dep hdep hbu bl B hB key k cv0 c d hcv0 hk hkne hr
          rw [hT2 d hdne] at hD
          obtain ⟨h1, h2⟩ := hrest1 k c d D hk hkn' hr hD
          refine ⟨h1, bucketUX_T W1 T1 _ K1 d D h2 (Nat.le_refl _) ?_⟩
          intro k' c' C' hk' hC'
          obtain ⟨D0, hD0⟩ := Option.isSome_iff_exists.1 h1
          have hbmD := hbmp1 d D0 D hD0 hD
          have hr' : bktReach T c c' := bktReach.child d D0 k' c' hr hD0 (by rw [← hbmD]; exact hk')
          rw [hT2 c' (spSib_ne T dep hdep hbu bl B hB key k cv0 c c' hcv0 hk hkne hr')]
          exact hC'
        · show W64 0 = (ibOf _).root'
          unfold ibOf; simp only; rw [hvroot]; rfl
    · classical
      rw [decide_eq_false Hif]
      sorry
    · sorry
  isplitr
  · iintro !> %i %key %m' ⟨%Hk, %Hm'⟩ ⟨%Hmm, -⟩
    subst Hmm
    have := (Hkset key).1 (List.mem_of_getElem? Hk)
    rw [Hm'] at this; cases this
  iintro %m' ⟨%Hmm, HP, HΦ⟩ Hbm
  subst Hmm
  unfold spPost
  unfold spLoop
  -- the end of the loop: every opened bucket done
  icases HP with ⟨%W1, %T1, %ρ1, %F1, %K1, %B1, %cv, %nv, Hch, Hnmv, Hwand, Hkids, -, Htb, %Hf⟩
  ihave Hs := Hwand $$ Hbm
  obtain ⟨hg1, hW1, hB1, hbm1, hbv1, hib1, hrn1, hfr1, hbmp1, hK1, hc1, hk1, hn1, hl1, hht1, hns1, -⟩ := Hf
  icases (spillR_at I γd γ W1 txl txid T1 ρ1 F1 K1 bl B1 hB1).1 $$ Hs with
    ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  wp_auto
  by_cases hrn : B1.bv.rootNode' = null
  · rw [decide_eq_true hrn]
    wp_auto
    have hBn : B.bv.rootNode' = null := hrn1 hrn
    have hbv : B1.bv = B.bv := by
      rw [hbv1, hrn]; rw [← hBn]
    have hpg : W1.pages = W.pages := by rw [hW1]
    obtain ⟨bnd1, hkb⟩ := hk1
    have hr1 : bktRanked B1 := bktRanked_of_keys W1 _ bl B1 bnd1 hc1 hkb
    rw [List.take_length]
    ihave Hkm := (keys_bigSepM (fun k => kidRes γ W1 T1 B1 k) B1.bm keys
      (fun k => by rw [hbm1]; exact Hkset k) Hknodup).1 $$ Hkids
    ihave Hold := old_of_kids γ W1 T1 _ bl B1 bnd1 hg1.1 hc1 hkb hr1 hrn $$ [Htb Hkm]
    · iframe
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists W1, T1, ρ1, F1, K1, B1
    isplitl [Hdb Hv Ht Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns Hc Ho Hg HF]
    · iapply (spillR_at I γd γ W1 txl txid T1 ρ1 F1 K1 bl B1 hB1).2
      unfold bktOwnX
      iframe
    isplitr
    · ipureintro
      exact ⟨hg1, hfr1, hpg, hB1, hbm1, hbmp1, hK1⟩
    ileft
    isplitr
    · ipureintro; exact ⟨hBn, hbv, hib1⟩
    have e : oldToks (GF := GF) γ W1 B1.ib = oldToks γ W B.ib := by
      unfold oldToks; rw [hib1, hpg]
    rw [← e]
    iexact Hold
  · rw [decide_eq_false hrn]
    wp_auto
    obtain ⟨bnd1, hkb⟩ := hk1
    have hr1 : bktRanked B1 := bktRanked_of_keys W1 _ bl B1 bnd1 hc1 hkb
    rw [List.take_length]
    ihave Hkm := (keys_bigSepM (fun k => kidRes γ W1 T1 B1 k) B1.bm keys
      (fun k => by rw [hbm1]; exact Hkset k) Hknodup).1 $$ Hkids
    icases ready_of_shape γ W1 T1 (uint.nat T1.mv.pgid') bl B1 K1 bnd1 hg1.1 hc1 hkb hr1 ((spNest_nil W1 T1 B1).1 hn1) hl1 hrn
      (fun l r h => ⟨(hns1 l r h).2.2.1, (hns1 l r h).1⟩) hg1.2.2.2.1
      (by unfold uint.nat; word) hht1 $$ [Htb Hkm]
      with ⟨%bnd, %kd, %ht, %S, ⟨%hbr, %hsub, %hS, %hnh⟩, Hrt⟩
    · iframe
    ihave Hs := (spillR_at I γd γ W1 txl txid T1 ρ1 F1 K1 bl B1 hB1).2 $$
      [Hdb Hv Ht Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns Hc Ho Hg HF]
    · unfold bktOwnX; iframe
    have hne : ∀ l r, B1.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length := by
      intro l r h hp
      obtain ⟨-, -, -, h4, h5, -⟩ := hkb.2.2 l r h
      cases hl : r.nv.isLeaf'
      · have := (h4 hl).1; omega
      · exact h5 hl (hns1 l r h).1 hp
    have hthr : uint.Z (splitThr (W64 (W1.ps : Int)) B1.bv.FillPercent') ≤ W1.ps := by
      rw [hbv1, hW1]; exact hU0.2.2.2.2.2.2.2
    have hps1 : W1.ps < 2 ^ 20 := by rw [hW1]; exact hps
    have hcp := clean_pgids W1 _ bl B1 hc1 (by rw [hW1]; exact hp0)
    have hsz : ∀ l r, B1.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28 :=
      fun l r h => (hns1 l r h).2.2.2
    have htok : treeOK bl B1 := spTreeOK_of_clean W1 _ bl B1 hc1 hr1 hrn hkb.2.1
    wp_apply hspill I γd γ W1 txl txid T1 ρ1 F1 K1 bl B1 bnd kd ht S hFS hg1 hB1 hrn hkb.2.1 hbr hsub
      hnh hS hthr hps1 hsz hne hcp.1 hcp.2.1 hcp.2.2 htok $$ [Hs Hrt] as %err Hpost
    · iframe
    icases Hpost with (⟨%Herr, %W2, %T2, %ρ2, %F2, %K2, %B2, %p, %top, %pid, %Q, Hs2, HQ, %Hf2⟩ |
      ⟨%Herr, Herr⟩)
    · subst Herr
      wp_auto
      obtain ⟨hg2, hfr2, hpg2, hB2, hbv2, hib2, hnm2, hbm2, hup, hpnd, hdom, hQs, hQsub, hbuf, hK2,
        rt, hrt, hrtp, hrts, hrtpar, hrtcs⟩ := Hf2
      icases (spillR_at I γd γ W2 txl txid T2 ρ2 F2 K2 bl B2 hB2).1 $$ Hs2 with
        ⟨Hdb, Hv, Ht, Hm, Hpm, Hbufs, Hb, Hc, Ho, Hg, HF⟩
      unfold bktOwnX
      icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
      obtain ⟨hpp, rest, hrest, hlast⟩ := chain_parentPath B2.ns _ p top hup
      icases chain_accX W2 B2.ns _ p top hup hpnd B2.ns (fun _ _ => rfl) $$ Hns with ⟨Hch, Hchback⟩
      rw [hrest] at hpp
      rw [hrest]
      rw [hbv2]
      wp_auto
      wp_apply hroot _ _ rest (DFrac.own 1) hpp $$ [Hch] as Hch
      · iframe
      rw [hlast]
      ihave Hns := Hchback $$ Hch
      icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun x r => nodeOwnX (GF := GF) W2 x r)
        (show Std.get? B2.ns top = some rt from hrt)).1 $$ Hns with ⟨Htop, Hnsback⟩
      unfold nodeOwnX
      icases Htop with ⟨Htn, Htop⟩
      have htx2 : B2.bv.tx' = txl := hg2.2.2.2.2.2.2.2.2.2.1 bl B2 hB2
      unfold TxW_rest_root
      icases Ht with ⟨Hwr, Hmg, Hdbf, Hmetaf, Hpages, Hstats, Hch, HWF, %Htxn⟩
      simp only [hbv2] at htx2
      rw [htx2]
      wp_auto
      ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
      · iPkgInit
      wp_apply hPgid T2.t.meta' T2.mv (DFrac.own 1) $$ [Hm] as Hm
      · iframe
      have hlt : uint.Z pid < uint.Z T2.mv.pgid' := by
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbuf
        obtain ⟨-, h2, -⟩ := hg2.2.2.2.2.2.2.2.2.2.2.1
        obtain ⟨-, -, -, h4, -⟩ := h2 pid b hb
        have h5 : uint.nat pid + 1 ≤ uint.nat T2.mv.pgid' := by unfold dspan at h4; omega
        unfold uint.nat at h5; word
      rw [hrtp, decide_eq_false (by omega)]
      wp_auto
      wp_method_call
      try wp_auto
      wp_apply hSet $$ [Hib] as Hib
      · iframe
      try wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ Htn with ⟨Htn, %Htopn⟩
      ihave Hns := Hnsback $$ [Htn Htop]
      · iframe
      -- the bucket with its new root
      have hB' : ({ T2 with bs := <[bl := setRootB B2 top pid]> T2.bs } : WTx).bs !! bl =
          some (setRootB B2 top pid) := GMap.lookup_insert _ _ _
      have hpid2 : 2 ≤ uint.nat pid := by
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbuf
        exact (hg2.2.2.2.2.2.2.2.2.2.2.1.2.1 pid b hb).2.2.1
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists W2, { T2 with bs := <[bl := setRootB B2 top pid]> T2.bs }, ρ2, F2, K2,
        setRootB B2 top pid
      isplitl [Hdb Hv Hwr Hmg Hdbf Hmetaf Hpages Hstats Hch HWF Hm Hpm Hbufs Hbv Hib Hnm Hbm Hpo Hns Hc Ho Hg HF]
      · iapply (spillR_at I γd γ W2 txl txid _ ρ2 F2 K2 bl _ hB').2
        rw [othersOwn_insert,
          bufsOwn_eq ({ T2 with bs := <[bl := setRootB B2 top pid]> T2.bs } : WTx) T2 rfl rfl,
          ghostOK_eq γ W2 ({ T2 with bs := <[bl := setRootB B2 top pid]> T2.bs } : WTx) T2 rfl,
          capsB_ns B2 (setRootB B2 top pid) K2 rfl]
        unfold bktOwnX TxW_rest_root
        rw [pageOwn_eq W2 B2 (setRootB B2 top pid) rfl rfl rfl]
        unfold setRootB
        simp only [hbv2]
        rw [htx2]
        isimp only [hrtp] at Hib
        iframe
        ipureintro; exact Htxn
      have hblBs : bl ∈ Bs := (hBs bl).2 bktReach.root
      have hT2b : (T2.bs !! bl).isSome := by rw [hB2]; rfl
      have hfr12 : spillFrame T1 T2 (· ∈ Bs) := spillFrame_mono T1 T2 _ _ hfr2 (fun c h => h ▸ hblBs)
      have hfr' : spillFrame T { T2 with bs := <[bl := setRootB B2 top pid]> T2.bs } (· ∈ Bs) :=
        spillFrame_trans _ _ _ _ _ hfr1
          (spillFrame_trans _ _ _ _ _ hfr12 (spillFrame_upd T2 bl _ _ hblBs hT2b) (fun _ h => h))
          (fun _ h => h)
      isplitr
      · ipureintro
        refine ⟨spillG_setRoot W2 txl txid T2 ρ2 F2 bl B2 top rt pid hg2 hB2 hrt hrtpar hrtcs hrtp p
            (by rw [hbv2]; exact hup) (by rw [hbv2]; exact hrn), hfr', by rw [hpg2, hW1], hB', ?_, ?_, ?_⟩
        · show B2.bm = B.bm; rw [hbm2, hbm1]
        · intro c C C' hC hC'
          by_cases e : bl = c
          · subst e
            rw [hB] at hC; cases hC
            rw [hB'] at hC'; cases hC'
            show B2.bm = B.bm; rw [hbm2, hbm1]
          · change (<[bl := setRootB B2 top pid]> T2.bs) !! c = some C' at hC'
            rw [GMap.lookup_insert_ne _ _ e] at hC'
            obtain ⟨C1, hC1⟩ := Option.isSome_iff_exists.1 ((hfr1.1 c).1 (by rw [hC]; rfl))
            have hn : ¬ (c = bl) := fun h => e h.symm
            rw [((derefStarX_bm _ _ (hfr2.2.2.2.2.2 c C1 C' hn hC1 hC').1)).1, hbmp1 c C C1 hC hC1]
        · intro c C' l hc hC' hl
          have e : bl ≠ c := fun h => hc (h ▸ hblBs)
          change (<[bl := setRootB B2 top pid]> T2.bs) !! c = some C' at hC'
          rw [GMap.lookup_insert_ne _ _ e] at hC'
          obtain ⟨C1, hC1⟩ := Option.isSome_iff_exists.1 ((hfr2.1 c).2 (by rw [hC']; rfl))
          have hn : ¬ (c = bl) := fun h => e h.symm
          obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hl
          obtain ⟨r1, hr1⟩ := derefStarX_ns C1 C' (hfr2.2.2.2.2.2 c C1 C' hn hC1 hC').1 l r' hr'
          rw [hK2 c C' l (fun h => e h.symm) hC' hl, hK1 c C1 l hc hC1 (by rw [hr1]; rfl)]
      iright
      iexists pid, top, Q
      iframe HQ
      ipureintro
      refine ⟨?_, ?_, Htopn, ?_, hbuf, hQsub, rt, hrt, hrtp, hrts, hrtpar, hrtcs⟩
      · show ({ B2.bv with rootNode' := top } : Bucket) = _
        rw [hbv2, hbv1]
      · show ({ B2.ib with root' := pid } : InBucket) = _
        rw [hib2, hib1]
      · intro h; rw [h] at hpid2; simp at hpid2
    · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Herr
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      iapply HΦ
      iright
      iframe
      ipureintro; exact Herr

theorem Bucket.spill.wp_proof (hinl : Bucket.inlineable.spec (GF := GF) (hG := hG))
    (hfree : Bucket.free.xspec (GF := GF) (hG := hG))
    (hwrite : Bucket.write.xspec (GF := GF) (hG := hG))
    (hcur : Bucket.Cursor.wspec (GF := GF) (hG := hG))
    (hseek : Cursor.seek.sspec (GF := GF) (hG := hG))
    (hnode : Cursor.node.sspec (GF := GF) (hG := hG))
    (hput : node.put.spec (GF := GF) (hG := hG))
    (hspill : node.spill.spec (GF := GF) (hG := hG))
    (hroot : node.root.spec (GF := GF) (hG := hG))
    (hPgid : Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSet : InBucket.SetRootPage.spec (GF := GF) (hG := hG)) :
    Bucket.spill.spec (GF := GF) (hG := hG) := by
  intro I γd γ W txl txid T ρ F K bl B Bs hFS hg hbu hB hnd hBs hU hps hp0
  obtain ⟨dep, hdep⟩ := hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact spill_rec hinl hfree hwrite hcur hseek hnode hput hspill hroot hPgid hSet (dep bl + 1) I γd γ W txl txid T ρ F K bl B Bs dep hdep (Nat.lt_succ_self _)
    hFS hg hbu hB hnd hBs (fun c C h1 h2 => Or.inl (hU c C h1 h2)) hps hp0

end proof

end bbolt
end EtcdGrove
end Perennial
