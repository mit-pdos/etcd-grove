/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__rebalance.lean` (U8b, `notes/bbolt-proof-plan.md`).

`b.rebalance()` rebalances `b`'s cached nodes (a map iteration: each node still cached when its
key is reached, `node.rebalance.spec'`), then recurses into its cached buckets (`b.buckets`). Its
internal spec (`Bucket.rebalance.spec'`) is over `rebalance`'s invariant `rblX`: after it, every
bucket reached from `b` through the bucket caches has no unbalanced node, and a bucket without one
keeps none (`node.rebalance` never marks a node unbalanced). At `Commit` (`tx.root.rebalance()`)
every bucket is reached from the root (`liveReach`), and `rebalOK_of_rbl` gives the post.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__rebalance
public import Proof.go_etcd_io.bbolt.node__rebalance
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The buckets reached from `b` through the bucket caches (`b` included). -/
inductive bReach (X : WX) : Loc → Loc → Prop
  | self (b : Loc) : bReach X b b
  | child (b c d : Loc) (B : BRec) (n : GoString) :
      X.t.bs !! b = some B → B.bm !! n = some c → bReach X c d → bReach X b d

/-- No node of bucket `c` is unbalanced. -/
def balanced (X : WX) (c : Loc) : Prop :=
  ∀ B, X.t.bs !! c = some B → ∀ l r, B.ns !! l = some r → r.nv.unbalanced' = false

/-- **`b.rebalance()`** of a bucket `bl` of the transaction, under `rebalance`'s invariant: every
bucket reached from it balanced after, a balanced bucket kept so, the steps' frees. -/
def Bucket.rebalance.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl dbl : Loc),
  rblX X w.fl dbl none → (X.t.bs !! bl).isSome →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' dbl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧
        (∀ c, bReach X bl c → balanced X' c) ∧ (∀ c, balanced X c → balanced X' c)⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-! ### The loops' invariants (pure) -/

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- The bucket reach is kept by the steps (the buckets' locations and caches kept). -/
theorem bReach_rel (X X' : WX) (fl fl' : FLPg) (t : w64) (h : rblRel X fl X' fl' t) (a d : Loc)
    (hr : bReach X a d) : bReach X' a d := by
  induction hr with
  | self b => exact .self b
  | child b c d B n hb hn _ ih =>
    obtain ⟨B', hB', -, -, hbm⟩ := rblRel_at X X' fl fl' t h b B hb
    exact .child b c d B' n hB' (by rw [hbm]; exact hn) ih

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- `n.rebalance()` keeps every balanced bucket balanced. -/
theorem balanced_step (X1 X2 : WX) (fl1 fl2 : FLPg) (t : w64) (bl n : Loc)
    (hR : rblRel X1 fl1 X2 fl2 t) (hS : rblStepX X1 X2 bl n) (c : Loc) (h : balanced X1 c) :
    balanced X2 c := by
  intro B2 hB2 l r2 hl
  by_cases hc : c = bl
  · subst hc
    obtain ⟨B1, hB1⟩ : ∃ B1, X1.t.bs !! c = some B1 := by
      have := hR.2.2.2.2.2.2.2.2.1 c; rw [hB2] at this
      exact Option.isSome_iff_exists.1 this.symm
    rcases Bool.eq_false_or_eq_true r2.nv.unbalanced' with hu | hu
    · obtain ⟨-, r1, hr1, hu1, -⟩ := (hS.2 B1 B2 hB1 hB2).2.2.2 l r2 hl hu
      rw [h B1 hB1 l r1 hr1] at hu1; cases hu1
    · exact hu
  · rw [hS.1 c hc] at hB2
    exact h B2 hB2 l r2 hl

/-- The node loop's invariant (pure part): before the `i`-th key, the bucket's record `B1` caches
the map `m'`, the unbalanced nodes' page ids are keys not yet reached. -/
def nInv (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List w64) (i : Nat)
    (m' : GMap w64 Loc) (X1 : WX) (fl1 : FLPg) (B1 : BRec) : Prop :=
  X1.t.bs !! bl = some B1 ∧ B1.nm = m' ∧ B1.bv = B.bv ∧ rblX X1 fl1 dbl none ∧
  rblRel X w.fl X1 fl1 X.t.mv.txid' ∧
  (∀ l r, B1.ns !! l = some r → r.nv.unbalanced' = true → r.nv.pgid' ∈ keys.drop i) ∧
  (∀ c, balanced X c → balanced X1 c)

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- A cached node of the bucket is cached under its page id. -/
theorem nm_of_ns (X1 : WX) (fl1 : FLPg) (dbl bl : Loc) (B1 : BRec) (hI : rblX X1 fl1 dbl none)
    (hb : X1.t.bs !! bl = some B1) (l : Loc) (r : NRec) (hl : B1.ns !! l = some r) :
    B1.nm !! r.nv.pgid' = some l :=
  ((hI.2.1 bl B1 hb).1.1.2.2.2.2.2.2.2.1 l r hl).2.2.2.2.2.2.2.1

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- A cached page id's node is a node of the bucket. -/
theorem ns_of_nm (X1 : WX) (fl1 : FLPg) (dbl bl : Loc) (B1 : BRec) (hI : rblX X1 fl1 dbl none)
    (hb : X1.t.bs !! bl = some B1) (k : w64) (v : Loc) (hv : B1.nm !! k = some v) :
    ∃ r, B1.ns !! v = some r :=
  let ⟨r, hr, _⟩ := ((hI.2.1 bl B1 hb).1.1.2.2.2.2.1 k v hv).2
  ⟨r, hr⟩

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem nInv_init (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List w64)
    (hI : rblX X w.fl dbl none) (hb : X.t.bs !! bl = some B)
    (hk : ∀ k, k ∈ keys ↔ (B.nm !! k).isSome) : nInv X w dbl bl B keys 0 B.nm X w.fl B := by
  refine ⟨hb, rfl, rfl, hI, rblRel_refl _ _ _, fun l r hl _ => ?_, fun _ h => h⟩
  rw [List.drop_zero]
  exact (hk _).2 (by rw [nm_of_ns X w.fl dbl bl B hI hb l r hl]; rfl)

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem nInv_step (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List w64) (i : Nat)
    (m' : GMap w64 Loc) (X1 : WX) (fl1 : FLPg) (B1 : BRec) (key : w64) (v : Loc)
    (h : nInv X w dbl bl B keys i m' X1 fl1 B1) (hk : keys[i]? = some key) (hv : m' !! key = some v)
    (X2 : WX) (fl2 : FLPg) (hI2 : rblX X2 fl2 bl none) (hR2 : rblRel X1 fl1 X2 fl2 X1.t.mv.txid')
    (hS2 : rblStepX X1 X2 bl v) :
    ∃ B2, nInv X w dbl bl B keys (i + 1) B2.nm X2 fl2 B2 := by
  obtain ⟨hb1, hnm1, hbv1, hI1, hR1, hpk1, hbal1⟩ := h
  obtain ⟨B2, hb2, hbv2, -, -⟩ := rblRel_at X1 X2 fl1 fl2 _ hR2 bl B1 hb1
  have hmv : X1.t.mv = X.t.mv := hR1.2.2.2.2.2.1
  rw [hmv] at hR2
  refine ⟨B2, hb2, rfl, hbv2.trans hbv1, rblX_none X2 fl2 bl dbl hI2,
    rblRel_trans _ _ _ _ _ _ _ hR1 hR2, fun l r2 hl hu => ?_,
    fun c hc => balanced_step X1 X2 fl1 fl2 _ bl v hR2 hS2 c (hbal1 c hc)⟩
  obtain ⟨hlv, r1, hr1, hu1, hpg⟩ := (hS2.2 B1 B2 hb1 hb2).2.2.2 l r2 hl hu
  rw [hpg]
  apply mem_drop_succ keys i key _ hk _ (hpk1 l r1 hr1 hu1)
  intro he; apply hlv
  have h7 := nm_of_ns X1 fl1 dbl bl B1 hI1 hb1 l r1 hr1
  rw [he, hnm1, hv] at h7; exact (Option.some.inj h7).symm

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem nInv_skip (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List w64) (i : Nat)
    (m' : GMap w64 Loc) (X1 : WX) (fl1 : FLPg) (B1 : BRec) (key : w64)
    (h : nInv X w dbl bl B keys i m' X1 fl1 B1) (hk : keys[i]? = some key) (hv : m' !! key = none) :
    nInv X w dbl bl B keys (i + 1) m' X1 fl1 B1 := by
  obtain ⟨hb1, hnm1, hbv1, hI1, hR1, hpk1, hbal1⟩ := h
  refine ⟨hb1, hnm1, hbv1, hI1, hR1, fun l r hl hu => ?_, hbal1⟩
  apply mem_drop_succ keys i key _ hk _ (hpk1 l r hl hu)
  intro he
  have h7 := nm_of_ns X1 fl1 dbl bl B1 hI1 hb1 l r hl
  rw [he, hnm1, hv] at h7; cases h7

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem nInv_end (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List w64)
    (m' : GMap w64 Loc) (X1 : WX) (fl1 : FLPg) (B1 : BRec)
    (h : nInv X w dbl bl B keys keys.length m' X1 fl1 B1) : balanced X1 bl := by
  intro B' hB' l r hl
  rw [h.1] at hB'; cases hB'
  rcases Bool.eq_false_or_eq_true r.nv.unbalanced' with hu | hu
  · have := h.2.2.2.2.2.1 l r hl hu; rw [List.drop_length] at this; cases this
  · exact hu

/-- The bucket loop's invariant (pure part): the subtrees of the children before the `i`-th key
balanced. -/
def bInv (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List GoString) (i : Nat)
    (X1 : WX) (fl1 : FLPg) : Prop :=
  rblX X1 fl1 dbl none ∧ rblRel X w.fl X1 fl1 X.t.mv.txid' ∧ balanced X1 bl ∧
  (∀ c, balanced X c → balanced X1 c) ∧
  ∀ k name c, k < i → keys[k]? = some name → B.bm !! name = some c → ∀ d, bReach X c d →
    balanced X1 d

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem bInv_step (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List GoString) (i : Nat)
    (X1 : WX) (fl1 : FLPg) (key : GoString) (c : Loc) (h : bInv X w dbl bl B keys i X1 fl1)
    (hk : keys[i]? = some key) (hc : B.bm !! key = some c) (X2 : WX) (fl2 : FLPg)
    (hI2 : rblX X2 fl2 dbl none) (hR2 : rblRel X1 fl1 X2 fl2 X1.t.mv.txid')
    (hr2 : ∀ d, bReach X1 c d → balanced X2 d) (hb2 : ∀ c, balanced X1 c → balanced X2 c) :
    bInv X w dbl bl B keys (i + 1) X2 fl2 := by
  obtain ⟨hI1, hR1, hbl1, hbal1, hdone1⟩ := h
  have hmv : X1.t.mv = X.t.mv := hR1.2.2.2.2.2.1
  rw [hmv] at hR2
  refine ⟨hI2, rblRel_trans _ _ _ _ _ _ _ hR1 hR2, hb2 bl hbl1, fun c hc => hb2 c (hbal1 c hc),
    fun k name c' hk' hkn hc' d hd => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | hk'
  · exact hb2 d (hdone1 k name c' hk' hkn hc' d hd)
  · subst hk'; rw [hk] at hkn; cases hkn; rw [hc] at hc'; cases hc'
    exact hr2 d (bReach_rel X X1 w.fl fl1 _ hR1 c d hd)

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem bInv_end (X : WX) (w : WDb) (dbl bl : Loc) (B : BRec) (keys : List GoString)
    (X1 : WX) (fl1 : FLPg) (hb : X.t.bs !! bl = some B)
    (hk : ∀ k, k ∈ keys ↔ (B.bm !! k).isSome) (h : bInv X w dbl bl B keys keys.length X1 fl1) :
    ∀ d, bReach X bl d → balanced X1 d := by
  intro d hd
  cases hd with
  | self => exact h.2.2.1
  | child _ c _ B' n hB' hn hcd =>
    rw [hb] at hB'; cases hB'
    obtain ⟨k, hk', hkn⟩ := List.getElem_of_mem ((hk n).2 (by rw [hn]; rfl))
    exact h.2.2.2.2 k n c hk' (by rw [List.getElem?_eq_getElem hk', hkn]) hn d hcd

/-! ### The recursion -/

/-- `Bucket.rebalance.spec'`, in the logic (for the Löb induction). -/
def rebalBw : IProp GF :=
  iprop(∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl dbl : Loc),
    ⌜rblX X w.fl dbl none ∧ (X.t.bs !! bl).isSome⌝ → ∀ Φ,
    wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w -∗
    ▷ (∀ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' dbl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧
        (∀ c, bReach X bl c → balanced X' c) ∧ (∀ c, balanced X c → balanced X' c)⌝ -∗ Φ #()) -∗
    WP (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance")) (Val #())) {{ Φ }})

theorem rebalB_loeb (hn : node.rebalance.spec' (GF := GF) (hG := hG)) : ⊢ rebalBw (GF := GF) := by
  iloeb as IH
  unfold rebalBw
  iintro %K %tx %r %m %X %w %bl %dbl %Hpre %Φ ⟨Hw, Hdb⟩ HΦ
  obtain ⟨hI, hbS⟩ := Hpre
  obtain ⟨B, hb⟩ := Option.isSome_iff_exists.1 hbS
  icases wtxW_nodes_fld K tx r m X bl B hb $$ Hw with ⟨Hf, Hw⟩
  wp_method_call
  wp_call
  try wp_auto
  ihave Hw := Hw $$ Hf
  icases wtxW_nm_acc K tx r m X bl B hb _ _ rfl rfl $$ Hw with ⟨Hnm, Hw⟩
  try wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List w64) (i : Nat) (m' : GMap w64 Loc) =>
      iprop(∃ (X1 : WX) (fl1 : FLPg) (B1 : BRec) (nv : Loc),
        ⌜nInv X w dbl bl B keys i m' X1 fl1 B1⌝ ∗ (B.bv.nodes' ↦$ m' -∗ wtxW K tx r m X1) ∗
        wdbW K tx X.v (w.withFl fl1) ∗ n_ptr ↦ nv)) $$ Hnm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hw Hdb n]
  · iexists X, w.fl, B, _
    iframe
    ipureintro
    exact nInv_init X w dbl bl B keys hI hb Hkset
  isplitr
  · iintro !> %i %key %v %m' ⟨%Hk, %Hm'⟩ ⟨%X1, %fl1, %B1, %nv, %HP, Hw, Hdb, n⟩ Hnm
    ihave Hw := Hw $$ Hnm
    try wp_auto
    have hI1 : rblX X1 fl1 dbl none := HP.2.2.2.1
    have hX1v : X1.v = X.v := HP.2.2.2.2.1.1
    obtain ⟨rv, hrv⟩ := ns_of_nm X1 fl1 dbl bl B1 hI1 HP.1 key v (by rw [HP.2.1]; exact Hm')
    wp_apply hn K tx r m X1 (w.withFl fl1) bl B1 v rv none (rblX_none X1 fl1 dbl bl hI1) HP.1 hrv
      (Or.inl rfl) $$ [Hw Hdb] as ⟨%X2, %fl2, Hw, Hdb, %Hpost⟩
    · rw [hX1v]; iframe
    rw [hX1v]
    obtain ⟨hI2, hR2, hS2⟩ := Hpost
    obtain ⟨B2, hInv2⟩ := nInv_step X w dbl bl B keys i m' X1 fl1 B1 key v HP Hk Hm' X2 fl2 hI2 hR2 hS2
    icases wtxW_nm_acc K tx r m X2 bl B2 hInv2.1 B.bv.nodes' B2.nm (by rw [hInv2.2.2.1]) rfl $$ Hw
      with ⟨Hnm, Hw⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists B2.nm
    iframe Hnm
    iexists X2, fl2, B2, v
    iframe
    ipureintro; exact hInv2
  isplitr
  · iintro !> %i %key %m' ⟨%Hk, %Hm'⟩ ⟨%X1, %fl1, %B1, %nv, %HP, Hw, Hdb, n⟩
    iexists X1, fl1, B1, nv
    iframe
    ipureintro
    exact nInv_skip X w dbl bl B keys i m' X1 fl1 B1 key HP Hk Hm'
  iintro %m' ⟨%X1, %fl1, %B1, %nv, %HP, Hw, Hdb, n⟩ Hnm
  ihave Hw := Hw $$ Hnm
  have hbal1 := nInv_end X w dbl bl B keys m' X1 fl1 B1 HP
  have hbv1 : B1.bv = B.bv := HP.2.2.1
  have hbm1 : B1.bm = B.bm := by
    obtain ⟨B1', hb1', -, -, hbm⟩ := rblRel_at X X1 w.fl fl1 _ HP.2.2.2.2.1 bl B hb
    rw [HP.1] at hb1'; cases hb1'; exact hbm
  icases wtxW_buckets_fld K tx r m X1 bl B1 HP.1 $$ Hw with ⟨Hf, Hw⟩
  try wp_auto
  ihave Hw := Hw $$ Hf
  rw [hbv1]
  icases wtxW_bm_acc K tx r m X1 bl B1 HP.1 B.bv.buckets' B.bm (by rw [hbv1]) hbm1 $$ Hw
    with ⟨Hbm, Hw⟩
  try wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
      iprop(⌜m' = B.bm⌝ ∗ ∃ (X2 : WX) (fl2 : FLPg) (cv : Loc),
        ⌜bInv X w dbl bl B keys i X2 fl2⌝ ∗ (B.bv.buckets' ↦$ B.bm -∗ wtxW K tx r m X2) ∗
        wdbW K tx X.v (w.withFl fl2) ∗ child_ptr ↦ cv)) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hw Hdb child]
  · isplitr
    · ipureintro; rfl
    iexists X1, fl1, _
    iframe
    ipureintro
    exact ⟨HP.2.2.2.1, HP.2.2.2.2.1, hbal1, HP.2.2.2.2.2.2, fun k _ _ hk => absurd hk (Nat.not_lt_zero _)⟩
  isplitr
  · iintro !> %i %key %c %m' ⟨%Hk, %Hc⟩ ⟨%Hmm, %X2, %fl2, %cv, %HQ, Hw, Hdb, child⟩ Hbm
    subst Hmm
    ihave Hw := Hw $$ Hbm
    try wp_auto
    have hX2v : X2.v = X.v := HQ.2.1.1
    have hcS : (X2.t.bs !! c).isSome := by
      obtain ⟨B2, hb2, -, -, hbm2⟩ := rblRel_at X X2 w.fl fl2 _ HQ.2.1 bl B hb
      exact (HQ.1.2.1 bl B2 hb2).2.1 key c (by rw [hbm2]; exact Hc)
    have hpre : rblX X2 (w.withFl fl2).fl dbl none ∧ (X2.t.bs !! c).isSome := ⟨HQ.1, hcS⟩
    wp_apply IH $$ %K %tx %r %m %X2 %(w.withFl fl2) %c %dbl %hpre [Hw Hdb]
      as %X3 %fl3 ⟨Hw, Hdb, %Hpost⟩
    · rw [hX2v]; iframe
    rw [hX2v]
    obtain ⟨hI3, hR3, hr3, hb3⟩ := Hpost
    have hInv3 := bInv_step X w dbl bl B keys i X2 fl2 key c HQ Hk Hc X3 fl3 hI3 hR3 hr3 hb3
    obtain ⟨B3, hB3, hbv3, -, hbm3⟩ := rblRel_at X X3 w.fl fl3 _ hInv3.2.1 bl B hb
    icases wtxW_bm_acc K tx r m X3 bl B3 hB3 B.bv.buckets' B.bm (by rw [hbv3]) hbm3 $$ Hw
      with ⟨Hbm, Hw⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists B.bm
    iframe Hbm
    isplitr
    · ipureintro; rfl
    iexists X3, fl3, c
    iframe
    ipureintro; exact hInv3
  isplitr
  · iintro !> %i %key %m' ⟨%Hk, %Hm'⟩ ⟨%Hmm, -⟩
    subst Hmm
    have := (Hkset key).1 (List.mem_of_getElem? Hk)
    rw [Hm'] at this; cases this
  iintro %m' ⟨%Hmm, %X2, %fl2, %cv, %HQ, Hw, Hdb, child⟩ Hbm
  subst Hmm
  ihave Hw := Hw $$ Hbm
  try wp_auto
  iapply HΦ $$ %X2 %fl2
  iframe
  ipureintro
  exact ⟨HQ.1, HQ.2.1, bInv_end X w dbl bl B keys X2 fl2 hb Hkset HQ, HQ.2.2.2.1⟩

/-- **`b.rebalance()`**: the two map iterations (order-independent invariants: the unbalanced
nodes' page ids are keys not yet reached; the buckets done balanced) and the recursion (Löb). -/
theorem Bucket.rebalance.wp_proof' (hn : node.rebalance.spec' (GF := GF) (hG := hG)) :
    Bucket.rebalance.spec' (GF := GF) (hG := hG) := by
  intro K tx r m X w bl dbl hI hbS
  have H := rebalB_loeb hn
  unfold rebalBw at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %K %tx %r %m %X %w %bl %dbl %(⟨hI, hbS⟩) HP
  inext
  iintro %X' %fl' ⟨Hw, Hdb, %Hpost⟩
  iapply HΦ
  iexists X', fl'
  iframe
  ipureintro; exact Hpost

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- A bucket the root reaches (`bktReach`) is reached from the root (`bReach`). -/
theorem bReach_snoc (X : WX) (a b c : Loc) (B : BRec) (n : GoString) (h : bReach X a b)
    (hb : X.t.bs !! b = some B) (hn : B.bm !! n = some c) : bReach X a c := by
  induction h with
  | self b => exact .child b c c B n hb hn (.self c)
  | child b c' d B' n' hb' hn' _ ih => exact .child b c' c B' n' hb' hn' (ih hb)

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem bReach_of_bktReach (X : WX) (c : Loc) (h : bktReach X c) : bReach X X.rl c := by
  induction h with
  | root => exact .self _
  | child bl c B n hb hn _ ih => exact bReach_snoc X X.rl bl c B n ih hb hn

/-- The writer's heap facts (its root bucket the transaction's `root` field, its objects
disjoint). -/
theorem wtxW_rl (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜heapOK (GF := GF) tx X⌝ ∗ wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hrest⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  isplitr
  · ipureintro; exact Hok
  · iframe
    ipureintro; exact Hr

/-- The writer's view is the committed state's. -/
theorem wdbW_view (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜v = View.ofC v.base w.C⌝ ∗ wdbW K tx v w := by
  unfold wdbW
  iintro ⟨H, %Hp⟩
  isplitr
  · ipureintro; exact Hp.2.2
  · iframe; ipureintro; exact Hp

/-- **`tx.root.rebalance()`** (the frozen spec), from the internal one: at `Commit` the invariant
holds (`rblX_init`), every bucket is live, hence reached from the root, hence balanced after;
`rebalOK_of_rbl` gives the post. -/
theorem Bucket.rebalance.wp_proof
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hNum : node.numChildren.spec (GF := GF) (hG := hG))
    (hIdx : node.childIndex.spec (GF := GF) (hG := hG))
    (hNext : node.nextSibling.spec (GF := GF) (hG := hG))
    (hPrev : node.prevSibling.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hRm : node.removeChild.spec (GF := GF) (hG := hG))
    (hFree : node.free.spec (GF := GF) (hG := hG))
    (hNode : Bucket.node.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hPg : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG)) :
    Bucket.rebalance.spec (GF := GF) (hG := hG) := by
  have hb := Bucket.rebalance.wp_proof' (node.rebalance.wp_proof hSize hNum hIdx hNext hPrev hDel
    hRm hFree hNode hInc hAssert hPg)
  intro K tx r m X w hok _hld hlr hflU
  -- batch 20: `flViewU` carries `covU`, the page extents and the pending entries' alignment;
  -- `wOK` the live nodes.
  obtain ⟨hfl, hcov, hext, hlen⟩ := hflU
  have hns : nsLive X := wOK_nsLive X hok
  have hrh : ∀ bl, (X.t.bs !! bl).isSome → bl = X.rl ∨ (X.handles !! bl).isSome := by sorry
  wp_start_folded as ⟨Hw, Hdb⟩
  icases wtxW_rl K tx r m X $$ Hw with ⟨%Hhok, Hw⟩
  have Hrl := Hhok.1
  have hI := rblX_init X w.fl X.rl hok hlr hfl hcov hns hext hlen Hhok.2.1 hrh
  icases wdbW_view K tx X.v w $$ Hdb with ⟨%Hv, Hdb⟩
  have e : (tx.[Tx, go!"root"] : Loc) = X.rl := by rw [Hrl]; rfl
  rw [e]
  have hroot : (X.t.bs !! X.rl).isSome := hok.1.2.2.2.2.1
  wp_apply (hb K tx r m X w X.rl X.rl hI hroot) $$ [Hw Hdb] as ⟨%X', %fl', Hw, Hdb, %Hpost⟩
  · iframe
  obtain ⟨hI', hR, hreach, -⟩ := Hpost
  have hbal : ∀ bl B l r, X'.t.bs !! bl = some B → B.ns !! l = some r →
      r.nv.unbalanced' = false := by
    intro bl B l r hb' hr
    have hs := hR.2.2.2.2.2.2.2.2.1 bl
    rw [hb'] at hs
    obtain ⟨B0, hb0⟩ := Option.isSome_iff_exists.1 hs.symm
    have hlive : bl ∈ X.live := hok.2.2.2.2.2.1.2.2.1 bl B0 hb0
    exact hreach bl (bReach_of_bktReach X bl (hlr.1 bl B0 hb0 hlive)) B hb' l r hr
  obtain ⟨h1, h2, h3⟩ := rebalOK_of_rbl X X' w.fl fl' X.rl X.t.mv.txid' hI' hR hbal
  have htxw : X.t.mv.txid' = w.wtxid := by
    have h0 := hok.1.2.2.2.1
    have hvt : X.v.txid = w.C.txid := by rw [Hv]; rfl
    apply BitVec.eq_of_toNat_eq
    unfold WDb.wtxid
    rw [toNat_W64_of_lt _ (by have := X.t.mv.txid'.isLt; omega)]
    omega
  rw [htxw] at h1
  obtain ⟨-, -, -, -, -, -, -, -, -, hcU, hE, hA, -, -⟩ := hI'
  iapply HΦ
  iexists X', fl'
  iframe
  ipureintro
  exact ⟨h1, h2, h3, hcU, hE, hA⟩

end proof

end bbolt
end EtcdGrove
end Perennial
