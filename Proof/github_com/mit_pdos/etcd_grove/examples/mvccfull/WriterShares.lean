/-
mvccfull's writer: the shares of an incarnation, gathered at a restart and lent again (Probe).
Lean-first (no Rocq counterpart).

An incarnation's retirement token, its `kv` field and its reader tokens are lent to the epoch's
readers (`rdLent`, `Readers.lean`) and streams (`epochTok`, `Streams.lean`); the writer keeps the rest
(`qw`, `nw`). `lentOk` says they add up to the whole. `shares_join` gathers them (a restart, before
`inc_retire` and `shut`); `shares_split` lends them again at the reopened incarnation, with the same
shares (so the other member's, and `writerOwn`'s `q`, `qs`, are unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- One step keeps or grows the history by one revision. -/
theorem opStep_len (ks : List GoString) (s : MSt) (o : OpM) :
    s.hs.length ≤ (opStep ks s o).hs.length ∧ (opStep ks s o).hs.length ≤ s.hs.length + 1 := by
  simp only [opStep, histAfter]
  split <;> simp

theorem foldl_opStep_len (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.hs.length ≤ (l.foldl (opStep ks) s).hs.length ∧
      (l.foldl (opStep ks) s).hs.length ≤ s.hs.length + l.length := by
  induction l with
  | nil => intro s; simp
  | cons o l ih =>
    intro s
    have h1 := opStep_len ks s o
    have h2 := ih (opStep ks s o)
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- **The model's history has at least the two empty revisions, and one more per operation at
most.** (Pure; proved.) -/
theorem runM_hs_len (ks : List GoString) (ops : List OpM) (n : Nat) :
    2 ≤ (runM ks ops n).hs.length ∧ (runM ks ops n).hs.length ≤ n + 2 := by
  have h := foldl_opStep_len ks (ops.take n) mStart
  have h0 : mStart.hs.length = 2 := rfl
  have ht : (ops.take n).length ≤ n := by simp only [List.length_take]; exact Nat.min_le_left _ _
  unfold runM
  omega

theorem foldl_opStep_prefix (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.hs <+: (l.foldl (opStep ks) s).hs := by
  induction l with
  | nil => intro s; exact List.prefix_refl _
  | cons o l ih =>
    intro s
    refine List.IsPrefix.trans ?_ (ih (opStep ks s o))
    simp only [opStep, histAfter]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

/-- **The model's history only grows along the log** (a prefix). (Pure; proved.) -/
theorem runM_hs_prefix (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    histAt ks ops n <+: histAt ks ops n' := by
  have ht : ops.take n' = ops.take n ++ (ops.take n').drop n := by
    have := List.take_append_drop n (ops.take n')
    rw [List.take_take, Nat.min_eq_left hn] at this
    exact this.symm
  unfold histAt runM
  rw [ht, List.foldl_append]
  exact foldl_opStep_prefix ks _ _

/-- The revision only grows along the log. (Pure; proved.) -/
theorem revAfter_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    revAfter ks ops n ≤ revAfter ks ops n' := by
  have := (runM_hs_prefix ks ops n n' hn).length_le
  unfold revAfter MSt.rev
  unfold histAt at this
  omega

theorem foldl_opStep_crev (ks : List GoString) (l : List OpM) : ∀ s : MSt,
    s.crev ≤ (l.foldl (opStep ks) s).crev := by
  induction l with
  | nil => intro s; exact Int.le_refl _
  | cons o l ih =>
    intro s
    refine Int.le_trans ?_ (ih (opStep ks s o))
    simp only [opStep]
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; omega
    · exact Int.le_refl _

/-- The compaction revision only grows along the log. (Pure; proved.) -/
theorem cmpAfter_mono (ks : List GoString) (ops : List OpM) (n n' : Nat) (hn : n ≤ n') :
    cmpAfter ks ops n ≤ cmpAfter ks ops n' := by
  have ht : ops.take n' = ops.take n ++ (ops.take n').drop n := by
    have := List.take_append_drop n (ops.take n')
    rw [List.take_take, Nat.min_eq_left hn] at this
    exact this.symm
  unfold cmpAfter runM
  rw [ht, List.foldl_append]
  exact foldl_opStep_crev ks _ _

/-- A member's store revision is the model's. (Pure; proved.) -/
theorem σOf_rev (ks : List GoString) (ops : List OpM) (n : Nat) :
    (σOf ks ops n).rev = revAfter ks ops n := by
  simp [σOf, MvccState.rev, logOfHist, revAfter, MSt.rev, histAt]

theorem σOf_notified (ks : List GoString) (ops : List OpM) (n : Nat) :
    (σOf ks ops n).notifiedLog = (σOf ks ops n).log := rfl

end model

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- An incarnation's handles are persistent (`isMvcc`'s, `persistent.law`). -/
theorem isInc_persistent (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) :
    ∀ ks γh i mp m ι kv, Persistent (isInc (GF := GF) ks γh i mp m ι kv) := by
  haveI := hpers.1
  intro ks γh i mp m ι kv
  unfold isInc; infer_instance

/-- The member's incarnation's handles, from the writer's part. -/
theorem memW_isInc (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw : Qp) (nw k : Nat) :
    memW (GF := GF) ks γh ops i mp m f v qw nw k ⊢
      memW ks γh ops i mp m f v qw nw k ∗ isInc ks γh i mp m v.ι v.kv := by
  haveI := isInc_persistent hpers
  unfold memW memCore incW
  dsimp only
  iintro ⟨Ho, Hh, Hid, Hhk, Hhok, Hp, Hb, Hl, Hk, Hr, Hc, Hls, Hpo, ⟨#Hi, Hrest⟩, Hrest2⟩
  iframe
  isplit <;> iexact Hi

/-- The writer's pieces of an incarnation at the share `a`: the retirement token's, the `kv`
field's, `c` reader tokens. -/
def incShare (mp : Loc) (ι : IncNames) (kv : GoInterface) (a : Qp) (c : Nat) : IProp GF :=
  iprop(ghostVar ι.ret a () ∗ mF go!"kv" mp ↦{DFrac.own a} kv ∗ mvccReaders ι.kv c)

/-- Two shares make one. -/
theorem incShare_add (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (mp : Loc) (ι : IncNames)
    (kv : GoInterface) (a b : Qp) (c d : Nat) :
    incShare (GF := GF) mp ι kv (a + b) (c + d) ⊣⊢ incShare mp ι kv a c ∗ incShare mp ι kv b d := by
  unfold incShare
  constructor
  · iintro ⟨G, K, R⟩
    icases ((ghostVar_fractional ι.ret ()).fractional a b).1 $$ G with ⟨G1, G2⟩
    icases (typedPointsto_frac_add (mF go!"kv" mp) kv a b).1 $$ K with ⟨K1, K2⟩
    icases (hsplit ι.kv c d).1 $$ R with ⟨R1, R2⟩
    iframe
  · iintro ⟨⟨G1, K1, R1⟩, ⟨G2, K2, R2⟩⟩
    isplitl [G1 G2]
    · iapply ((ghostVar_fractional ι.ret ()).fractional a b).2; iframe
    isplitl [K1 K2]
    · iapply (typedPointsto_frac_add (mF go!"kv" mp) kv a b).2; iframe
    · iapply (hsplit ι.kv c d).2; iframe

/-- One stream's token is a share `qs` with two reader tokens, and a history slot. -/
theorem epochTok_eq (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (E : Ep) (qs : Qp) :
    epochTok (GF := GF) E qs ⊣⊢
      histRd E.h E.γh ∗ isInc E.ks E.γh E.i E.mp E.m E.ι E.kv ∗ incShare E.mp E.ι E.kv qs 2 := by
  haveI := isInc_persistent hpers
  have h2 : incShare (GF := GF) E.mp E.ι E.kv qs 2 ⊣⊢
      incShare E.mp E.ι E.kv qs.half 1 ∗ incShare E.mp E.ι E.kv qs.half 1 := by
    have := incShare_add (GF := GF) hsplit E.mp E.ι E.kv qs.half qs.half 1 1
    rwa [Qp.half_add_half] at this
  unfold epochTok epRd incRd
  constructor
  · iintro ⟨Hh, ⟨#Hi, R1, G1, K1⟩, ⟨-, R2, G2, K2⟩⟩
    iframe Hh
    isplitr
    · iexact Hi
    iapply h2.2
    unfold incShare
    iframe
  · iintro ⟨Hh, #Hi, Hs⟩
    icases h2.1 $$ Hs with ⟨S1, S2⟩
    unfold incShare
    icases S1 with ⟨G1, K1, R1⟩
    icases S2 with ⟨G2, K2, R2⟩
    iframe
    isplit <;> iexact Hi

/-- **The streams' tokens joined** into a share (an accumulator `a`, `c`). -/
theorem epochToks_join (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (E : Ep) (qs : Qp)
    (ns : Nat) : ∀ (a : Qp) (c : Nat),
    incShare (GF := GF) E.mp E.ι E.kv a c ∗ ([∗list] _x ∈ List.replicate ns (), epochTok E qs) ⊢
      ∃ a' : Qp, ⌜a'.val = a.val + (ns : Rat) * qs.val⌝ ∗ incShare E.mp E.ι E.kv a' (c + 2 * ns) ∗
        histRds E.h E.γh ns := by
  induction ns with
  | zero =>
    intro a c
    iintro ⟨Hs, -⟩
    iexists a
    iframe Hs
    isplitr
    · ipureintro; grind
    · iunfold histRds; simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    intro a c
    iintro ⟨Hs, Ht⟩
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨T, Ht⟩
    icases (epochTok_eq hpers hsplit E qs).1 $$ T with ⟨Hh, -, S⟩
    ihave Hs : incShare E.mp E.ι E.kv (a + qs) (c + 2) $$ [Hs S]
    · iapply (incShare_add hsplit E.mp E.ι E.kv a qs c 2).2; iframe
    icases ih (a + qs) (c + 2) $$ [Hs Ht] with ⟨%a', %Ha', Hs, Hhs⟩
    · iframe
    iexists a'
    rw [show c + 2 * (n + 1) = c + 2 + 2 * n by omega]
    iframe Hs
    isplitr
    · ipureintro; rw [Ha', Qp.val_add]; push_cast; grind
    · iunfold histRds; iunfold histRds at Hhs
      rw [List.replicate_succ]
      iapply BigSepL.bigSepL_cons.2
      iframe

/-- **The streams' tokens lent** from a share (the reverse of `epochToks_join`). -/
theorem epochToks_split (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (E : Ep) (qs : Qp)
    (ns : Nat) : ∀ (a b : Qp) (c : Nat), a.val = b.val + (ns : Rat) * qs.val →
    isInc (GF := GF) E.ks E.γh E.i E.mp E.m E.ι E.kv ∗ incShare E.mp E.ι E.kv a (c + 2 * ns) ∗
        histRds E.h E.γh ns ⊢
      incShare E.mp E.ι E.kv b c ∗ ([∗list] _x ∈ List.replicate ns (), epochTok E qs) := by
  haveI := isInc_persistent hpers
  induction ns with
  | zero =>
    intro a b c hab
    have : a = b := Subtype.ext (by grind)
    subst this
    iintro ⟨-, Hs, -⟩
    iframe Hs
    simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    intro a b c hab
    let a1 : Qp := ⟨b.val + (n : Rat) * qs.val, by
      have := b.2
      have h1 : (0 : Rat) ≤ (n : Rat) * qs.val :=
        Rat.mul_nonneg (by exact_mod_cast Nat.zero_le n) (Rat.le_of_lt qs.2)
      grind⟩
    have ha : a = a1 + qs := Subtype.ext (by
      simp only [Qp.val_add, a1]; rw [hab]; push_cast; grind)
    iintro ⟨#Hi, Hs, Hhs⟩
    rw [ha, show c + 2 * (n + 1) = (c + 2 * n) + 2 by omega]
    icases (incShare_add hsplit E.mp E.ι E.kv a1 qs (c + 2 * n) 2).1 $$ Hs with ⟨Hs, S⟩
    iunfold histRds at Hhs
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hhs with ⟨Hh, Hhs⟩
    icases ih a1 b c rfl $$ [Hs Hhs] with ⟨Hs, Ht⟩
    · iframe Hi Hs; iunfold histRds; iexact Hhs
    iframe Hs
    iapply BigSepL.bigSepL_cons.2
    iframe Ht
    iapply (epochTok_eq hpers hsplit E qs).2
    iframe
    iexact Hi

/-- The readers' lent part is a share. -/
theorem rdLent_eq (mp : Loc) (ι : IncNames) (kv : GoInterface) (n : Nat) (q : Qp) :
    rdLent (GF := GF) mp ι kv n q ⊣⊢ incShare mp ι kv q n := by
  unfold rdLent incShare
  constructor
  · iintro ⟨R, G, K⟩; iframe
  · iintro ⟨G, K, R⟩; iframe

/-- **A restart's gathering**: the writer's share, the readers' and the streams' make the whole
(`lentOk`), with the streams' history slots. -/
theorem shares_join (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (E : Ep) (qw q qs : Qp) (nw n ns : Nat)
    (hq : qw.val + q.val + (ns : Rat) * qs.val = 1) (hn : nw + n + 2 * ns = mvccReaderN) :
    incShare (GF := GF) E.mp E.ι E.kv qw nw ∗ rdLent E.mp E.ι E.kv n q ∗
        ([∗list] _x ∈ List.replicate ns (), epochTok E qs) ⊢
      incShare E.mp E.ι E.kv 1 mvccReaderN ∗ histRds E.h E.γh ns := by
  iintro ⟨Hs, Hl, Ht⟩
  icases (rdLent_eq E.mp E.ι E.kv n q).1 $$ Hl with Hl
  ihave Hs : incShare E.mp E.ι E.kv (qw + q) (nw + n) $$ [Hs Hl]
  · iapply (incShare_add hsplit E.mp E.ι E.kv qw q nw n).2; iframe
  icases epochToks_join hpers hsplit E qs ns (qw + q) (nw + n) $$ [Hs Ht] with ⟨%a', %Ha', Hs, Hh⟩
  · iframe
  have h1 : a' = 1 := Subtype.ext (by rw [Ha', Qp.val_add, Qp.val_one, ← hq])
  rw [h1, hn] at *
  iframe

/-- **A restart's lending again**, at the reopened incarnation, with the same shares. -/
theorem shares_split (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (E : Ep) (qw q qs : Qp) (nw n ns : Nat)
    (hq : qw.val + q.val + (ns : Rat) * qs.val = 1) (hn : nw + n + 2 * ns = mvccReaderN) :
    isInc (GF := GF) E.ks E.γh E.i E.mp E.m E.ι E.kv ∗ incShare E.mp E.ι E.kv 1 mvccReaderN ∗
        histRds E.h E.γh ns ⊢
      incShare E.mp E.ι E.kv qw nw ∗ rdLent E.mp E.ι E.kv n q ∗
        ([∗list] _x ∈ List.replicate ns (), epochTok E qs) := by
  haveI := isInc_persistent hpers
  iintro ⟨#Hi, Hs, Hh⟩
  icases epochToks_split hpers hsplit E qs ns 1 (qw + q) (nw + n)
    (by rw [Qp.val_add, Qp.val_one, ← hq]) $$ [Hs Hh] with ⟨Hs, Ht⟩
  · rw [hn]; iframe; iexact Hi
  icases (incShare_add hsplit E.mp E.ι E.kv qw q nw n).1 $$ Hs with ⟨Hs, Hl⟩
  iframe
  iapply (rdLent_eq E.mp E.ι E.kv n q).2
  iframe

end shares

end mvccfull
end EtcdGrove
end Perennial
