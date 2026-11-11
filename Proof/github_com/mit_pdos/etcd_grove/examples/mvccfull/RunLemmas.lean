/-
mvccfull's entry point `Run`: the lemmas of its proof (`Run.lean`). Lean-first (no Rocq counterpart).

The run's allocations: a report counter's invariant (`ctrInv_alloc`) and its `Load` (`ctrInv_load`),
the history's lock with its reader slots (`hist_allocF`, as mvccrand's `hist_alloc`), the slots split
(`histRds_add`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.OpenLemmas
public import Perennial.Spec.sync.atomic.Int64__Load

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/-- The keys `walkM p n` adds are at most `n` letters longer than `p`. -/
theorem walkM_len_le : ∀ (n : Nat) (p : GoString), ∀ k ∈ walkM p n, k.length ≤ p.length + n
  | 0, p => by
    intro k hk
    simp only [walkM] at hk
    split at hk
    · simp at hk
    · simp only [List.mem_singleton] at hk; subst hk; omega
  | n + 1, p => by
    intro k hk
    simp only [walkM, List.mem_append] at hk
    rcases hk with ((h | h) | h) | h
    · split at h
      · simp at h
      · simp only [List.mem_singleton] at h; subst h; omega
    all_goals
      have := walkM_len_le n _ k h
      simp only [List.length_append, List.length_singleton] at this
      omega

/-- A non-empty prefix adds at least `n + 1` keys. -/
theorem walkM_len_ge : ∀ (n : Nat) (p : GoString), p ≠ [] → n + 1 ≤ (walkM p n).length
  | 0, p, hp => by simp [walkM, hp]
  | n + 1, p, hp => by
    have := walkM_len_ge n (p ++ [W8 97]) (by simp)
    simp only [walkM, hp, ite_false, List.length_append, List.length_singleton]
    omega

/-- **The keys at depth `d`**: at least `d` of them, each at most `d` long. -/
theorem keysOf_bounds (d : Nat) :
    d ≤ (keysOf d).length ∧ ∀ k ∈ keysOf d, k.length ≤ d := by
  refine ⟨?_, fun k hk => by have := walkM_len_le d [] k hk; simpa using this⟩
  cases d with
  | zero => omega
  | succ n =>
    have := walkM_len_ge n [W8 97] (by simp)
    unfold keysOf
    simp only [walkM, ite_true, List.nil_append, List.length_append]
    omega

/-- **The run's shares of an incarnation**: the writer's, the readers' and each of `n` streams'
the same, `1 / (n + 2)`. -/
def runShare (n : Nat) : Qp := ⟨1 / ((n : Rat) + 2), by
  have : (0 : Rat) < (n : Rat) + 2 := by
    have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
    grind
  exact Rat.div_pos (by decide) this⟩

theorem runShare_sum (n : Nat) :
    (runShare n).val + (runShare n).val + (n : Rat) * (runShare n).val = 1 := by
  have h : (0 : Rat) < (n : Rat) + 2 := by
    have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
    grind
  show 1 / ((n : Rat) + 2) + 1 / ((n : Rat) + 2) + (n : Rat) * (1 / ((n : Rat) + 2)) = 1
  have hc := Rat.mul_inv_cancel ((n : Rat) + 2) (Rat.ne_of_gt h)
  simp only [Rat.div_def, Rat.one_mul]
  grind

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A fresh counter's invariant** (a zero atomic). -/
theorem ctrInv_alloc (N : Namespace) (l : Loc) :
    (l ↦ (zeroValDef : sync.atomic.Int64) : IProp GF) ⊢ |={⊤}=> ctrInv N l := by
  iintro H
  ihave H := ownInt64_of_zero l $$ H
  imod inv_alloc N ⊤ (∃ v : w64, sync.atomic.ownInt64 (GF := GF) l (DFrac.own 1) v) $$ [H] with #Hi
  · inext; iexists _; iexact H
  imodintro
  iunfold ctrInv
  iexact Hi

/-- **A counter's `Load`**, at any value. -/
theorem ctrInv_load (N : Namespace) (l : Loc) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ ctrInv N l -∗ (∀ v : w64, Φ #v) -∗
      WP (App (Val (l @!! go.GoType.PointerType sync.atomic.Int64.ty @!! go!"Load")) (Val #()))
        {{ Φ }} := by
  haveI : Persistent (ctrInv (GF := GF) N l) := by unfold ctrInv; infer_instance
  iintro #Hp #Hc HΦ
  iapply (sync.atomic.Int64.wp_Load l (DFrac.own 1)) $$ Hp
  iunfold ctrInv at Hc
  iinv Hc with ⟨%a, >Ha⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑N from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists a
  iframe
  iintro Ha
  imod Hcl with -
  imod Hclose $$ [Ha] with -
  · inext; iexists _; iframe
  imodintro
  iapply HΦ

/-- `n` handles of the history from as many reader slots. -/
theorem histRds_of (h : Loc) (γh : HistNames) : ∀ n : Nat,
    isHistory (GF := GF) h γh ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (hMu h) (histR h γh)) ⊢ histRds h γh n
  | 0 => by
    iintro -
    iunfold histRds
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2; itrivial
  | n + 1 => by
    iintro ⟨#Hh, Hs⟩
    iunfold histRds
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iunfold histRd; iframe Hh H1
    · ihave H := histRds_of h γh n $$ [Hs]
      · iframe Hh Hs
      iunfold histRds at H
      iexact H

/-- **The history's lock and `n` handles**, at most the lock's reader slots. -/
theorem hist_allocF (h : Loc) (γh : HistNames) (n : Nat)
    (hn : n ≤ Int.toNat sync.rwmutex.actualMaxReaders) :
    hMu h ↦ zero_val sync.RWMutex ∗ histR (GF := GF) h γh 1 ⊢
      |={⊤}=> isHistory h γh ∗ histRds h γh n := by
  iintro ⟨Hmu, Hr⟩
  imod sync.init_RWMutex (histR (GF := GF) h γh) (E := ⊤) (hMu h) $$ [Hr] Hmu with Hslots
  · inext; iexact Hr
  ihave ⟨Hslots, #Hg⟩ := sync.ownRWMutex_slots_guard (hMu h) (histR (GF := GF) h γh) $$ Hslots
  ihave #Hh : isHistory (GF := GF) h γh $$ []
  · iunfold isHistory; iexact Hg
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = n + m :=
    ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm]
  icases (backend.bigSepL_replicate_add _ n m).1 $$ Hslots with ⟨Hn, -⟩
  imodintro
  iframe Hh
  iapply histRds_of h γh n $$ [Hn]
  iframe Hh Hn

/-- The history's handles split. -/
theorem histRds_add (h : Loc) (γh : HistNames) (a b : Nat) :
    histRds (GF := GF) h γh (a + b) ⊣⊢ histRds h γh a ∗ histRds h γh b := by
  unfold histRds
  exact backend.bigSepL_replicate_add _ a b

/-- One handle. -/
theorem histRds_one (h : Loc) (γh : HistNames) :
    histRds (GF := GF) h γh 1 ⊣⊢ histRd h γh := by
  unfold histRds
  exact BigSepL.bigSepL_singleton

/-- **The writer's `kv` field share, out of a member** (for `startEpoch`, which reads it). -/
theorem memW_kv (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc)
    (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) :
    memW (GF := GF) ks γh ops i mp m f v qw nw k ⊢
      mF go!"kv" mp ↦{DFrac.own qw} v.kv ∗
        (mF go!"kv" mp ↦{DFrac.own qw} v.kv -∗ memW ks γh ops i mp m f v qw nw k) := by
  unfold memW memCore
  dsimp only
  iintro ⟨Ho, Hh, Hid, Hhk, Hhok, Hp, Hb, Hl, Hk, Hrest⟩
  iframe Hk
  iintro Hk
  iframe

/-- **A member's shares lent** to an epoch's readers and streams (`shares_split`, from the whole). -/
theorem memW_lend (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (ks : List GoString) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (k : Nat)
    (x h : Loc) (cfg : Config) (qw q qs : Qp) (nw n ns : Nat)
    (hq : qw.val + q.val + (ns : Rat) * qs.val = 1) (hn : nw + n + 2 * ns = mvccReaderN) :
    memW (GF := GF) ks γh ops i mp m f v 1 mvccReaderN k ∗ histRds h γh ns ⊢
      memW ks γh ops i mp m f v qw nw k ∗ rdLent mp v.ι v.kv n q ∗
        [∗list] _x ∈ List.replicate ns (), epochTok ⟨x, h, ks, γh, cfg, i, mp, m, v.ι, v.kv⟩ qs := by
  haveI := isInc_persistent hpers
  iintro ⟨Hm, Hhs⟩
  iunfold memW at Hm
  iunfold memCore at Hm
  icases Hm with ⟨Ho, Hh, #Hid, #Hhk, Hhok, Hp, Hb, Hl, Hkv, Hrev, Hcmp, Hls, %Hv, Hinc, Hopen,
    Hback, HhookIs, Hrdrs, Hbk, Hles, %HU⟩
  iunfold incW at Hinc
  icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
  ihave Hsh : incShare mp v.ι v.kv 1 mvccReaderN $$ [Hret Hkv Hrdrs]
  · iunfold incShare; iframe
  icases shares_split hpers hsplit ⟨x, h, ks, γh, cfg, i, mp, m, v.ι, v.kv⟩ qw q qs nw n ns hq hn
    $$ [Hsh Hhs] with ⟨Hsh, Hlent, Htoks⟩
  · iframe #; iframe
  iunfold incShare at Hsh
  icases Hsh with ⟨Hret, Hkv, Hrdrs⟩
  iframe Hlent Htoks
  iunfold memW; iunfold memCore; dsimp only; iunfold incW
  iframe #; iframe
  ipureintro; exact ⟨Hv, HU⟩

/-- **A member's shares gathered back** (`shares_join`, the whole). -/
theorem memW_gather (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hsplit : mvcc.api.mvccReaders_split.law (GF := GF)) (ks : List GoString) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (k : Nat)
    (x h : Loc) (cfg : Config) (qw q qs : Qp) (nw n ns : Nat)
    (hq : qw.val + q.val + (ns : Rat) * qs.val = 1) (hn : nw + n + 2 * ns = mvccReaderN) :
    memW (GF := GF) ks γh ops i mp m f v qw nw k ∗ rdLent mp v.ι v.kv n q ∗
        ([∗list] _x ∈ List.replicate ns (), epochTok ⟨x, h, ks, γh, cfg, i, mp, m, v.ι, v.kv⟩ qs) ⊢
      memW ks γh ops i mp m f v 1 mvccReaderN k ∗ histRds h γh ns := by
  haveI := isInc_persistent hpers
  iintro ⟨Hm, Hlent, Htoks⟩
  iunfold memW at Hm
  iunfold memCore at Hm
  icases Hm with ⟨Ho, Hh, #Hid, #Hhk, Hhok, Hp, Hb, Hl, Hkv, Hrev, Hcmp, Hls, %Hv, Hinc, Hopen,
    Hback, HhookIs, Hrdrs, Hbk, Hles, %HU⟩
  iunfold incW at Hinc
  icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
  ihave Hsh : incShare mp v.ι v.kv qw nw $$ [Hret Hkv Hrdrs]
  · iunfold incShare; iframe
  icases shares_join hpers hsplit ⟨x, h, ks, γh, cfg, i, mp, m, v.ι, v.kv⟩ qw q qs nw n ns hq hn
    $$ [Hsh Hlent Htoks] with ⟨Hsh, Hhs⟩
  · iframe
  iunfold incShare at Hsh
  icases Hsh with ⟨Hret, Hkv, Hrdrs⟩
  iframe Hhs
  iunfold memW; iunfold memCore; dsimp only; iunfold incW
  iframe #; iframe
  ipureintro; exact ⟨Hv, HU⟩

/-- **A member at the run's end** (`write`'s post, the readers stopped: what `Run`'s final loop
takes of member `i`): the writer's part (`memW`, at the log's end) at its shares `qw`, `nw` with the
lent ones (`q` to the readers, given back: `rdLent`; `qs` to each stream: `epochStream`), and the
member's `regs` counter. -/
def memEnd (x h : Loc) (ks : List GoString) (γh : HistNames) (cfg : Config) (ops : List OpM)
    (q qs : Qp) (n i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) : IProp GF :=
  iprop(∃ (qw : Qp) (nw k : Nat), memW ks γh ops i mp m f v qw nw k ∗
    ⌜qw.val + q.val + ((sint.Z cfg.Streams').toNat : Rat) * qs.val = 1 ∧
      nw + n + 2 * (sint.Z cfg.Streams').toNat = mvccReaderN ∧ 1 ≤ nw ∧ v.ops = ops.length⌝ ∗
    (∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" mp ↦ sl ∗ sl ↦* ss ∗
      ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = (sint.Z cfg.Streams').toNat⌝ ∗
      [∗list] s ∈ ss, epochStream ⟨x, h, ks, γh, cfg, i, mp, m, v.ι, v.kv⟩ qs s) ∗
    rdLent mp v.ι v.kv n q ∗ ctrInv (sCtrN .@ "regs") (mF go!"regs" mp))

end lemmas

end mvccfull
end EtcdGrove
end Perennial
