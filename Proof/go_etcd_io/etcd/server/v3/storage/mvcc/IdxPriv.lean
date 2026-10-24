/-
**The index during the rebuild** (the restore plan, R3's design point): a tree index no one
else can reach, its `RWMutex` private memory (`PlainRWMutex.lean`), its tree and key indexes
owned (`ownTree` at `1`). `restoreIntoIndex`'s goroutine owns it while it rebuilds the index and
calls `put`/`tombstone` on cached key indexes outside the tree's lock; `store.restore` turns it
into a lock-protected `isTreeIndex` (`init_RWMutex`) once the goroutine is done. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.PlainRWMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

/-- Inserting an item equivalent to none of the items: a permutation of the item put in front. -/
theorem btInsert_perm_of_new {V : Type} {less : V → V → Prop} [DecidableRel less] (v : V) :
    ∀ (L : List V), (∀ w ∈ L, less w v ∨ less v w) → (btInsert less v L).Perm (v :: L)
  | [], _ => List.Perm.refl _
  | w :: ws, h => by
    unfold btInsert
    by_cases h1 : less w v
    · rw [ite_eq_left h1]
      have ih := btInsert_perm_of_new v ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
      exact (List.Perm.cons w ih).trans (List.Perm.swap v w ws)
    · rw [ite_eq_right h1]
      have h2 : less v w := (h w List.mem_cons_self).resolve_left h1
      rw [ite_eq_left h2]

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A tree index no one else can reach**, holding the entries `L`: its tree and logger (as
`isTreeIndex`), its `RWMutex` unlocked private memory, the tree and its key indexes owned. -/
def ownIdxPriv (ti : Loc) (L : List IdxEntry) : IProp GF :=
  iprop(∃ (t lg : Loc), ti.[treeIndex, go!"tree"] ↦□ t ∗ ti.[treeIndex, go!"lg"] ↦□ lg ∗
    ⌜lg ≠ null⌝ ∗ idxMuAddr ti ↦ rwZero ∗ ownTree t L 1)

/-- **The index lock's ghost part, before the lock exists** (`newTreeIndex` makes it; the rebuild
advances it and puts it in the lock it makes): the events' count's authority at `n`, the
compaction revision's lower bound `-1`, a lower bound of the committed log, and the compactor's
state as the lock holds it (`idxLockInv`). -/
def idxLockG (γ : IdxNames) (n : Nat) : IProp GF :=
  iprop(monoNatAuthOwn γ.nev 1 n ∗ crevLb γ (-1) ∗ (∃ log₀ : Log, monoListLbOwn γ.log log₀) ∗
    idxCmpOwn γ 1 [] (-1))

theorem idxReaders_of_toks (ti t : Loc) (γ : IdxNames) : ∀ (n : Nat),
    ti.[treeIndex, go!"tree"] ↦□ t ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (idxMuAddr ti) (idxLockInv (GF := GF) t γ)) ⊢
      [∗list] _x ∈ List.replicate n (), idxReader ti γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨#Ht, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iunfold idxReader; iexists t; iframe H1; iexact Ht
    · iapply idxReaders_of_toks ti t γ n; iframe Hs; iexact Ht

/-- **A private index made a lock-protected one** (`init_RWMutex` on its `RWMutex`, back at its
zero value): its entries `L` are the index of the writer's log (no compaction), the lock's ghost
part at the log's events. The index and every reader's token. -/
theorem idx_publish (ti : Loc) (γ : IdxNames) (L : List IdxEntry) (log : Log)
    (hrep : IdxCRep (-1) (evsOf (log ++ [[]])) (idxOfEntries L)) :
    ⊢ ownIdxPriv (GF := GF) ti L -∗ idxLockG γ (evsOf (log ++ [[]])).length -∗
      idxWriterLb γ log ={⊤}=∗
      isTreeIndex ti γ ∗ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        idxReader ti γ) := by
  iintro Hix Hg #Hw
  iunfold ownIdxPriv at Hix
  icases Hix with ⟨%t, %lg, #Htree, #Hlg, %Hlgnn, Hmu, Htr⟩
  iunfold idxLockG at Hg
  icases Hg with ⟨Hnauth, #Hclb, ⟨%log₀, #Hllb⟩, Hcmp⟩
  iunfold idxWriterLb at Hw
  icases Hw with ⟨#Hhlb, #Hnlb, %Hwf⟩
  imod sync.init_RWMutex (idxLockInv (hG := hG) t γ) (idxMuAddr ti) $$ [Hnauth Htr Hcmp] Hmu
    with Htoks
  · inext
    unfold idxLockInv
    iexists log, [], L, -1
    simp only [named]
    iframe Hnauth Htr Hhlb Hclb
    isplitl []
    · iexists log₀; iframe Hllb; ipureintro; omega
    isplitl []
    · ipureintro; exact ⟨hrep, Int.le_refl _⟩
    isplitl []
    · ipureintro; exact Hwf
    iapply idxCmpOwn_neg γ 1 [] L (-1) (by decide) $$ Hcmp
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  imodintro
  isplitl []
  · iunfold isTreeIndex
    iexists t, lg
    simp only [named]
    iframe #
    ipureintro; exact Hlgnn
  rw [← List.replicate_succ]
  iapply idxReaders_of_toks ti t γ (m + 1)
  isplitl []
  · iexact Htree
  rw [List.replicate_succ]
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

/-- **Fresh index names, split** for `newTreeIndex` (the event count's authority and the compactor's
state, with the lower bounds it takes) and the rest the store keeps: the writer's handle for the
empty log, the other half of the committed log's authority and the compaction revision's authority
at `-1` (`NewStore`; the restore plan's R5d). -/
theorem idxFresh_split (γ : IdxNames) :
    idxFresh (GF := GF) γ ⊢ |==> (monoNatAuthOwn γ.nev 1 0 ∗
      ghostVar γ.cmp 1 ((-1 : Int), ([] : List Loc)) ∗ crevLb γ (-1) ∗
      monoListLbOwn γ.log ([] : Log) ∗ idxWriter γ [] [] ∗ idxLogAuth γ (1 : Qp).half [] ∗
      crevUB γ 1 (-1)) := by
  iintro Hfresh
  iunfold idxFresh at Hfresh
  icases Hfresh with ⟨Hhauth, #Hhlb, Hnauth, #Hnlb, Hlauth, #Hllb, Hcauth, #Hclb, Hcmp⟩
  have hhalves := (monoListAuthOwn_fractional (GF := GF) γ.log ([] : Log)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hhalves
  icases hhalves.1 $$ Hlauth with ⟨Hlauth, Hlother⟩
  have hshape : histShape [] [] = [] := rfl
  have hevs : (evsOf ([] ++ [[]])).length = 0 := rfl
  have hwf : IdxWf [] [] := by
    refine ⟨⟨fun _ => rfl, fun r cs i k hr hi => ?_⟩, by simp, by simp, fun _ h => by simp at h⟩
    simp only [List.nil_append, List.getElem?_singleton] at hr
    split at hr
    · simp only [Option.some.injEq] at hr; subst hr; simp at hi
    · simp at hr
  imod receipt_zero (GF := GF) with Hr0
  imodintro
  iframe Hnauth Hcmp Hllb Hlother
  isplitl []
  · iunfold crevLb; rw [crevN_neg]; iexact Hclb
  isplitl [Hhauth Hlauth Hr0]
  · iunfold idxWriter
    rw [hshape, hevs]
    iframe Hhauth Hlauth
    isplitl []
    · iexact Hnlb
    isplitl []
    · ipureintro; exact hwf
    simp only [logCh, List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero]
    iexact Hr0
  iunfold crevUB; rw [crevN_neg]; iexact Hcauth

/-- **A new index's names over the store's** (`store.Restore`'s, the restore plan's R5d): the
store's history, committed-log and compaction names kept, fresh event-count and compactor names,
the event count's authority at `n` (the events of the restored log) and the compactor's state
whole, what `newTreeIndex` takes. -/
theorem idx_renew (γ : IdxNames) (n : Nat) :
    ⊢ |==> ∃ (nv cm : GName), monoNatAuthOwn (GF := GF) nv 1 n ∗ monoNatLbOwn nv n ∗
      ghostVar cm 1 ((-1 : Int), ([] : List Loc)) := by
  istart
  imod mono_nat_own_alloc (GF := GF) n with ⟨%nv, Hn, #Hnlb⟩
  imod ghostVar_alloc ((-1 : Int), ([] : List Loc)) with ⟨%cm, Hc⟩
  imodintro
  iexists nv, cm
  iframe
  iexact Hnlb

end reprs

end mvcc

end EtcdGrove
end Perennial
