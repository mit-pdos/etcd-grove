/-
The database's file into and out of its crash invariant (W1 of `plans/bbolt-crash-plan.md` §7;
Lean-first, no Rocq counterpart).

* `bfile_alloc`: the file whole and idle (as `Open` holds it, its `OsMeta` and every byte) becomes
  the crash-mode record `{ path, ino := i, cs := some c }`'s resources: the invariant
  (`bCsInv`, `csInvI` with the obligation `bCsOk` and the closing name `gc` the caller chooses:
  bbolt's `B.bq`), the writer's share of the `OsMeta` (`bMeta`, idle at `C`) and bbolt's share of
  every byte (`bBytes`, with fresh exclusivity tokens).
* `bfile_close`: back, with the closing token `csDone gc` (`ghostVar B.bq 1 ()`, from the
  `boltState γ 1` that `DB.Close` consumes): the file whole again, as `fileHoldsM` holds it.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFile
public import Proof.os.CrashStIL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
theorem exMap_lookup_ge (n k : Nat) (h : n ≤ k) : exMap n !! k = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((exMap n).insert n ()) !! k = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]; exact ih (by omega)

omit go_gctx sem in
/-- The exclusivity tokens of a fresh map of `n` keys, as the tokens of bytes `[0, n)`. -/
theorem exMap_frags (γ : GName) : ∀ n : Nat,
    ([∗map] k ↦ v ∈ exMap n, ghostMapElem (GF := GF) γ k (DFrac.own 1) v) ⊢
      [∗list] k ∈ List.range' 0 n, ghostMapElem (K := Nat) (V := Unit) γ k (DFrac.own 1) ()
  | 0 => by
    rw [List.range'_zero]; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | n + 1 => by
    show ([∗map] k ↦ v ∈ (exMap n).insert n (), ghostMapElem (GF := GF) γ k (DFrac.own 1) v) ⊢ _
    refine (BigSepM.bigSepM_insert (exMap_lookup_ge n n (Nat.le_refl _))).1.trans ?_
    rw [List.range'_1_concat, Nat.zero_add]
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_append.2
    iintro ⟨Hn, Hm⟩
    isplitl [Hm]
    · iapply exMap_frags γ n $$ Hm
    · iapply BigSepL.bigSepL_singleton.2; iexact Hn

/-- **The file whole and idle into its crash invariant** (see the file header). -/
theorem bfile_alloc (path : GoString) (i : Ino) (gc : GName) (N : Namespace) (C : CommitSt)
    (m : OsMeta) (xs : List ByteG) (a : BAbs) (E : CoPset) (hl : xs.length = m.size)
    (hcut : m.cut = none) (ha : a.phase = .idle ∧ a.cur = C)
    (hok : bCsOk a ⟨m, xs, 0, 0, .idle⟩) (hdur : ∀ x ∈ xs, x = durB x.1)
    (hlh : FsNoErr → m.lo = m.hi) :
    ⊢ osMeta (GF := GF) i (DFrac.own 1) m -∗ osBytes i 0 (DFrac.own 1) xs ={E}=∗
      ∃ c : CsN, ⌜c.gc = gc ∧ c.N = N⌝ ∗
        bCsInv (GF := GF) { path := path, ino := i, cs := some c } ∗
        bMeta { path := path, ino := i, cs := some c } C [] m ∗
        bBytes { path := path, ino := i, cs := some c } 0 (DFrac.own 1) xs := by
  iintro Hm Hb
  have hwf : (⟨m, xs, 0, 0, .idle⟩ : CSt).Wf := ⟨hl, Nat.le_refl _, Nat.zero_le _, trivial⟩
  imod csInvI_alloc_c N i gc bCsOk ⟨m, xs, 0, 0, .idle⟩ a E rfl
    (Nat.le_refl _) hwf hcut hok $$ Hm Hb with ⟨%γ, %γa, #Hinv, Hown⟩
  icases (csOwnI_split i γ γa ⟨m, xs, 0, 0, .idle⟩ a rfl rfl rfl).1 $$ Hown with ⟨Hown, Hb⟩
  imod ghost_map_alloc (GF := GF) (exMap m.size) with ⟨%γe, Hauth, Hfr⟩
  ihave Hfr := exMap_frags γe m.size $$ Hfr
  imodintro
  iexists ⟨γ, γa, gc, N, γe⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · unfold bCsInv; iexact Hinv
  unfold csOwnIL csOwnL
  icases Hown with ⟨Ht, Hm, %Hlok⟩
  isplitl [Ht Hm Hauth]
  · unfold bMeta; dsimp only
    iframe Hm Hauth
    iexists xs, a
    iframe Ht
    ipureintro
    exact ⟨hwf, ha.1, ha.2, fun k x hk _ => hdur x (List.mem_of_getElem? hk), hlh⟩
  · unfold bBytes bGhost BFile.dq; dsimp only [dhalf]
    rw [hl]
    iframe Hb Hfr

/-- **The file out of its crash invariant**: the writer's share of the `OsMeta`, bbolt's share of
every byte and the closing token give the file whole back (see the file header). -/
theorem bfile_close (p : BFile) (c : CsN) (hc : p.cs = some c) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta)
    (xs : List ByteG) (E : CoPset) (hE : ↑c.N ⊆ E) (hl : xs.length = m.size) :
    ⊢ bCsInv (GF := GF) p -∗ bMeta p C L m -∗ bBytes p 0 (DFrac.own 1) xs -∗ csDone c.gc ={E}=∗
      osMeta p.ino (DFrac.own 1) m ∗ osBytes p.ino 0 (DFrac.own 1) xs := by
  iintro #Hinv Hm Hb Hd
  ihave #Hinv := (show bCsInv (GF := GF) p ⊢ csInvI c.N p.ino c.g c.ga c.gc bCsOk by
    unfold bCsInv; rw [hc]) $$ Hinv
  ihave Hm := (show bMeta (GF := GF) p C L m ⊢ iprop(osMeta p.ino (DFrac.own (1 : Qp).half) m ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗
      ∃ (bs : List ByteG) (a : BAbs), csTokI c.g c.ga a (⟨m, bs, 0, 0, .idle⟩ : CSt) ∗
        ⌜(⟨m, bs, 0, 0, .idle⟩ : CSt).Wf ∧ a.phase = .idle ∧ a.cur = C ∧ DurOut L bs ∧
          (FsNoErr → m.lo = m.hi)⌝) by
    unfold bMeta; rw [hc]) $$ Hm
  icases Hm with ⟨Hm, -, %bs, %a, Ht, %Hf⟩
  icases (bBytes_os p 0 (DFrac.own 1) xs).1 $$ Hb with ⟨Hb, -⟩
  have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
  rw [hdq]
  have hbl : bs.length = m.size := Hf.1.1
  ihave Hown := (show csTokI (GF := GF) c.g c.ga a (⟨m, bs, 0, 0, .idle⟩ : CSt) ∗
      osMeta p.ino (DFrac.own (1 : Qp).half) m ⊢
      csOwnIL (GF := GF) p.ino c.g c.ga ⟨m, bs, 0, 0, .idle⟩ a from
    csOwnL_intro _ _ _ m rfl ⟨Hf.1, rfl, rfl, rfl⟩) $$ [Ht Hm]
  · iframe
  imod csOwnIL_agree c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a E hE 0
    (DFrac.own (1 : Qp).half) xs (by show 0 + xs.length ≤ bs.length; omega) $$ Hinv Hown Hb
    with ⟨Hown, Hb, %he⟩
  have hxb : xs = bs := by
    rw [he, List.drop_zero, hl, ← hbl, List.take_length]
  subst hxb
  ihave Hown := (csOwnI_split p.ino c.g c.ga ⟨m, xs, 0, 0, .idle⟩ a rfl rfl rfl).2 $$ [Hown Hb]
  · iframe
  iapply csInvI_close c.N p.ino c.g c.ga c.gc bCsOk ⟨m, xs, 0, 0, .idle⟩ a E hE rfl
    (Nat.le_refl _) $$ Hinv Hown Hd
