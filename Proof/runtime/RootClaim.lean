/-
**The run's directory as the program finds it, and its own checks of it** (P3 of the pure-premise plan,
2026-11-24: the mvcc testers' `MainAt(r)`, which checks the directory `r` itself instead of the
closed theorem assuming it, `notes/STATUS.md`).

* **`rootClaimF r`**: what the file extension's start gives a program about a root `r` of the file
  system's model (`StartFiles.lean`'s `start_rootClaim`): the tree's shared invariants, the whole claim
  on the root directory's names (whatever they hold), and a share of the root's call permission.
* **`claims_of_names`** splits the claim into one claim per name of a list; **`fileHoldsF_of_only`**
  turns the claim on a name the program found empty into a fresh database file
  (`backend.fileHoldsF p ∅`, what bbolt's `Open` takes), as `StartFiles.lean`'s `files_of_claim` does
  at start from the premise that the name is absent.
* **`dirFits`'s loop** (the pure part): `tailRun p`, the bytes of `p` after its last `/`, which the Go
  loop counts; `Fs.WinOk p` (every 256-byte window of `p` holds a `/`) iff no prefix of `p` has a
  `tailRun` of 256 or more (`winOk_iff_tailRun`).
* `fsNoErrAt_of_all`: the semantics' `FsNoErrAll` gives `FsNoErrAt` of a path that fits.

Untrusted (definitions and lemmas). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import GooseLang.Ext.Fs.TreeShared
public import GooseLang.Ext.Fs.PathFitsLemmas
public import GooseLang.Ext.Fs.NoErrRemoveSteps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## `dirFits`'s loop -/

/-- One byte of `dirFits`'s loop: a `/` resets the run, any other byte extends it. -/
def tailRunStep (n : Nat) (c : w8) : Nat := if c = slashB then 0 else n + 1

/-- **The bytes of `p` after its last `/`** (all of `p` if it has none): `dirFits`'s `run` after
reading `p`. -/
def tailRun (p : GoString) : Nat := p.foldl tailRunStep 0

theorem tailRun_nil : tailRun [] = 0 := rfl

theorem tailRun_snoc (p : GoString) (c : w8) :
    tailRun (p ++ [c]) = if c = slashB then 0 else tailRun p + 1 := by
  unfold tailRun
  rw [List.foldl_append]
  rfl

/-- One more byte of `p`: `dirFits`'s loop body. -/
theorem tailRun_take_succ (p : GoString) (k : Nat) (c : w8) (h : p[k]? = some c) :
    tailRun (p.take (k + 1)) = if c = slashB then 0 else tailRun (p.take k) + 1 := by
  rw [List.take_succ, h, Option.toList_some, tailRun_snoc]

/-- Reading `/`-free bytes extends the run by their number. -/
theorem foldl_tailRunStep_noSlash :
    ∀ (q : GoString) (n : Nat), slashB ∉ q → q.foldl tailRunStep n = n + q.length
  | [], n, _ => by simp
  | c :: q, n, hq => by
    have hc : c ≠ slashB := fun h => hq (h ▸ List.mem_cons_self ..)
    have hq' : slashB ∉ q := fun h => hq (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons, foldl_tailRunStep_noSlash q _ hq']
    simp only [tailRunStep, if_neg hc, List.length_cons]
    omega

/-- The run is a `/`-free suffix of that length. -/
theorem tailRun_suffix_len :
    ∀ (k : Nat) (p : GoString), p.length = k →
      ∃ s u : GoString, p = s ++ u ∧ slashB ∉ u ∧ u.length = tailRun p
  | 0, p, hk => by
    rw [List.length_eq_zero_iff.1 hk]
    exact ⟨[], [], rfl, List.not_mem_nil, rfl⟩
  | k + 1, p, hk => by
    have hne : p ≠ [] := by intro h; subst h; simp at hk
    have hp := (List.dropLast_concat_getLast hne).symm
    generalize p.getLast hne = c at hp
    generalize hq : p.dropLast = q at hp
    have hql : q.length = k := by rw [← hq]; simp [hk]
    obtain ⟨s, u, hq', hu, hl⟩ := tailRun_suffix_len k q hql
    rw [hp, tailRun_snoc]
    by_cases hc : c = slashB
    · rw [if_pos hc]
      exact ⟨q ++ [c], [], (List.append_nil _).symm, List.not_mem_nil, rfl⟩
    · rw [if_neg hc]
      refine ⟨s, u ++ [c], by rw [hq', List.append_assoc], ?_, by simp [hl]⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hu, fun h => hc h.symm⟩

theorem tailRun_suffix (p : GoString) :
    ∃ s u : GoString, p = s ++ u ∧ slashB ∉ u ∧ u.length = tailRun p :=
  tailRun_suffix_len _ p rfl

/-- **`WinOk` is what `dirFits`'s loop checks**: every 256-byte window of `p` holds a `/` iff the run
stays under 256 after each byte. -/
theorem winOk_iff_tailRun (p : GoString) :
    WinOk p ↔ ∀ n, n ≤ p.length → tailRun (p.take n) < 256 := by
  constructor
  · intro hw n _
    refine Classical.byContradiction fun hge => ?_
    obtain ⟨s, u, hp, hu, hl⟩ := tailRun_suffix (p.take n)
    have hl' : 256 ≤ u.length := by omega
    -- the last 256 bytes of `u`, an infix of `p` with no `/`
    have hinf : u.drop (u.length - 256) <:+: p := by
      have h1 : u.drop (u.length - 256) <:+ u := List.drop_suffix _ _
      have h2 : u <:+ p.take n := ⟨s, hp.symm⟩
      exact (h1.trans h2).isInfix.trans (List.take_prefix n p).isInfix
    have hlen : (u.drop (u.length - 256)).length = 256 := by
      rw [List.length_drop]; omega
    exact hu (List.mem_of_mem_drop (hw _ hinf hlen))
  · intro ht q hq hl
    refine Classical.byContradiction fun hs => ?_
    obtain ⟨s, t, hst⟩ := hq
    have hn : (s ++ q).length ≤ p.length := by rw [← hst]; simp
    have htake : p.take (s ++ q).length = s ++ q := by
      rw [← hst]; exact List.take_left' rfl
    have h := ht _ hn
    rw [htake] at h
    unfold tailRun at h
    rw [List.foldl_append, foldl_tailRunStep_noSlash q _ hs] at h
    omega

/-- **`DirFits` is what `dirFits` checks**: under 3800 bytes, and the run under 256 after each
byte. -/
theorem dirFits_iff_tailRun (p : GoString) :
    DirFits p ↔ p.length < 3800 ∧ ∀ n, n ≤ p.length → tailRun (p.take n) < 256 := by
  unfold DirFits
  rw [winOk_iff_tailRun]

/-! ## The run's directory at start -/

section claims
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The root `r` as the program finds it at start** (`start_rootClaim`): `r` a root of the file
system's roots `R` (its directory `j0`), the tree's shared invariants, the whole claim on the names
of `r`'s directory (what they hold: `h`, any), and a share of `r`'s call permission. -/
def rootClaimF (r : GoString) : IProp GF :=
  iprop(∃ (R : Roots) (j0 : Ino) (h : NamesH) (q : Qp), ⌜(r, j0) ∈ R⌝ ∗
    osInv (L := hG.goose_localGS) ∗ osSharedInv (L := hG.goose_localGS) R ∗
    osNames (L := hG.goose_localGS) j0 (.except []) (DFrac.own 1) h ∗
    osCallPerm (L := hG.goose_localGS) (callKey R r) q)

/-- **The claim on the names of `j0` but `acc`, split along the names `bs`** (none in `acc`): one
whole claim per name. -/
theorem claims_of_names (R : Roots) (j0 : Ino) :
    ∀ (bs acc : List GoString) (h : NamesH), bs.Nodup → (∀ b ∈ bs, b ∉ acc) →
      ⊢ osSharedInv (L := hG.goose_localGS) R -∗
        osNames (L := hG.goose_localGS) j0 (.except acc) (DFrac.own 1) h ={⊤}=∗
        [∗list] b ∈ bs, ∃ hb : NamesH, osNames (L := hG.goose_localGS) j0 (.only [b]) (DFrac.own 1) hb
  | [], _, _, _, _ => by
    iintro - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: bs, acc, h, hnd, hacc => by
    iintro #Hsh Hn
    have hb : b ∉ acc := hacc b (List.mem_cons_self ..)
    have hsplit := osNames_split (E := ⊤) (L := hG.goose_localGS) R j0 (.except acc) [b] h
      (fun _ _ => CoPset.mem_full)
    have hin : (NameSet.except acc).inter [b] = .only [b] := by
      simp [NameSet.inter, hb]
    have hdiff : (NameSet.except acc).diff [b] = .except (acc ++ [b]) := rfl
    rw [hin, hdiff] at hsplit
    imod hsplit $$ Hsh Hn with ⟨Hb, Hrest⟩
    have hnd' := List.nodup_cons.1 hnd
    imod claims_of_names R j0 bs (acc ++ [b]) _ hnd'.2
      (fun b' hb' => by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hacc b' (List.mem_cons_of_mem _ hb'), fun he => hnd'.1 (he ▸ hb')⟩)
      $$ Hsh Hrest with Hfs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hfs
    iexists _
    iexact Hb

/-- **A name found empty is a fresh database file**: the whole claim on the name `b` of the root
`r`'s directory, holding nothing, with a share of `r`'s call permission, is `fileHoldsF (r/b) ∅`. -/
theorem fileHoldsF_of_only (R : Roots) (r b : GoString) (j0 : Ino) (h : NamesH) (q : Qp)
    (hr : (r, j0) ∈ R) (hb : NameOk b) (hfit : PathFits (child r b)) (hcur : h.cur !! b = none) :
    ⊢ osInv (L := hG.goose_localGS) -∗ osSharedInv (L := hG.goose_localGS) R -∗
      osNames (L := hG.goose_localGS) j0 (.only [b]) (DFrac.own 1) h -∗
      osCallPerm (L := hG.goose_localGS) (callKey R r) q ={⊤}=∗
      backend.fileHoldsF (GF := GF) (child r b) ∅ := by
  iintro #Hinv #Hsh Hb Hp
  imod osPathS_root (E := ⊤) (L := hG.goose_localGS) R r j0 (DFrac.own 1) hr
    (fun _ _ => CoPset.mem_full) $$ Hsh with Hpath
  imodintro
  unfold backend.fileHoldsF
  iexists R, r, b, DFrac.own 1, j0, q, h
  iframe Hinv Hsh Hpath Hp Hb
  isplitr
  · ipureintro; exact ⟨rfl, hb, hfit⟩
  unfold bbolt.nameHolds
  iright
  ipureintro
  exact ⟨hcur, rfl⟩

/-- **The names found empty, as fresh database files** (`fileHoldsF_of_only` of each, a share of
`r`'s call permission each). -/
theorem files_of_done (R : Roots) (r : GoString) (j0 : Ino) (hr : (r, j0) ∈ R) :
    ∀ (bs : List GoString) (q : Qp), (∀ b ∈ bs, NameOk b ∧ PathFits (child r b)) →
      ⊢ osInv (L := hG.goose_localGS) -∗ osSharedInv (L := hG.goose_localGS) R -∗
        ([∗list] b ∈ bs, ∃ hb : NamesH,
          osNames (L := hG.goose_localGS) j0 (.only [b]) (DFrac.own 1) hb ∗ ⌜hb.cur !! b = none⌝) -∗
        osCallPerm (L := hG.goose_localGS) (callKey R r) q ={⊤}=∗
        [∗list] b ∈ bs, backend.fileHoldsF (GF := GF) (child r b) ∅
  | [], _, _ => by
    iintro - - - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: bs, q, hok => by
    iintro #Hinv #Hsh Hl Hp
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨⟨%hb, Hb, %hn⟩, Hl⟩
    rw [← Qp.half_add_half q]
    icases (osCallPerm_split (L := hG.goose_localGS) (callKey R r) q.half q.half).1 $$ Hp
      with ⟨Hp1, Hp2⟩
    imod fileHoldsF_of_only R r b j0 hb q.half hr (hok b (List.mem_cons_self ..)).1
      (hok b (List.mem_cons_self ..)).2 hn $$ Hinv Hsh Hb Hp1 with Hf
    imod files_of_done R r j0 hr bs q.half (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
      $$ Hinv Hsh Hl Hp2 with Hfs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hf Hfs

end claims

/-- **The semantics' `FsNoErrAll` covers a path that fits** (`FsNoErrAt`). -/
theorem fsNoErrAt_of_all [GooseExts] [GoGlobalContext] [ExtSemantics fsExt] [backend.FsNoErrAll]
    {p : GoString} (hp : PathFits p) : FsNoErrAt p := by
  obtain ⟨Sio, hi, hpath, h1, h2⟩ := (inferInstance : backend.FsNoErrAll).ok
  exact ⟨⟨Sio, hi, h1, h2, fun p' _ => hpath p'⟩, hp⟩

end EtcdGrove
end Perennial

end
