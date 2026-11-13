/-
Lemmas of `fileutil.TouchDirAll`'s proof (W4, sixth session): the ancestors of `d = parent/name` as
paths of a prefix of its components (`os.ancPath`: `Clean`, `Dir`, the length), a spine split along a
prefix (`osSpine_app`), and `Stat`/`syncDir` of any ancestor of `parent` (`wp_statAnc`, `wp_syncDirAnc`):
over a borrowed prefix of `parent`'s spine below the root, over the above-root hypotheses above it.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir
public import LinuxFs.Proof.os.StatS
public import LinuxFs.Proof.os.MkdirAllParts
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

/-! ## Paths -/

theorem joinPath_nil_segs (l : List GoString) : joinPath [] l = path.segsPath l := by
  rw [segsPath_flatMap]; simp [joinPath]; rfl

theorem joinPath_joinPath (a b : List GoString) : joinPath (joinPath [] a) b = joinPath [] (a ++ b) := by
  simp [joinPath, List.flatMap_append]

theorem ancPath_ne {l : List GoString} (hne : l ≠ []) : os.ancPath l = joinPath [] l := by
  simp [os.ancPath, hne]

theorem ancPath_cleanAbs {l : List GoString} (hne : l ≠ []) (hl : ∀ c ∈ l, NameOk c) :
    filepath.CleanAbs (os.ancPath l) :=
  ⟨l, hne, fun c hc => cleanSeg_of_nameOk (hl c hc), by rw [ancPath_ne hne, joinPath_nil_segs]⟩

theorem ancPath_clean {l : List GoString} (hne : l ≠ []) (hl : ∀ c ∈ l, NameOk c) :
    path.cleanModel (os.ancPath l) = os.ancPath l :=
  filepath.cleanModel_cleanAbs _ (ancPath_cleanAbs hne hl)

theorem ancPath_snoc (l : List GoString) (c : GoString) :
    os.ancPath (l ++ [c]) = joinPath [] l ++ [path.slash] ++ c := by
  rw [ancPath_ne (by simp)]; simp [joinPath]; rfl

theorem dir_ancPath_snoc (l : List GoString) (c : GoString) (hl : ∀ x ∈ l, NameOk x) (hc : NameOk c) :
    path.dirModel (os.ancPath (l ++ [c])) = os.ancPath l := by
  rw [ancPath_snoc]
  by_cases hne : l = []
  · subst hne
    have h1 := path.lastIndexByte_seg [] c (cleanSeg_of_nameOk hc).2.1
    simp only [joinPath, List.flatMap_nil, List.append_nil]
    unfold path.dirModel path.splitModel
    rw [h1]
    simp [os.ancPath]
    decide
  · rw [ancPath_ne hne, joinPath_nil_segs]
    exact filepath.dirModel_name _ c ⟨l, hne, fun x hx => cleanSeg_of_nameOk (hl x hx), rfl⟩
      (cleanSeg_of_nameOk hc)

theorem dir_root : path.dirModel (os.ancPath []) = os.ancPath [] := by
  simp only [os.ancPath, ↓reduceIte]; try decide

theorem ancPath_length_lt (l : List GoString) (c : GoString) (hc : NameOk c) :
    (os.ancPath l).length < (os.ancPath (l ++ [c])).length := by
  rw [ancPath_snoc]
  have : 0 < c.length := by cases c with | nil => exact absurd rfl hc.1 | cons _ _ => simp
  by_cases hne : l = []
  · subst hne; simp [os.ancPath, joinPath]; omega
  · rw [ancPath_ne hne]; simp; try omega

/-- `Dir` of the path of the first `m` components: of the first `m - 1` (`/` for `m ≤ 1`). -/
theorem dir_take (full : List GoString) (hf : ∀ c ∈ full, NameOk c) (m : Nat) (hm : m ≤ full.length) :
    path.dirModel (os.ancPath (full.take m)) = os.ancPath (full.take (m - 1)) := by
  cases m with
  | zero => simpa using dir_root
  | succ m =>
    have hm' : m < full.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hm']
    simp only [Option.toList_some, Nat.add_sub_cancel]
    exact dir_ancPath_snoc _ _ (fun x hx => hf x (List.mem_of_mem_take hx)) (hf _ (List.getElem_mem hm'))

/-- The path of the first `m ≥ 1` components is not its own `Dir`. -/
theorem dir_take_ne (full : List GoString) (hf : ∀ c ∈ full, NameOk c) (m : Nat) (h0 : 0 < m)
    (hm : m ≤ full.length) :
    path.dirModel (os.ancPath (full.take m)) ≠ os.ancPath (full.take m) := by
  rw [dir_take full hf m hm]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : m' < full.length := by omega
  intro he
  have := ancPath_length_lt (full.take m') full[m'] (hf _ (List.getElem_mem hm'))
  have hx : full.take (m' + 1) = full.take m' ++ [full[m']] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm']; simp
  rw [Nat.add_sub_cancel, hx] at he
  rw [he] at this
  exact Nat.lt_irrefl _ this

/-! ## Spines -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem osSpine_app (a b : List GoString) (j : Ino) (dq : DFrac) (J : Ino) :
    osSpine (GF := GF) j (a ++ b) dq J ⊣⊢ ∃ jm, osSpine (GF := GF) j a dq jm ∗ osSpine jm b dq J := by
  induction a generalizing j with
  | nil =>
    simp only [List.nil_append, osSpine]
    constructor
    · iintro H; iexists j; iframe; ipureintro; rfl
    · iintro ⟨%jm, %h, H⟩; subst h; iexact H
  | cons c a ih =>
    simp only [List.cons_append, osSpine]
    constructor
    · iintro ⟨%h, %J', Hn, %hJ, Hs⟩
      icases (ih J').1 $$ Hs with ⟨%jm, Ha, Hb⟩
      iexists jm
      isplitl [Hn Ha]
      · iexists h, J'
        iframe
        ipureintro; exact hJ
      iexact Hb
    · iintro ⟨%jm, ⟨%h, %J', Hn, %hJ, Ha⟩, Hb⟩
      iexists h, J'
      iframe
      isplitr
      · ipureintro; exact hJ
      iapply (ih J').2
      iexists jm
      iframe

theorem osSpine_split (cs : List GoString) (m : Nat) (j : Ino) (dq : DFrac) (J : Ino) :
    osSpine (GF := GF) j cs dq J ⊣⊢
      ∃ jm, osSpine (GF := GF) j (cs.take m) dq jm ∗ osSpine jm (cs.drop m) dq J := by
  conv => lhs; rw [← List.take_append_drop m cs]
  exact osSpine_app _ _ j dq J

/-- **`Stat` of an ancestor of `parent`** (the path of the first `k` components of `rcs ++ cs`, the
root `/rcs` and the spine's `cs`): below the root, over a borrowed prefix of the spine
(`os.Stat.wp_dirS`); above it, the hypothesis. -/
theorem wp_statAnc (hAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG)) (R : Roots)
    (rcs cs : List GoString) (j0 jp : Ino) (dq : DFrac) (qc : Qp) (k : Nat) (hR : RootsOk R)
    (hm : (joinPath [] rcs, j0) ∈ R) (hrcs : rcs ≠ []) (hcs : ∀ c ∈ cs, NameOk c)
    (hk : k ≤ (rcs ++ cs).length) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs dq jp ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #(os.ancPath ((rcs ++ cs).take k))))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osSpine j0 cs dq jp ∗
        osCallPerm qc }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hs, Hperm⟩ HΦ
  by_cases hlt : k < rcs.length
  · rw [List.take_append_of_le_length (by omega)]
    wp_apply hAbove _ R qc ⟨rcs, j0, k, hm, hlt, rfl⟩ $$ [Hperm] as %fi %err Hperm
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
  · obtain ⟨m, rfl⟩ : ∃ m, k = rcs.length + m := ⟨k - rcs.length, by omega⟩
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      ancPath_ne (by simp [hrcs]), ← joinPath_joinPath]
    icases (osSpine_split cs m j0 dq jp).1 $$ Hs with ⟨%jm, Ha, Hb⟩
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 (cs.take m) dq jm hR hm
      (fun c hc => hcs c (List.mem_of_mem_take hc))).2 $$ Ha
    wp_apply os.Stat.wp_dirS _ R jm dq qc $$ [Hp Hperm] as %fi %err ⟨Hp, Hperm, -⟩
    · iframe; isplitl [] <;> iassumption
    ihave Ha := (os.osPathS_joinPath R (joinPath [] rcs) j0 (cs.take m) dq jm hR hm
      (fun c hc => hcs c (List.mem_of_mem_take hc))).1 $$ Hp
    iapply HΦ
    iframe
    iapply (osSpine_split cs m j0 dq jp).2
    iexists jm
    iframe

/-- **`syncDir` of an ancestor of `parent`**: below the root over a borrowed prefix of the spine,
committing on success; above it, the hypothesis (nothing known). -/
theorem wp_syncDirAnc
    (hSync : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec (GF := GF) (hG := hG))
    (hAbove : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.specAboveRoot (GF := GF) (hG := hG))
    (R : Roots) (rcs cs : List GoString) (j0 jp : Ino) (dq : DFrac) (qc : Qp) (n k : Nat)
    (hR : RootsOk R) (hm : (joinPath [] rcs, j0) ∈ R) (hrcs : rcs ≠ []) (hcs : ∀ c ∈ cs, NameOk c)
    (hk : k ≤ (rcs ++ cs).length) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs dq jp ∗ osCallPerm qc ∗ osLogLb n }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir))
        (Val #(os.ancPath ((rcs ++ cs).take k))))
    {{ (err : GoInterface), RET #err; osSpine j0 cs dq jp ∗ osCallPerm qc ∗
        (⌜rcs.length ≤ k⌝ -∗ ⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ osCommitLb n) }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hs, Hperm, #Hlb⟩ HΦ
  by_cases hlt : k < rcs.length
  · rw [List.take_append_of_le_length (by omega)]
    wp_apply hAbove _ R qc ⟨rcs, j0, k, hm, hlt, rfl⟩ $$ [Hperm] as %err Hperm
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    iintro %hle
    exfalso; omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = rcs.length + m := ⟨k - rcs.length, by omega⟩
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      ancPath_ne (by simp [hrcs]), ← joinPath_joinPath]
    icases (osSpine_split cs m j0 dq jp).1 $$ Hs with ⟨%jm, Ha, Hb⟩
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 (cs.take m) dq jm hR hm
      (fun c hc => hcs c (List.mem_of_mem_take hc))).2 $$ Ha
    wp_apply hSync _ R jm dq qc n $$ [Hp Hperm] as %err ⟨Hp, Hperm, Hr⟩
    · iframe; iframe #
    ihave Ha := (os.osPathS_joinPath R (joinPath [] rcs) j0 (cs.take m) dq jm hR hm
      (fun c hc => hcs c (List.mem_of_mem_take hc))).1 $$ Hp
    iapply HΦ
    isplitl [Ha Hb]
    · iapply (osSpine_split cs m j0 dq jp).2
      iexists jm
      iframe
    isplitl [Hperm]
    · iexact Hperm
    iintro -
    iexact Hr

end iris

end EtcdGrove
end Perennial
