/-
The definitions and lemmas of `TouchDirAll.lean`'s proofs (`touchC`, `wp_existAnc`, `merged_cur`, ...), in
a module of their own (import tiers, 2026-11-18; `TouchDirAllDir.lean`, which imported them, retired 2026-11-22).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import Spec.os.MkdirAll
public import Spec.path.filepath.Clean
public import Spec.path.filepath.Dir
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchLemmas
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteableLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

/-- The directories `TouchDirAll`'s first loop has collected once its `d` is the path of the first `m - 1`
components of `full` (`d = parent/name` the path of all of them): the paths of the first `m`, …,
`|full|` components, outermost first. -/
def touchC (full : List GoString) (m : Nat) : List GoString :=
  (List.range' m (full.length + 1 - m)).map (fun i => os.ancPath (full.take i))

theorem touchC_cons (full : List GoString) (m : Nat) (hm : m ≤ full.length) :
    touchC full m = os.ancPath (full.take m) :: touchC full (m + 1) := by
  unfold touchC
  rw [show full.length + 1 - m = (full.length + 1 - (m + 1)) + 1 by omega, List.range'_succ]
  simp

theorem touchC_end (full : List GoString) : touchC full (full.length + 1) = [] := by
  simp [touchC]

theorem touchC_length (full : List GoString) (m : Nat) :
    (touchC full m).length = full.length + 1 - m := by
  simp [touchC]

theorem touchC_get (full : List GoString) (m i : Nat) (hi : i < (touchC full m).length) :
    (touchC full m)[i] = os.ancPath (full.take (m + i)) := by
  simp [touchC]

/-- `verify.Assert(true, …)` returns. -/
theorem wp_verifyAssert_true (msg : GoString) (v : GoSlice) :
    {{ (emp : IProp GF) }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.verify.Assert)) (Val #true)) (Val #msg)) (Val #v))
    {{ RET #(); emp }} := by
  wp_start as -
  wp_auto
  iapply HΦ
  iempintro

/-- `Exist` of the path of the first `k` components of `full = rcs ++ cs ++ [name]` (`/rcs` a root,
`cs` the spine's, `name` absent): some answer, `false` for `full` itself. -/
theorem wp_existAnc (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG))
    (R : Roots) (rcs cs : List GoString) (name : GoString) (full : List GoString) (j0 jp : Ino) (qp : Qp)
    (h : NamesH) (k : Nat) (hfull : full = (rcs ++ cs) ++ [name]) (hR : RootsOk R)
    (hm : (joinPath [] rcs, j0) ∈ R) (hrcs : rcs ≠ []) (hcs : ∀ c ∈ cs, NameOk c) (hname : NameOk name)
    (hnone : h.cur !! name = none) (hk : k ≤ full.length) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs (DFrac.own qp) jp ∗
        osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm (callKey R (joinPath [] rcs)) 1 }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #(os.ancPath (full.take k))))
    {{ (b : Bool), RET #b; osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗
        osCallPerm (callKey R (joinPath [] rcs)) 1 ∗ ⌜k = full.length → b = false⌝ }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hs, Hn, Hperm⟩ HΦ
  by_cases hkn : k = full.length
  · subst hkn
    have hdir : os.ancPath (full.take full.length) = child (joinPath (joinPath [] rcs) cs) name := by
      rw [List.take_length, ancPath_ne (by subst hfull; simp), hfull, joinPath_snoc, joinPath_joinPath]
    rw [hdir, ← callKey_joinPath hR hm cs]
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
    wp_apply wp_Exist (child (joinPath (joinPath [] rcs) cs) name) _ _
      (os.Stat.wp_absentS _ name R jp (.only [name]) (DFrac.own qp) (DFrac.own 1) h 1 hname
        (by simp [NameSet.Mem]) hnone) $$ [Hp Hn Hperm] as %b ⟨%err, %hb, Hp, Hn, Hperm, %herr⟩
    · iframe; isplitl [] <;> iassumption
    ihave Hs := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).1 $$ Hp
    iapply HΦ
    iframe
    ipureintro; intro _; simp [hb, herr]
  · have hfl : full.length = (rcs ++ cs).length + 1 := by subst hfull; simp; omega
    have hk' : k ≤ (rcs ++ cs).length := by omega
    rw [show full.take k = (rcs ++ cs).take k by subst hfull; rw [List.take_append_of_le_length hk']]
    wp_apply wp_Exist _ _ _ (wp_statAnc hStatAbove R rcs cs j0 jp (DFrac.own qp) 1 k hR hm hrcs hcs hk')
      $$ [Hs Hperm] as %b ⟨%err, %hb, Hs, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd h hkn

/-- A `mkdir`'s outcome on a claim held as two halves. -/
theorem mkOut_join (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    mkOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ∗ mkOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ⊢
      mkOut j b h (DFrac.own 1) o := by
  cases o with
  | none =>
    simp only [mkOut]
    iintro ⟨H1, H2⟩
    iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1 $$ [$H1 $H2]
  | some xsJ =>
    obtain ⟨x, s, J⟩ := xsJ
    simp only [mkOut]
    iintro ⟨⟨Hl, H1⟩, ⟨-, H2⟩⟩
    iframe Hl
    iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1 $$ [$H1 $H2]

/-- An absent name, its claim whole: `tmpDirH`. -/
theorem tmpDirH_none (j : Ino) (b : GoString) (h : NamesH) (hb : h.cur !! b = none) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ⊢ tmpDirH j b h := by
  unfold tmpDirH
  rw [hb]
  unfold tmpSub
  iintro Hn
  isplitl [Hn]
  · iexact Hn
  · iempintro

/-- A name holding a directory that holds no directory, both claims whole, with its `.touch`'s
file: `tmpDirH`. -/
theorem tmpDirH_dir (j : Ino) (b : GoString) (h : NamesH) (J : Ino) (hJ : NamesH)
    (hb : h.cur !! b = some (.dir J)) (hno : ∀ c J', hJ.cur !! c ≠ some (.dir J')) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
      tmpEnt (hJ.cur !! go!".touch") ⊢ tmpDirH j b h := by
  unfold tmpDirH
  rw [hb]
  unfold tmpSub
  iintro ⟨Hn, HJ, HT⟩
  iframe Hn
  iexists hJ
  iframe HJ HT
  ipureintro
  intro c n hc
  cases n with
  | file i => exact ⟨i, rfl⟩
  | dir J' => exact absurd hc (hno c J')

/-- A name holding an empty directory, both claims whole: `tmpDirH`. -/
theorem tmpDirH_dirE (j : Ino) (b : GoString) (h : NamesH) (J : Ino) (hJ : NamesH)
    (hb : h.cur !! b = some (.dir J)) (he : hJ.cur = ∅) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ⊢
      tmpDirH j b h := by
  iintro ⟨Hn, HJ⟩
  iapply tmpDirH_dir j b h J hJ hb (fun c J' hc => by rw [he] at hc; simp at hc)
  iframe Hn HJ
  rw [show hJ.cur !! go!".touch" = none by rw [he]; simp]
  unfold tmpEnt
  iempintro

/-- What `IsDirWriteable` leaves at `.touch`: no directory, and its file whole if any. -/
theorem touchOut_tmpEnt (o : Option Node) :
    (⌜o = none⌝ ∨ ∃ i, ⌜o = some (.file i)⌝ ∗ trFile (GF := GF) i False) ⊢
      ⌜∀ J', o ≠ some (.dir J')⌝ ∗ tmpEnt o := by
  iintro (%h | ⟨%i, %h, Ht⟩)
  · subst h; isplitl []
    · ipureintro; intro J' hc; cases hc
    · unfold tmpEnt; iempintro
  · subst h; isplitl []
    · ipureintro; intro J' hc; cases hc
    · unfold tmpEnt; iexact Ht

/-- A directory's claim merged from its `.only [b]` and `.except [b]` parts: each name's entry is the
part's holding it. -/
theorem merged_cur (hm hT hR : NamesH) (J : Ino) (b c : GoString)
    (h1 : hm.restrict J (.only [b]) = hT.restrict J (.only [b]))
    (h2 : hm.restrict J (.except [b]) = hR.restrict J (.except [b])) :
    hm.cur !! c = if c = b then hT.cur !! c else hR.cur !! c := by
  by_cases hc : c = b
  · subst hc
    have := congrArg (fun x => x.cur !! c) h1
    simp only [NamesH.restrict] at this
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), restrictN_lookup _ _ _ (by simp [NameSet.Mem])] at this
    simp [this]
  · have := congrArg (fun x => x.cur !! c) h2
    simp only [NamesH.restrict] at this
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem, hc]), restrictN_lookup _ _ _ (by simp [NameSet.Mem, hc])] at this
    simp [hc, this]

end proof

end EtcdGrove
end Perennial
