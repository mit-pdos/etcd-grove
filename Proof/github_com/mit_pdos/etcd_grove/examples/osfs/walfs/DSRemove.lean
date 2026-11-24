/-
`os.Remove` and `os.Mkdir` over whole claims, whatever the name holds (walfs-local; `Create` removes
`wal.tmp/seg` and `wal.tmp`, then makes `wal.tmp`, without knowing what is there).

* `wp_rmAny`: `os.Remove(d/b)` with the whole claim on `b` and, if `b` names a directory, its whole
  `.except []` claim (`subRes`): the name gone, or the claim as it was and an error. Absent: `unlink` and `rmdir`
  fail (`wp_osUnlinkS_none`, `wp_osRmdirS_none`). A file: the `unlink` (`wp_osUnlinkS`). An empty
  directory: `unlink` fails, the `rmdir` (`wp_osRmdirS`). A non-empty one: both fail
  (`wp_osRmdirS_nonempty`).
* `wp_rmNoDir`: `os.Remove(d/b/c)`, `d/b` no directory: an error, no effect (`DSOps.lean`).
* `wp_mkAny`: `os.Mkdir(d/b)` with the whole claim on `b`: a new, empty directory there with its
  whole claim (`wp_osMkdirS`), or an error with the claim as it was (`wp_osMkdirS_some` when `b`
  holds something).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSOps
public import Spec.os.Remove
public import Spec.os.Mkdir
public import Proof.os.RemoveAllExt
public import Proof.os.MkdirParts
public import Proof.os.IgnoringEINTR

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- What `os.Remove` of `b` needs beyond the claim on `b`: the whole claim of the directory `b`
names, if it names one. -/
def subRes (b : GoString) (h : NamesH) : IProp GF :=
  match h.cur !! b with
  | some (.dir J) => iprop(∃ hJ, osNames (L := L) J (.except []) (DFrac.own 1) hJ)
  | _ => iprop(emp)

theorem subRes_none {b : GoString} {h : NamesH} (hn : h.cur !! b = none) :
    ⊢ subRes (L := L) b h := by
  unfold subRes; rw [hn]; iempintro

variable {s : Stuckness} {E : CoPset}

/-- **`rmdir(2)` of `d/b`, a directory `J` holding the name `c`**, with a fraction of the claim on
`b` (not a spine to `d/b`) and of a claim on names `N ∋ c` of `J`: an errno, no effect. -/
theorem wp_osRmdirS_nonempty' (R : Roots) (d b : GoString) (j J : Ino) (N : NameSet)
    (dq dqb dqn : DFrac) (h hJ : NamesH) (c : GoString) (k s0 : Nat) (q : Qp) (hb : NameOk b)
    (hcb : h.cur !! b = some (.dir J)) (hN : N.Mem c) (hc : (hJ.cur !! c).isSome)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqb h -∗
      osNames (L := L) J N dqn hJ -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqb h -∗ osNames (L := L) J N dqn hJ -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  let P : OsState → Prop := fun st => PathNames st d j (.only [b]) h ∧
    ∀ x, N.Mem x → st.tree.entry J x = hJ.cur !! x
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d b) → P st →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some (s0, child d b) → P st →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨J', -, -, ⟨hl, hempty⟩, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp.1 hb (by simp [NameSet.Mem]), hcb] at hl
      cases hl
      have := hempty c
      rw [hp.2 c hN] at this
      rw [this] at hc; exact absurd hc (by simp)
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  have hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
        iprop((osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqb h) ∗
          osNames (L := L) J N dqn hJ) -∗ ⌜P st⌝ := by
    intro st Γn hR hcoh
    iintro HA ⟨Hpb, Hn⟩
    icases pathNames_of R d dq j _ dqb h st Γn hR hcoh $$ HA Hpb with %h1
    icases osNames_entry hcoh J N dqn hJ $$ HA Hn with %h3
    ipureintro; exact ⟨h1, h3⟩
  iintro #Hinv #Hsi Hp Hb Hn Hk HΦ
  iapply wp_callEndS "Rmdir" _ (by simp [val.isPanic]) R k s0 (child d b) q
    iprop((osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqb h) ∗
      osNames (L := L) J N dqn hJ)
    P (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e) hF hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hb Hn] Hk
  · iframe
  iintro %w %hW Hq ⟨⟨Hp, Hb⟩, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  icases osPathS_callKey R d dq j $$ Hp with ⟨Hp, %hk⟩
  iapply HΦ $$ %e %he [Hq] Hp Hb Hn
  iapply osCallPerm_congr q (hk b) $$ Hq

end res

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `subRes` of a name holding no directory: nothing. -/
theorem subRes_nodir {b : GoString} {h : NamesH} (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
    ⊢ subRes (GF := GF) b h := by
  unfold subRes
  split
  · exact absurd ‹_› (hnd _)
  · iempintro

/-- One attempt of `os.Remove`'s `syscall.Unlink(p)` or `syscall.Rmdir(p)`: the stub `fn`
(`fsUnlink`, `fsRmdir`: `CallBegin`, the extension's step), from `I`, gives `I` back on `EINTR` and
`Ψ e` on any other errno. -/
def rmAttempt (fn p : GoString) (I : IProp GF) (Ψ : w64 → IProp GF) : IProp GF :=
  iprop(∀ Φ : val → IProp GF, I -∗
    (∀ e : w64, ((⌜e = W64 4⌝ ∗ I) ∨ (⌜e ≠ W64 4⌝ ∗ Ψ e)) -∗ Φ #e) -∗
    WP (App (Val (@! fn)) (Val #p)) {{ Φ }})

/-- **`os.Remove(p)`** (Go's: `ignoringEINTR` around `syscall.Unlink(p)`, then for an error
`ignoringEINTR` around `syscall.Rmdir(p)` and `&PathError{"remove", p, e}`), for any per-attempt
resources (`rmAttempt`): the unlink's errno `e` gives `nil` (0) or the rmdir loop, whose errno `e1`
gives `nil` (0) or an error. -/
theorem wp_RemoveG (p : GoString) (I : IProp GF) (U : w64 → IProp GF) (Q : GoInterface → IProp GF) :
    {{ I ∗ □ rmAttempt syscall.fsUnlink p I U ∗
        (∀ e : w64, ⌜e ≠ W64 4⌝ -∗ U e -∗
          ((⌜e = 0⌝ -∗ Q interface.nil) ∧
           (⌜e ≠ 0⌝ -∗ ∃ (J : IProp GF) (Rm : w64 → IProp GF), J ∗ □ rmAttempt syscall.fsRmdir p J Rm ∗
             ∀ e1 : w64, ⌜e1 ≠ W64 4⌝ -∗ Rm e1 -∗
               ((⌜e1 = 0⌝ -∗ Q interface.nil) ∧
                ∀ err : GoInterface, ⌜err ≠ interface.nil⌝ -∗ Q err)))) }}
      (App (Val (@! os.Remove)) (Val #p))
    {{ (err : GoInterface), RET #err; Q err }} := by
  wp_start as ⟨HI, #Hu, HK⟩
  try wp_auto
  rw [recv_eq_func_mk]
  -- the unlink loop
  wp_apply (os.wp_ignoringEINTR _ iprop(name_ptr ↦ p ∗ I)
    (fun e => iprop(⌜e ≠ W64 4⌝ ∗ name_ptr ↦ p ∗ U e))) $$ [name HI] as %e ⟨%he4, Hname, HU⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, HI⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    wp_func_call; wp_call
    try wp_auto
    iunfold rmAttempt at Hu
    wp_apply Hu $$ HI as %e' Hr
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ'
    icases Hr with (⟨%he, HI⟩ | ⟨%he, HU⟩)
    · ileft; iframe; ipureintro; exact he
    · iright; (try dsimp only); iframe; ipureintro; exact ⟨he, he⟩
  ihave HK := HK $$ %e %he4 HU
  by_cases h0 : e = 0
  · subst h0
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    icases HK with ⟨HK, -⟩
    iapply HΦ
    iapply HK
    (try ipureintro)
    (try rfl)
    (try trivial)
  simp only [errnoErr, h0, ↓reduceIte]
  try wp_auto
  icases HK with ⟨-, HK⟩
  ispecialize HK $$ %h0
  icases HK with ⟨%J, %Rm, HJ, #Hr, HK⟩
  rw [recv_eq_func_mk]
  -- the rmdir loop
  wp_apply (os.wp_ignoringEINTR _ iprop(name_ptr ↦ p ∗ J)
    (fun e1 => iprop(⌜e1 ≠ W64 4⌝ ∗ name_ptr ↦ p ∗ Rm e1))) $$ [Hname HJ] as %e1 ⟨%he14, Hname, HR⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, HJ⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    wp_func_call; wp_call
    try wp_auto
    iunfold rmAttempt at Hr
    wp_apply Hr $$ HJ as %e' Hr'
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ'
    icases Hr' with (⟨%he, HJ⟩ | ⟨%he, HR⟩)
    · ileft; iframe; ipureintro; exact he
    · iright; (try dsimp only); iframe; ipureintro; exact ⟨he, he⟩
  ihave HK := HK $$ %e1 %he14 HR
  by_cases h10 : e1 = 0
  · subst h10
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    icases HK with ⟨HK, -⟩
    iapply HΦ
    iapply HK
    (try ipureintro)
    (try rfl)
    (try trivial)
  simp only [errnoErr, h10, ↓reduceIte]
  try wp_auto
  icases HK with ⟨-, HK⟩
  by_cases h20 : e1 = W64 20
  · subst h20
    try simp only [decide_true, Bool.not_true]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    iapply HK
    ipureintro; intro hc; cases hc
  · try simp only [decide_eq_false h20, Bool.not_false]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    iapply HK
    ipureintro; intro hc; cases hc

/-- `wp_rmAny`'s result: `b` gone, or as it was (`h`) and an error. -/
def rmQ (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (err : GoInterface) :
    IProp GF :=
  iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
    ∃ h', osNames j (.only [b]) (DFrac.own 1) h' ∗ subRes (GF := GF) b h' ∗
      ⌜(h' = h ∧ err ≠ interface.nil) ∨ h'.cur !! b = none⌝)

/-- `os.Remove`'s rmdir loop on `d/b` holding no directory in the claim `h1` (each attempt failing,
no effect): `rmQ` for `h1` as it was or with `b` absent. -/
theorem rmdir_tail (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h h1 : NamesH) (hb : NameOk b)
    (hnd : ∀ J, h1.cur !! b ≠ some (.dir J)) (hfin : h1 = h ∨ h1.cur !! b = none) :
    ⊢ osInv (GF := GF) -∗ osSharedInv R -∗ osLogLb h.next -∗
      osPathS R d dq j -∗ osCallPerm (callKey R d) 1 -∗ osNames j (.only [b]) (DFrac.own 1) h1 -∗
      ∃ (J : IProp GF) (Rm : w64 → IProp GF), J ∗ □ rmAttempt syscall.fsRmdir (child d b) J Rm ∗
        ∀ e1 : w64, ⌜e1 ≠ W64 4⌝ -∗ Rm e1 -∗
          ((⌜e1 = 0⌝ -∗ rmQ R d b j dq h interface.nil) ∧
           ∀ err : GoInterface, ⌜err ≠ interface.nil⌝ -∗ rmQ R d b j dq h err) := by
  iintro #Hos #Hsi #Hlb Hp Hperm Hn
  iexists iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗ osNames j (.only [b]) (DFrac.own 1) h1),
    (fun e1 => iprop(⌜e1 ≠ 0⌝ ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
      osNames j (.only [b]) (DFrac.own 1) h1))
  isplitl [Hp Hperm Hn]
  · iframe
  isplitl []
  · iintro !>
    unfold rmAttempt
    iintro %Φ' ⟨Hp, Hperm, Hn⟩ HΦ'
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsRmdir.impl
    wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
    iclear Hls1
    wp_apply +noauto wp_osRmdirS_none R d b j dq (DFrac.own 1) h1 t1 s1 1 hb hnd
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
    iapply HΦ'
    by_cases he4 : e1 = W64 4
    · ileft; iframe; ipureintro; exact he4
    · iright; (try dsimp only); iframe; ipureintro; exact ⟨he4, he1⟩
  iintro %e1 %he4 ⟨%he1, Hp, Hperm, Hn⟩
  isplit
  · iintro %h0; exact absurd h0 he1
  · iintro %err %hne
    unfold rmQ
    iframe Hp Hperm
    iexists h1
    iframe Hn
    isplitl []
    · iapply (subRes_nodir hnd)
    ipureintro
    rcases hfin with rfl | hn
    · exact .inl ⟨rfl, hne⟩
    · exact .inr hn

/-- **`os.Remove(d/b)`** with the whole claim on `b` (and `subRes`): `b` gone, or as it was and an
error. -/
theorem wp_rmAny (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ subRes (GF := GF) b h }}
      (App (Val (@! os.Remove)) (Val #(child d b)))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        ∃ h', osNames j (.only [b]) (DFrac.own 1) h' ∗ subRes (GF := GF) b h' ∗
          ⌜(h' = h ∧ err ≠ interface.nil) ∨ h'.cur !! b = none⌝ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start_folded as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hsub⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  cases hcb : h.cur !! b with
  | none =>
    iclear Hsub
    wp_apply (wp_RemoveG (child d b)
      iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗ osNames j (.only [b]) (DFrac.own 1) h)
      (fun e => iprop(⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [b]) (DFrac.own 1) h))
      (rmQ R d b j dq h)) $$ [Hp Hperm Hn] as %err HQ
    · iframe
      isplitl []
      · iintro !>
        unfold rmAttempt
        iintro %Φ' ⟨Hp, Hperm, Hn⟩ HΦ'
        icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
        wp_stub syscall.fsUnlink.impl
        wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
        iclear Hls
        wp_apply +noauto wp_osUnlinkS_none R d b j dq (DFrac.own 1) h t s0 1 hb
          (fun i hi => by simp [hcb] at hi) CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
        iapply HΦ'
        by_cases he4 : e = W64 4
        · ileft; iframe; ipureintro; exact he4
        · iright; (try dsimp only); iframe; ipureintro; exact ⟨he4, he⟩
      iintro %e %he4 ⟨%he0, Hp, Hperm, Hn⟩
      isplit
      · iintro %h0; exact absurd h0 he0
      · iintro %_
        iapply (rmdir_tail R d b j dq h h hb (fun J hJ => by simp [hcb] at hJ) (.inl rfl))
          $$ Hos Hsi Hlb Hp Hperm Hn
    iapply HΦ
    iunfold rmQ at HQ
    first | iexact HQ | (iunfold subRes at HQ; iexact HQ)
  | some n =>
  cases n with
  | file i =>
    iclear Hsub
    have habs : ∀ x s, (h.log x (⟨.remove j b (.file i), s⟩ : LogEntry)
        (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
      intro x s; simp only [NamesH.log]
      rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
    wp_apply (wp_RemoveG (child d b)
      iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        (osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∨
          ∃ h1 : NamesH, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗ ⌜h1.cur !! b = none⌝))
      (fun e => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        ∃ h1 : NamesH, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗
          ⌜(h1 = h ∨ h1.cur !! b = none) ∧ (∀ J, h1.cur !! b ≠ some (.dir J)) ∧
            (e = 0 → h1.cur !! b = none)⌝))
      (rmQ R d b j dq h)) $$ [Hp Hperm Hn] as %err HQ
    · iframe Hp Hperm
      isplitl [Hn]
      · ileft; iexact Hn
      isplitl []
      · iintro !>
        unfold rmAttempt
        iintro %Φ' ⟨Hp, Hperm, HSt⟩ HΦ'
        icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
        wp_stub syscall.fsUnlink.impl
        wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
        iclear Hls
        icases HSt with (Hn | ⟨%h1, Hn, %hn1⟩)
        · wp_apply +noauto wp_osUnlinkS R d b j i dq h t s0 1 hb hcb hs CoPset.subseteq_top
            CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e Hperm Hp Hres
          iapply HΦ'
          unfold osNamesAfter
          icases Hres with (⟨%he, Hn⟩ | ⟨%x, -, Hn⟩)
          · by_cases he4 : e = W64 4
            · ileft
              isplitr
              · ipureintro; exact he4
              iframe Hp Hperm
              ileft; iexact Hn
            · iright; (try dsimp only)
              isplitr
              · ipureintro; exact he4
              iframe Hp Hperm
              iexists h
              iframe Hn
              ipureintro
              exact ⟨.inl rfl, (fun J hJ => by simp [hcb] at hJ), fun h0 => absurd h0 he⟩
          · by_cases he4 : e = W64 4
            · ileft
              isplitr
              · ipureintro; exact he4
              iframe Hp Hperm
              iright; iexists _; iframe Hn; ipureintro; exact habs _ _
            · iright; (try dsimp only)
              isplitr
              · ipureintro; exact he4
              iframe Hp Hperm
              iexists _
              iframe Hn
              ipureintro
              exact ⟨.inr (habs _ _), (fun J hJ => by simp [habs] at hJ), fun _ => habs _ _⟩
        · wp_apply +noauto wp_osUnlinkS_none R d b j dq (DFrac.own 1) h1 t s0 1 hb
            (fun i hi => by simp [hn1] at hi) CoPset.subseteq_top CoPset.subseteq_top
            $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
          iapply HΦ'
          by_cases he4 : e = W64 4
          · ileft
            isplitr
            · ipureintro; exact he4
            iframe Hp Hperm
            iright; iexists h1; iframe Hn; ipureintro; exact hn1
          · iright; (try dsimp only)
            isplitr
            · ipureintro; exact he4
            iframe Hp Hperm
            iexists h1
            iframe Hn
            ipureintro
            exact ⟨.inr hn1, (fun J hJ => by simp [hn1] at hJ), fun _ => hn1⟩
      iintro %e %he4 ⟨Hp, Hperm, %h1, Hn, %hh1⟩
      obtain ⟨hfin, hnd, h0e⟩ := hh1
      isplit
      · iintro %h0
        unfold rmQ
        iframe Hp Hperm
        iexists h1
        iframe Hn
        isplitl []
        · iapply (subRes_nodir hnd)
        ipureintro; exact .inr (h0e h0)
      · iintro %_
        iapply (rmdir_tail R d b j dq h h1 hb hnd hfin) $$ Hos Hsi Hlb Hp Hperm Hn
    iapply HΦ
    iunfold rmQ at HQ
    first | iexact HQ | (iunfold subRes at HQ; iexact HQ)
  | dir J =>
    unfold subRes
    rw [hcb]
    icases Hsub with ⟨%hJ, HJ⟩
    have habs : ∀ x s, (h.log x (⟨.remove j b (.dir J), s⟩ : LogEntry)
        (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
      intro x s; simp only [NamesH.log]
      rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
    wp_apply (wp_RemoveG (child d b)
      iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
        osNames J (.except []) (DFrac.own 1) hJ)
      (fun e => iprop(⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ))
      (rmQ R d b j dq h)) $$ [Hp Hperm Hn HJ] as %err HQ
    · iframe
      isplitl []
      · iintro !>
        unfold rmAttempt
        iintro %Φ' ⟨Hp, Hperm, Hn, HJ⟩ HΦ'
        icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
        wp_stub syscall.fsUnlink.impl
        wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
        iclear Hls
        wp_apply +noauto wp_osUnlinkS_none R d b j dq (DFrac.own 1) h t s0 1 hb
          (fun i hi => by simp [hcb] at hi) CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
        iapply HΦ'
        by_cases he4 : e = W64 4
        · ileft; iframe; ipureintro; exact he4
        · iright; (try dsimp only); iframe; ipureintro; exact ⟨he4, he⟩
      iintro %e %he4 ⟨%he0, Hp, Hperm, Hn, HJ⟩
      isplit
      · iintro %h0; exact absurd h0 he0
      iintro %_
      -- the rmdir loop: the claim (and `J`'s) as it was, or the name gone
      iexists iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
          ((osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗
              osNames (GF := GF) J (.except []) (DFrac.own 1) hJ) ∨
            ∃ h1 : NamesH, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗ ⌜h1.cur !! b = none⌝)),
        (fun e1 => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
          ∃ h1, osNames j (.only [b]) (DFrac.own 1) h1 ∗ subRes (GF := GF) b h1 ∗
            ⌜(h1 = h ∧ e1 ≠ 0) ∨ h1.cur !! b = none⌝))
      isplitl [Hp Hperm Hn HJ]
      · iframe Hp Hperm; ileft; iframe
      isplitl []
      · iintro !>
        unfold rmAttempt
        iintro %Φ' ⟨Hp, Hperm, HSt⟩ HΦ'
        icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
        wp_stub syscall.fsRmdir.impl
        wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
        iclear Hls1
        icases HSt with (⟨Hn, HJ⟩ | ⟨%h1, Hn, %hn1⟩)
        · by_cases hem : hJ.cur = ∅
          · wp_apply +noauto wp_osRmdirS R d b j J dq h hJ t1 s1 hb hcb hem CoPset.subseteq_top
              CoPset.subseteq_top $$ Hos Hsi Hp Hn HJ Hk1 as %e1 Hperm Hp HJ Hres
            iapply HΦ'
            unfold osNamesAfter
            icases Hres with (⟨%he1, Hn⟩ | ⟨%x, -, Hn⟩)
            · by_cases he14 : e1 = W64 4
              · ileft
                isplitr
                · ipureintro; exact he14
                iframe Hp Hperm
                ileft; iframe
              · iright; (try dsimp only)
                isplitr
                · ipureintro; exact he14
                iframe Hp Hperm
                iexists h
                iframe Hn
                isplitl [HJ]
                · (try unfold subRes); simp only [hcb]; iexists hJ; iexact HJ
                ipureintro; exact .inl ⟨rfl, he1⟩
            · iclear HJ
              by_cases he14 : e1 = W64 4
              · ileft
                isplitr
                · ipureintro; exact he14
                iframe Hp Hperm
                iright; iexists _; iframe Hn; ipureintro; exact habs _ _
              · iright; (try dsimp only)
                isplitr
                · ipureintro; exact he14
                iframe Hp Hperm
                iexists _
                iframe Hn
                isplitl []
                · first | iapply subRes_none (habs _ _) | (simp only [habs _ _]; iempintro)
                ipureintro; exact .inr (habs _ _)
          · obtain ⟨c, hc⟩ : ∃ c, (hJ.cur !! c).isSome := by
              refine Classical.byContradiction fun hno => hem ?_
              apply GMap.ext; intro c
              cases hx : hJ.cur !! c with
              | none => simp
              | some _ => exact absurd ⟨c, by simp [hx]⟩ hno
            wp_apply +noauto wp_osRmdirS_nonempty' R d b j J (.except []) dq (DFrac.own 1)
              (DFrac.own 1) h hJ c t1 s1 1 hb hcb (by simp [NameSet.Mem]) hc CoPset.subseteq_top
              CoPset.subseteq_top $$ Hos Hsi Hp Hn HJ Hk1 as %e1 %he1 Hperm Hp Hn HJ
            iapply HΦ'
            by_cases he14 : e1 = W64 4
            · ileft
              isplitr
              · ipureintro; exact he14
              iframe Hp Hperm
              ileft; iframe
            · iright; (try dsimp only)
              isplitr
              · ipureintro; exact he14
              iframe Hp Hperm
              iexists h
              iframe Hn
              isplitl [HJ]
              · (try unfold subRes); simp only [hcb]; iexists hJ; iexact HJ
              ipureintro; exact .inl ⟨rfl, he1⟩
        · wp_apply +noauto wp_osRmdirS_none R d b j dq (DFrac.own 1) h1 t1 s1 1 hb
            (fun J' hJ' => by simp [hn1] at hJ') CoPset.subseteq_top CoPset.subseteq_top
            $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
          iapply HΦ'
          by_cases he14 : e1 = W64 4
          · ileft
            isplitr
            · ipureintro; exact he14
            iframe Hp Hperm
            iright; iexists h1; iframe Hn; ipureintro; exact hn1
          · iright; (try dsimp only)
            isplitr
            · ipureintro; exact he14
            iframe Hp Hperm
            iexists h1
            iframe Hn
            isplitl []
            · first | iapply subRes_none hn1 | (simp only [hn1]; iempintro)
            ipureintro; exact .inr hn1
      iintro %e1 %he14 ⟨Hp, Hperm, %h1, Hn, Hs, %hh1⟩
      isplit
      · iintro %h0
        unfold rmQ
        iframe Hp Hperm
        iexists h1
        iframe Hn Hs
        ipureintro
        rcases hh1 with ⟨-, hne⟩ | hn
        · exact absurd h0 hne
        · exact .inr hn
      · iintro %err %hne
        unfold rmQ
        iframe Hp Hperm
        iexists h1
        iframe Hn Hs
        ipureintro
        rcases hh1 with ⟨rfl, -⟩ | hn
        · exact .inl ⟨rfl, hne⟩
        · exact .inr hn
    iapply HΦ
    iunfold rmQ at HQ
    first | iexact HQ | (iunfold subRes at HQ; iexact HQ)

/-- **`os.Remove(d/b/c)`, `d/b` no directory** (a fraction of the claim on `b`): an error, no
effect. -/
theorem wp_rmNoDir (R : Roots) (d b c : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hb : NameOk b) (hc : NameOk c) (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j (.only [b]) dqn h }}
      (App (Val (@! os.Remove)) (Val #(child (child d b) c)))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j (.only [b]) dqn h }} := by
  wp_start_folded as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  imod osLogLb_0 with #Hlb
  wp_apply (wp_RemoveG (child (child d b) c)
    iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) dqn h)
    (fun e => iprop(⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j (.only [b]) dqn h))
    (fun _ => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) dqn h)))
    $$ [Hp Hperm Hn] as %err HQ
  · iframe
    isplitl []
    · iintro !>
      unfold rmAttempt
      iintro %Φ' ⟨Hp, Hperm, Hn⟩ HΦ'
      icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
      ihave Hperm := osCallPerm_congr qc (hk b c).symm $$ Hperm
      wp_stub syscall.fsUnlink.impl
      wp_apply +noauto wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
      iclear Hls
      wp_apply +noauto wp_osUnlinkS_noDir R d b c j dq dqn h t s0 qc hb hc hnd CoPset.subseteq_top
        CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
      iapply HΦ'
      by_cases he4 : e = W64 4
      · ileft; iframe; ipureintro; exact he4
      · iright; (try dsimp only); iframe; ipureintro; exact ⟨he4, he⟩
    iintro %e %he4 ⟨%he0, Hp, Hperm, Hn⟩
    isplit
    · iintro %h0; exact absurd h0 he0
    iintro %_
    iexists iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) dqn h),
      (fun e1 => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) dqn h))
    isplitl [Hp Hperm Hn]
    · iframe
    isplitl []
    · iintro !>
      unfold rmAttempt
      iintro %Φ' ⟨Hp, Hperm, Hn⟩ HΦ'
      icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
      ihave Hperm := osCallPerm_congr qc (hk b c).symm $$ Hperm
      wp_stub syscall.fsRmdir.impl
      wp_apply +noauto wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
      iclear Hls1
      wp_apply +noauto wp_osRmdirS_noDir R d b c j dq dqn h t1 s1 qc hb hc hnd CoPset.subseteq_top
        CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
      iapply HΦ'
      by_cases he14 : e1 = W64 4
      · ileft; iframe; ipureintro; exact he14
      · iright; (try dsimp only); iframe; ipureintro; exact he14
    iintro %e1 %he14 HR
    isplit
    · iintro %_; iexact HR
    · iintro %err %_; iexact HR
  iapply HΦ
  iexact HQ

/-- **`os.Mkdir(d/b)`** with the whole claim on `b`: an error and the claim as it was, or a new,
empty directory there with its whole claim (the error then either). -/
theorem wp_mkAny (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (perm : w32)
    (hb : NameOk b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗
        osCallPerm (callKey R d) 1 ∗ osNames j (.only [b]) (DFrac.own 1) h }}
      (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        ∃ h', osNames j (.only [b]) (DFrac.own 1) h' ∗
          (⌜h' = h ∧ err ≠ interface.nil⌝ ∨ ∃ J hJ, ⌜h'.cur !! b = some (.dir J) ∧ hJ.cur = ∅⌝ ∗
            osNames J (.except []) (DFrac.own 1) hJ) }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start_folded as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  cases hcb : h.cur !! b with
  | some n =>
    have hsome : (h.cur !! b).isSome := by rw [hcb]; rfl
    wp_apply os.Mkdir.wp_takenS d b perm R j (.only [b]) dq (DFrac.own 1) h 1 hb hbN hsome
      $$ [Hp Hn Hperm] as %err ⟨Hp, Hn, Hperm, %hne, -⟩
    · iframe; iframe #
    iapply HΦ
    iframe Hp Hperm
    iexists h
    iframe Hn
    ileft; ipureintro; exact ⟨rfl, hne⟩
  | none =>
  imod osLogLb_0 with #Hlb
  icases osPathS_pathIn_keep R d dq j $$ Hp with ⟨%hpd, Hp⟩
  have hpin : PathIn R (child d b) := pathIn_child hpd.2 hb
  have htn : RootsTreeName R (child d b) := os.treeName_child hpd.2 hb
  wp_apply (os.Mkdir.wp_tree R (child d b) perm
    iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
      (osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∨
        ∃ h1 J hJ, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗
          ⌜h1.cur !! b = some (.dir J) ∧ hJ.cur = ∅⌝ ∗ osNames (GF := GF) J (.except []) (DFrac.own 1) hJ))
    (fun e => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
      ∃ h', osNames j (.only [b]) (DFrac.own 1) h' ∗
        (⌜h' = h ∧ e ≠ 0⌝ ∨ ∃ J hJ, ⌜h'.cur !! b = some (.dir J) ∧ hJ.cur = ∅⌝ ∗
          osNames J (.except []) (DFrac.own 1) hJ)))
    hpin htn) $$ [Hp Hperm Hn] as %err ⟨-, %e, ⟨Hp, Hperm, %h', Hn, Hr⟩, %he⟩
  · iframe Hsys Hos Hsi Hp Hperm
    isplitl [Hn]
    · ileft; iexact Hn
    iintro !>
    unfold os.mkdirAttempt
    iintro %m %Φ' ⟨Hp, Hperm, HSt⟩ HΦ'
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsMkdir.impl
    wp_apply +noauto wp_osCallBeginS R _ 1 0 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    icases HSt with (Hn | ⟨%h1, %J, %hJ, Hn, %hJ1, HJ⟩)
    · wp_apply +noauto wp_osMkdirS R d b j dq h t s0 hb hcb CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hp Hn Hk as %e Hperm Hp Hres
      iapply HΦ'
      icases Hres with (⟨%he, Hn⟩ | ⟨%x, %J, -, Hn, %hJ, HJ, %hJ'⟩)
      · by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe Hp Hperm
          ileft; iexact Hn
        · iright; (try dsimp only)
          isplitr
          · ipureintro; exact he4
          iframe Hp Hperm
          iexists h
          iframe Hn
          ileft; ipureintro; exact ⟨rfl, he⟩
      · have hd : (h.log x (⟨.mkdir j b J, s0⟩ : LogEntry) (<[b := .dir J]> h.cur)).cur !! b =
            some (.dir J) := by simp only [NamesH.log]; rw [GMap.lookup_insert]
        by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe Hp Hperm
          iright; iexists _, J, hJ; iframe Hn HJ; ipureintro; exact ⟨hd, hJ'.1⟩
        · iright; (try dsimp only)
          isplitr
          · ipureintro; exact he4
          iframe Hp Hperm
          iexists _
          iframe Hn
          iright; iexists J, hJ; iframe HJ; ipureintro; exact ⟨hd, hJ'.1⟩
    · have hsome : (h1.cur !! b).isSome := by rw [hJ1.1]; rfl
      wp_apply +noauto wp_osMkdirS_some R d b j (.only [b]) dq (DFrac.own 1) h1 t s0 1 hb hbN hsome
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
      iapply HΦ'
      by_cases he4 : e = W64 4
      · ileft
        isplitr
        · ipureintro; exact he4
        iframe Hp Hperm
        iright; iexists h1, J, hJ; iframe Hn HJ; ipureintro; exact hJ1
      · iright; (try dsimp only)
        isplitr
        · ipureintro; exact he4
        iframe Hp Hperm
        iexists h1
        iframe Hn
        iright; iexists J, hJ; iframe HJ; ipureintro; exact hJ1
  iapply HΦ
  iframe Hp Hperm
  iexists h'
  iframe Hn
  icases Hr with (%hr | HR)
  · ileft; ipureintro
    refine ⟨hr.1, fun hc => hr.2 (he.2.1 hc)⟩
  · iright; iexact HR

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
