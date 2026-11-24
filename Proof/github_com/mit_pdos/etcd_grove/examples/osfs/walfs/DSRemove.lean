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

set_option hygiene false in
/-- `Remove`'s `rmdir(2)` loop on a name holding no directory in the claim `hc` (`Hn`): each
attempt a nonzero errno with no effect, `EINTR` retried; then `post` after `iapply HΦ`. -/
local macro "rmdir_none_loop" hc:term ", " hnd:term " => " post:tacticSeq : tactic => `(tactic| (
  iloeb as IH2 generalizing Hperm Hp Hn
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub os.fsRmdir.impl
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  -- PORT: which stub? (RmdirS)
  wp_apply wp_osRmdirS_none R d b j dq (DFrac.own 1) $hc t1 s1 1 hb $hnd CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    try wp_auto
    iapply IH2 $$ Hperm Hp Hn HΦ
    all_goals iframe
  rw [decide_eq_false he14]
  try wp_auto
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  try wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)
  · rw [decide_eq_false h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)))

set_option hygiene false in
/-- The error after `Remove`'s `rmdir` loop failed with `e1` (`he1`). -/
local macro "rm_err" " => " post:tacticSeq : tactic => `(tactic| (
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  try wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)
  · rw [decide_eq_false h20]
    try wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)))

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
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hsub⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  cases hcb : h.cur !! b with
  | none =>
    iclear Hsub
    iloeb as IH generalizing Hperm Hp Hn
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    try wp_auto
    wp_stub os.fsUnlink.impl
    wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    -- PORT: which stub? (UnlinkS)
    wp_apply wp_osUnlinkS_none R d b j dq (DFrac.own 1) h t s0 1 hb (fun i hi => by simp [hcb] at hi)
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      iapply IH $$ Hperm Hp Hn HΦ
    rw [decide_eq_false he4]
    try wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    rmdir_none_loop h, (fun J hJ => by simp [hcb] at hJ) =>
      iframe Hp Hperm
      iexists h
      iframe Hn
      isplitl []
      · first | iapply subRes_none hcb | (simp only [hcb]; iempintro)
      ipureintro; exact .inl ⟨rfl, fun h => by cases h⟩
  | some n =>
  cases n with
  | file i =>
    iclear Hsub
    have habs : ∀ x s, (h.log x (⟨.remove j b (.file i), s⟩ : LogEntry)
        (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
      intro x s; simp only [NamesH.log]
      rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
    -- the unlink loop: the claim as it was, or with the name gone
    ihave HSt : iprop(osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∨
        ∃ h1 : NamesH, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗ ⌜h1.cur !! b = none⌝)
      $$ [Hn]
    · ileft; iexact Hn
    iloeb as IH generalizing Hperm Hp HSt
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    try wp_auto
    wp_stub os.fsUnlink.impl
    wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    icases HSt with (Hn | ⟨%h1, Hn, %hn1⟩)
    · wp_apply wp_osUnlinkS R d b j i dq h t s0 1 hb hcb hs CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hp Hn Hk as %e Hperm Hp Hres
      unfold osNamesAfter
      icases Hres with (⟨%he, Hn⟩ | ⟨%x, -, Hn⟩)
      · by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          try wp_auto
          iapply IH $$ Hperm Hp [Hn] HΦ
          ileft; iexact Hn
        rw [decide_eq_false he4]
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he)]
        try wp_auto
        rmdir_none_loop h, (fun J hJ => by simp [hcb] at hJ) =>
          iframe Hp Hperm
          iexists h
          iframe Hn
          isplitl []
          · (try unfold subRes); simp only [hcb]; iempintro
          ipureintro; exact .inl ⟨rfl, fun h => by cases h⟩
      · by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          try wp_auto
          iapply IH $$ Hperm Hp [Hn] HΦ
          iright; iexists _; iframe Hn; ipureintro; exact habs _ _
        rw [decide_eq_false he4]
        try wp_auto
        by_cases he0 : e = W64 0
        · rw [decide_eq_true he0]
          try wp_auto
          iapply HΦ
          iframe Hp Hperm
          iexists _
          iframe Hn
          isplitl []
          · first | iapply subRes_none (habs _ _) | (simp only [habs _ _]; iempintro)
          ipureintro; exact .inr (habs _ _)
        rw [decide_eq_false he0]
        try wp_auto
        rmdir_none_loop (h.log x (⟨.remove j b (.file i), s0⟩ : LogEntry)
            (restrictN (.only [b]) (GMap.delete b h.cur))), (fun J hJ => by simp [habs] at hJ) =>
          iframe Hp Hperm
          iexists _
          iframe Hn
          isplitl []
          · first | iapply subRes_none (habs _ _) | (simp only [habs _ _]; iempintro)
          ipureintro; exact .inr (habs _ _)
    · wp_apply wp_osUnlinkS_none R d b j dq (DFrac.own 1) h1 t s0 1 hb
        (fun i hi => by simp [hn1] at hi) CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ Hperm Hp [Hn] HΦ
        iright; iexists h1; iframe Hn; ipureintro; exact hn1
      rw [decide_eq_false he4]
      try wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he)]
      try wp_auto
      rmdir_none_loop h1, (fun J hJ => by simp [hn1] at hJ) =>
        iframe Hp Hperm
        iexists h1
        iframe Hn
        isplitl []
        · first | iapply subRes_none hn1 | (simp only [hn1]; iempintro)
        ipureintro; exact .inr hn1
  | dir J =>
    unfold subRes
    rw [hcb]
    icases Hsub with ⟨%hJ, HJ⟩
    -- the unlink loop: no effect
    iloeb as IH generalizing Hperm Hp Hn HJ
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    try wp_auto
    wp_stub os.fsUnlink.impl
    wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    -- PORT: which stub? (UnlinkS)
    wp_apply wp_osUnlinkS_none R d b j dq (DFrac.own 1) h t s0 1 hb (fun i hi => by simp [hcb] at hi)
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      iapply IH $$ Hperm Hp Hn HJ HΦ
    rw [decide_eq_false he4]
    try wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    iclear IH
    have habs : ∀ x s, (h.log x (⟨.remove j b (.dir J), s⟩ : LogEntry)
        (restrictN (.only [b]) (GMap.delete b h.cur))).cur !! b = none := by
      intro x s; simp only [NamesH.log]
      rw [restrictN_lookup _ _ _ hbN]; exact GMap.lookup_delete _ _
    -- the rmdir loop: the claim (and `J`'s) as it was, or the name gone
    ihave HSt : iprop((osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗
          osNames (GF := GF) J (.except []) (DFrac.own 1) hJ) ∨
        ∃ h1 : NamesH, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗ ⌜h1.cur !! b = none⌝)
      $$ [Hn HJ]
    · ileft; iframe
    iloeb as IH2 generalizing Hperm Hp HSt
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    try wp_auto
    wp_stub os.fsRmdir.impl
    wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
    iclear Hls1
    icases HSt with (⟨Hn, HJ⟩ | ⟨%h1, Hn, %hn1⟩)
    · by_cases hem : hJ.cur = ∅
      · wp_apply wp_osRmdirS R d b j J dq h hJ t1 s1 hb hcb hem CoPset.subseteq_top
          CoPset.subseteq_top $$ Hos Hsi Hp Hn HJ Hk1 as %e1 Hperm Hp HJ Hres
        unfold osNamesAfter
        icases Hres with (⟨%he1, Hn⟩ | ⟨%x, -, Hn⟩)
        · by_cases he14 : e1 = W64 4
          · rw [decide_eq_true he14]
            try wp_auto
            iapply IH2 $$ Hperm Hp [Hn HJ] HΦ
            ileft; iframe
          rw [decide_eq_false he14]
          try wp_auto
          rm_err =>
            iframe Hp Hperm
            iexists h
            iframe Hn
            isplitl [HJ]
            · (try unfold subRes); simp only [hcb]; iexists hJ; iexact HJ
            ipureintro; exact .inl ⟨rfl, fun h => by cases h⟩
        · iclear HJ
          by_cases he14 : e1 = W64 4
          · rw [decide_eq_true he14]
            try wp_auto
            iapply IH2 $$ Hperm Hp [Hn] HΦ
            iright; iexists _; iframe Hn; ipureintro; exact habs _ _
          rw [decide_eq_false he14]
          try wp_auto
          by_cases he10 : e1 = W64 0
          · rw [decide_eq_true he10]
            try wp_auto
            iapply HΦ
            iframe Hp Hperm
            iexists _
            iframe Hn
            isplitl []
            · first | iapply subRes_none (habs _ _) | (simp only [habs _ _]; iempintro)
            ipureintro; exact .inr (habs _ _)
          have he1 : e1 ≠ W64 0 := he10
          rm_err =>
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
        -- PORT: which stub? (RmdirS)
        wp_apply wp_osRmdirS_nonempty' R d b j J (.except []) dq (DFrac.own 1) (DFrac.own 1) h hJ c
          t1 s1 1 hb hcb (by simp [NameSet.Mem]) hc CoPset.subseteq_top CoPset.subseteq_top
          $$ Hos Hsi Hp Hn HJ Hk1 as %e1 %he1 Hperm Hp Hn HJ
        by_cases he14 : e1 = W64 4
        · rw [decide_eq_true he14]
          try wp_auto
          iapply IH2 $$ Hperm Hp [Hn HJ] HΦ
          ileft; iframe
        rw [decide_eq_false he14]
        try wp_auto
        rm_err =>
          iframe Hp Hperm
          iexists h
          iframe Hn
          isplitl [HJ]
          · (try unfold subRes); simp only [hcb]; iexists hJ; iexact HJ
          ipureintro; exact .inl ⟨rfl, fun h => by cases h⟩
    · wp_apply wp_osRmdirS_none R d b j dq (DFrac.own 1) h1 t1 s1 1 hb
        (fun J' hJ' => by simp [hn1] at hJ') CoPset.subseteq_top CoPset.subseteq_top
        $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
      by_cases he14 : e1 = W64 4
      · rw [decide_eq_true he14]
        try wp_auto
        iapply IH2 $$ Hperm Hp [Hn] HΦ
        iright; iexists h1; iframe Hn; ipureintro; exact hn1
      rw [decide_eq_false he14]
      try wp_auto
      rm_err =>
        iframe Hp Hperm
        iexists h1
        iframe Hn
        isplitl []
        · first | iapply subRes_none hn1 | (simp only [hn1]; iempintro)
        ipureintro; exact .inr hn1

/-- **`os.Remove(d/b/c)`, `d/b` no directory** (a fraction of the claim on `b`): an error, no
effect. -/
theorem wp_rmNoDir (R : Roots) (d b c : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hb : NameOk b) (hc : NameOk c) (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j (.only [b]) dqn h }}
      (App (Val (@! os.Remove)) (Val #(child (child d b) c)))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j (.only [b]) dqn h }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn
  icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
  ihave Hperm := osCallPerm_congr qc (hk b c).symm $$ Hperm
  try wp_auto
  wp_stub os.fsUnlink.impl
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  -- PORT: which stub? (UnlinkS)
  wp_apply wp_osUnlinkS_noDir R d b c j dq dqn h t s0 qc hb hc hnd CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    try wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he4]
  try wp_auto
  rw [decide_eq_false (show e ≠ W64 0 from he)]
  try wp_auto
  iclear IH
  iloeb as IH2 generalizing Hperm Hp Hn
  icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
  ihave Hperm := osCallPerm_congr qc (hk b c).symm $$ Hperm
  try wp_auto
  wp_stub os.fsRmdir.impl
  wp_apply wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  -- PORT: which stub? (RmdirS)
  wp_apply wp_osRmdirS_noDir R d b c j dq dqn h t1 s1 qc hb hc hnd CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk1 as %e1 %he1 Hperm Hp Hn
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    try wp_auto
    iapply IH2 $$ Hperm Hp Hn HΦ
  rw [decide_eq_false he14]
  try wp_auto
  rm_err =>
    iframe

/-- **`os.Mkdir(d/b)`** with the whole claim on `b`: an error and the claim as it was, or a new,
empty directory there with its whole claim (the error then either). -/
theorem wp_mkAny (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (perm : w32)
    (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [b]) (DFrac.own 1) h }}
      (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
        ∃ h', osNames j (.only [b]) (DFrac.own 1) h' ∗
          (⌜h' = h ∧ err ≠ interface.nil⌝ ∨ ∃ J hJ, ⌜h'.cur !! b = some (.dir J) ∧ hJ.cur = ∅⌝ ∗
            osNames J (.except []) (DFrac.own 1) hJ) }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  imod osLogLb_0 with #Hlb
  cases hcb : h.cur !! b with
  | some n =>
    have hsome : (h.cur !! b).isSome := by rw [hcb]; rfl
    iloeb as IH generalizing Hperm Hp Hn
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    try wp_auto
    wp_stub syscall.fsMkdir.impl
    wp_apply wp_osCallBeginS R _ 1 0 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    -- PORT: which stub? (MkdirS)
    wp_apply wp_osMkdirS_some R d b j (.only [b]) dq (DFrac.own 1) h t s0 1 hb hbN hsome
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      iapply IH $$ Hperm Hp Hn HΦ
    rw [decide_eq_false he4]
    try wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    wp_apply os.wp_modelErrno
    try wp_auto
    wp_apply os.wp_modelPathError
    iapply HΦ
    iframe Hp Hperm
    iexists h
    iframe Hn
    ileft; ipureintro; exact ⟨rfl, fun hc => by cases hc⟩
  | none =>
  ihave HSt : iprop(osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∨
      ∃ h1 J hJ, osNames (GF := GF) j (.only [b]) (DFrac.own 1) h1 ∗
        ⌜h1.cur !! b = some (.dir J) ∧ hJ.cur = ∅⌝ ∗ osNames (GF := GF) J (.except []) (DFrac.own 1) hJ)
    $$ [Hn]
  · ileft; iexact Hn
  iloeb as IH generalizing Hperm Hp HSt
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub syscall.fsMkdir.impl
  wp_apply wp_osCallBeginS R _ 1 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (Hn | ⟨%h1, %J, %hJ, Hn, %hJ1, HJ⟩)
  · wp_apply wp_osMkdirS R d b j dq h t s0 hb hcb CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Hn Hk as %e Hperm Hp Hres
    icases Hres with (⟨%he, Hn⟩ | ⟨%x, %J, -, Hn, %hJ, HJ, %hJ'⟩)
    · by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ Hperm Hp [Hn] HΦ
        ileft; iexact Hn
      rw [decide_eq_false he4]
      try wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he)]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError
      iapply HΦ
      iframe Hp Hperm
      iexists h
      iframe Hn
      ileft; ipureintro; exact ⟨rfl, fun hc => by cases hc⟩
    · have hd : (h.log x (⟨.mkdir j b J, s0⟩ : LogEntry) (<[b := .dir J]> h.cur)).cur !! b =
          some (.dir J) := by simp only [NamesH.log]; rw [GMap.lookup_insert]
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ Hperm Hp [Hn HJ] HΦ
        iright; iexists _, J, hJ; iframe Hn HJ; ipureintro; exact ⟨hd, hJ'.1⟩
      rw [decide_eq_false he4]
      try wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        try wp_auto
        iapply HΦ
        iframe Hp Hperm
        iexists _
        iframe Hn
        iright; iexists J, hJ; iframe HJ; ipureintro; exact ⟨hd, hJ'.1⟩
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError
      iapply HΦ
      iframe Hp Hperm
      iexists _
      iframe Hn
      iright; iexists J, hJ; iframe HJ; ipureintro; exact ⟨hd, hJ'.1⟩
  · have hsome : (h1.cur !! b).isSome := by rw [hJ1.1]; rfl
    -- PORT: which stub? (MkdirS)
    wp_apply wp_osMkdirS_some R d b j (.only [b]) dq (DFrac.own 1) h1 t s0 1 hb hbN hsome
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      iapply IH $$ Hperm Hp [Hn HJ] HΦ
      iright; iexists h1, J, hJ; iframe Hn HJ; ipureintro; exact hJ1
    rw [decide_eq_false he4]
    try wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    wp_apply os.wp_modelErrno
    try wp_auto
    wp_apply os.wp_modelPathError
    iapply HΦ
    iframe Hp Hperm
    iexists h1
    iframe Hn
    iright; iexists J, hJ; iframe HJ; ipureintro; exact hJ1

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
