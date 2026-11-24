/-
Go's `os.Mkdir` (translated since 2026-11-24, Go-model overlays S5) over `syscall`'s model of `Mkdir`
(`models/syscall/model.go`): `fixLongPath`, then `ignoringEINTR` around a closure calling
`syscall.Mkdir(longName, syscallMode(perm))`, whose model asks `PathKind` and, below a root, runs the
stub `fsMkdir` (`CallBegin`, the extension's `Mkdir`); then `&PathError{"mkdir", name, e}` for an
error. `os.Mkdir.wp_tree` below a root, for any per-attempt resource (`os.mkdirAttempt`: one
`fsMkdir`); `os.Mkdir.wp_notTree` at a root or an ancestor of one (no step: some error);
`os.Mkdir.wp_takenS` of a taken name (an error, no effect). Untrusted.
-/
module

public import Proof.os.SharedAu
public import Proof.os.ErrorOk
public import Proof.os.SharedExt
public import Proof.os.PathKindS
public import Proof.os.IgnoringEINTR
public import Perennial.Proof.internal.gomodel.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- A path of the roots followed by a component is strictly below a root. -/
theorem os.treeName_child {R : Roots} {d b : GoString} (h : PathIn R d) (hb : NameOk b) :
    RootsTreeName R (child d b) := by
  obtain ⟨r, j0, cs, hm, hcs, rfl⟩ := h
  refine ⟨(r, j0), hm, cs ++ [b], by simp, fun c hc => ?_, (joinPath_snoc r cs b).symm⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact hcs c hc
  · simp at hc; subst hc; exact hb

/-- One attempt of `syscall.Mkdir(p)` below a root: the stub `fsMkdir` (`CallBegin`, the
extension's `Mkdir`), from `I`, gives `I` back on `EINTR` and `Ψ e` on any other errno. -/
def os.mkdirAttempt (p : GoString) (I : IProp GF) (Ψ : w64 → IProp GF) : IProp GF :=
  iprop(∀ (m : w32) (Φ : val → IProp GF), I -∗
    (∀ e : w64, ((⌜e = W64 4⌝ ∗ I) ∨ (⌜e ≠ W64 4⌝ ∗ Ψ e)) -∗ Φ #e) -∗
    WP (App (App (Val (@! syscall.fsMkdir)) (Val #p)) (Val #m)) {{ Φ }})

/-- **`os.Mkdir(p)` below a root** (`PathKind` is `1`): attempts (`os.mkdirAttempt`) until one does
not return `EINTR`; its errno `e` gives the result: `nil` for 0, else a `*PathError`. -/
theorem os.Mkdir.wp_tree (R : Roots) (p : GoString) (perm : w32) (I : IProp GF) (Ψ : w64 → IProp GF)
    (hpin : PathIn R p) (htn : RootsTreeName R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ I ∗ □ os.mkdirAttempt p I Ψ }}
      (App (App (Val (@! os.Mkdir)) (Val #p)) (Val #perm))
    {{ (err : GoInterface), RET #err; ∃ e : w64, Ψ e ∗ ⌜e ≠ W64 4 ∧ (err = interface.nil ↔ e = 0)⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, HI, #Hat⟩
  try wp_auto
  wp_apply os.wp_fixLongPath
  try wp_auto
  rw [recv_eq_func_mk]
  wp_apply (os.wp_ignoringEINTR _ iprop(I ∗ longName_ptr ↦ p ∗ perm_ptr ↦ perm)
    (fun e => iprop(⌜e ≠ W64 4⌝ ∗ Ψ e))) $$ [HI longName perm] as %e ⟨%he4, HΨ⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨HI, Hln, Hpm⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    wp_apply os.wp_syscallMode as %m _
    try wp_auto
    wp_func_call; wp_call
    try wp_auto
    wp_stub syscall.fsPathKind.impl
    wp_apply wp_osPathKindS R p hpin CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi as %k %hk
    obtain ⟨-, rfl⟩ := hk.resolve_right (fun h => h.1 htn)
    try wp_auto
    iunfold os.mkdirAttempt at Hat
    wp_apply Hat $$ HI as %e' Hr
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ'
    icases Hr with (⟨%he, HI⟩ | ⟨%he, HΨ⟩)
    · ileft; iframe; ipureintro; exact he
    · iright; dsimp only; iframe; ipureintro; exact ⟨he, he⟩
  by_cases h0 : e = 0
  · subst h0
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    iapply HΦ
    iexists W64 0
    iframe
    ipureintro; exact ⟨he4, by simp⟩
  · simp only [errnoErr, h0, ↓reduceIte]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    iexists e
    iframe
    ipureintro
    refine ⟨he4, ?_⟩
    simp
    first | exact h0 | simpa using h0 | (intro h; apply h0; rw [h]; rfl)

/-- **`os.Mkdir(p)` at a root or an ancestor of one** (`PathKind` is not `1`): any errno but 0,
no step of the extension (each `EINTR` retried): an error. -/
theorem os.Mkdir.wp_notTree (R : Roots) (p : GoString) (perm : w32)
    (hk : ∀ Φ : val → IProp GF, osInv (GF := GF) ∗ osSharedInv R ∗ (∀ k : w64, ⌜k ≠ W64 1⌝ -∗ Φ #k) ⊢
      WP (App (Val (@! syscall.fsPathKind)) (Val #p)) {{ Φ }}) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (App (Val (@! os.Mkdir)) (Val #p)) (Val #perm))
    {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }} := by
  wp_start as ⟨#Hos, #Hsi⟩
  try wp_auto
  wp_apply os.wp_fixLongPath
  try wp_auto
  rw [recv_eq_func_mk]
  wp_apply (os.wp_ignoringEINTR _ iprop(longName_ptr ↦ p ∗ perm_ptr ↦ perm)
    (fun e => iprop(⌜e ≠ W64 0⌝))) $$ [longName perm] as %e %he0
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hln, Hpm⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    wp_apply os.wp_syscallMode as %m _
    try wp_auto
    wp_func_call; wp_call
    try wp_auto
    wp_bind (App (Val (@! syscall.fsPathKind)) (Val #p))
    iapply hk
    iframe Hos Hsi
    iintro %k %hk1
    try wp_auto
    rw [decide_eq_false hk1]
    try wp_auto
    wp_apply internal.gomodel.wp_ChooseUint64 as %x _
    try wp_auto
    have hpost : ∀ y : w64, y ≠ 0 → (interface.mkOk syscall.Errno.ty #y : GoInterface) = errnoErr y := by
      intro y hy; unfold errnoErr; rw [if_neg hy]
    by_cases hx : x = 0
    · subst hx
      try wp_auto
      try simp only [syscall.EEXIST]
      try wp_auto
      rw [hpost _ (by decide)]
      iapply HΦ'
      iright; (try dsimp only); iframe; ipureintro; exact ⟨by decide, by decide⟩
    · rw [decide_eq_false (show x ≠ W64 0 from hx)]
      try wp_auto
      rw [hpost _ hx]
      iapply HΦ'
      by_cases hx4 : x = W64 4
      · ileft; iframe; ipureintro; exact hx4
      · iright; (try dsimp only); iframe; ipureintro; exact ⟨hx4, hx⟩
  have he0' : ¬ e = 0 := he0
  simp only [errnoErr, he0', ↓reduceIte]
  try wp_auto
  try wp_alloc pe as Hpe
  try wp_auto
  iapply HΦ
  ipureintro; intro hc; cases hc

/-- `os.Mkdir(d/b)` of a name holding something (a fraction of a claim on names containing `b`), with
a fraction of the call permission: an error, no effect. -/
theorem os.Mkdir.wp_takenS (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : (h.cur !! b).isSome) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗
        ⌜err ≠ interface.nil⌝ }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩ HΦ
  icases osPathS_pathIn_keep R d dq j $$ Hp with ⟨%hpd, Hp⟩
  have hpin : PathIn R (child d b) := pathIn_child hpd.2 hb
  have htn : RootsTreeName R (child d b) := os.treeName_child hpd.2 hb
  imod osLogLb_0 with #Hlb
  wp_apply (os.Mkdir.wp_tree R (child d b) perm
    iprop(osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc)
    (fun e => iprop(⌜e ≠ 0⌝ ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc))
    hpin htn) $$ [Hp Hn Hperm] as %err ⟨%e, ⟨%he0, Hp, Hn, Hperm⟩, %he⟩
  · iframe; iframe #
    iintro !>
    unfold os.mkdirAttempt
    iintro %m %Φ' ⟨Hp, Hn, Hperm⟩ HΦ'
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsMkdir.impl
    wp_apply +noauto wp_osCallBeginS R _ qc 0 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    wp_apply +noauto wp_osMkdirS_some R d b j N dq dqn h t s0 qc hb hN hi
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
    iapply HΦ'
    by_cases he4 : e = W64 4
    · ileft; iframe; ipureintro; exact he4
    · iright; (try dsimp only); iframe; ipureintro; exact ⟨he4, he⟩
  iapply HΦ
  iframe
  ipureintro; intro hc; exact he0 (he.2.1 hc)

end proof

end EtcdGrove
end Perennial
