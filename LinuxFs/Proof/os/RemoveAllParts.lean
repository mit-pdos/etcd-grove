/-
The pieces of `os.RemoveAll`'s model (`TrustedCode/os.lean`) in the tree's shared mode, for
`Proof/os/RemoveAll.lean` (`notes/wal-fsext-i2-design.md`, "Implementation log, `os.RemoveAll`").
Lean-first; untrusted.
-/
module

public import LinuxFs.Proof.os.MkdirAllParts
public import LinuxFs.Spec.os.RemoveAll

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

theorem os.wp_endsWithDot_child (d b : GoString) (hb : NameOk b) :
    {{ (True : IProp GF) }} (App (Val #(functions go!"os.endsWithDot" [])) (Val #(child d b)))
    {{ RET #false; True }} := by
  rw [show (go!"os.endsWithDot" : GoString) = os.endsWithDot from rfl]
  wp_start
  try wp_auto
  obtain ⟨hne, hdot, -, hs, -⟩ := hb
  have hlen : (child d b).length = d.length + 1 + b.length := by simp [child]; omega
  obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by
    cases b with | nil => exact absurd rfl hne | cons _ _ => simp⟩
  rw [decide_eq_false (show child d b ≠ [46#8] from fun h => by
    have := congrArg List.length h; simp [child] at this; omega)]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  rw [hlen] at Hl ⊢
  simp only [show sint.Z (W64 2) ≤ sint.Z (W64 ((d.length + 1 + b.length : Nat) : Int)) by word,
    _root_.decide_true]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [hlen]
  try wp_auto
  have hkb : k < b.length := by omega
  have hg1 : (child d b)[d.length + 1 + k]? = some b[k] := by
    simp [child, List.getElem?_append_right, show d.length ≤ d.length + 1 + k by omega,
      show d.length + 1 + k - d.length = k + 1 by omega, List.getElem?_eq_getElem hkb]
  rw [show W64 ((d.length + 1 + b.length : Nat) : Int) - W64 1 =
      W64 ((d.length + 1 + k : Nat) : Int) by rw [hk]; word]
  simp only [show (0 : Int) ≤ sint.Z (W64 ((d.length + 1 + k : Nat) : Int)) by word, ↓reduceIte,
    show sint.nat (W64 ((d.length + 1 + k : Nat) : Int)) = d.length + 1 + k by word, hg1]
  try wp_auto
  by_cases hd : b[k] = W8 46
  · rw [decide_eq_true hd]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    rw [hlen]
    try wp_auto
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by
      rcases k with _ | k
      · exfalso; apply hdot
        cases b with
        | nil => exact absurd rfl hne
        | cons x xs =>
          simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hk
          subst hk; simp only [List.getElem_cons_zero] at hd; rw [hd]; rfl
      · simp⟩
    have hmb : m < b.length := by omega
    have hg2 : (child d b)[d.length + 1 + m]? = some b[m] := by
      simp [child, List.getElem?_append_right, show d.length ≤ d.length + 1 + m by omega,
        show d.length + 1 + m - d.length = m + 1 by omega, List.getElem?_eq_getElem hmb]
    rw [show W64 ((d.length + 1 + b.length : Nat) : Int) - W64 2 =
        W64 ((d.length + 1 + m : Nat) : Int) by rw [hk]; word]
    simp only [show (0 : Int) ≤ sint.Z (W64 ((d.length + 1 + m : Nat) : Int)) by word, ↓reduceIte,
      show sint.nat (W64 ((d.length + 1 + m : Nat) : Int)) = d.length + 1 + m by word, hg2]
    try wp_auto
    rw [show (os.IsPathSeparator : GoString) = go!"os.IsPathSeparator" from rfl]
    wp_apply os.wp_IsPathSeparator
    rw [decide_eq_false (show b[m] ≠ slashB from fun h => hs (h ▸ List.getElem_mem hmb))]
    try wp_auto
    iapply HΦ; itrivial
  · rw [decide_eq_false hd]
    try wp_auto
    iapply HΦ; itrivial

theorem os.wp_splitPath_child (d b : GoString) (hb : NameOk b)
    (hd : ∃ c rest, d = slashB :: c :: rest ∧ c ≠ slashB) :
    {{ (True : IProp GF) }} (App (Val #(functions go!"os.splitPath" [])) (Val #(child d b)))
    {{ RET (PairV #d #b); True }} := by
  rw [show (go!"os.splitPath" : GoString) = os.splitPath from rfl]
  obtain ⟨c, rest, hdd, hc⟩ := hd
  obtain ⟨hne, -, -, hs, -⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by
    cases b with | nil => exact absurd rfl hne | cons _ _ => simp⟩
  have hdl : 2 ≤ d.length := by rw [hdd]; simp
  have hlen : (child d b).length = d.length + 1 + b.length := by simp [child]; omega
  have hg0 : (child d b)[0]? = some slashB := by rw [hdd]; simp [child]
  have hg1 : (child d b)[1]? = some c := by rw [hdd]; simp [child]
  wp_start
  try wp_auto
  ihave HI : (path_ptr ↦ child d b : IProp GF) $$ [path]
  · iexact path
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  rw [hlen] at Hl ⊢
  try wp_auto
  simp only [show sint.Z (W64 1) < sint.Z (W64 ((d.length + 1 + b.length : Nat) : Int)) by word,
    _root_.decide_true]
  try wp_auto
  simp only [hg0]
  try wp_auto
  simp only [hg1]
  try wp_auto
  rw [decide_eq_false (show c ≠ W8 47 from hc)]
  try wp_auto
  rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
    if_pos (by simp)]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [hlen]
  try wp_auto
  have hkb : k < b.length := by omega
  have hgk : (child d b)[d.length + 1 + k]? = some b[k] := by
    simp [child, List.getElem?_append_right, show d.length ≤ d.length + 1 + k by omega,
      show d.length + 1 + k - d.length = k + 1 by omega, List.getElem?_eq_getElem hkb]
  rw [show W64 ((d.length + 1 + b.length : Nat) : Int) - W64 1 =
      W64 ((d.length + 1 + k : Nat) : Int) by rw [hk]; word]
  ihave HI : ("path" ∷ path_ptr ↦ child d b ∗ "i" ∷ i_ptr ↦ W64 ((d.length + 1 + k : Nat) : Int) :
      IProp GF) $$ [HI i]
  · iframe
  wp_for HI
  simp only [show sint.Z (W64 0) < sint.Z (W64 ((d.length + 1 + k : Nat) : Int)) by word,
    _root_.decide_true]
  try wp_auto
  simp only [show (0 : Int) ≤ sint.Z (W64 ((d.length + 1 + k : Nat) : Int)) by word, ↓reduceIte,
    show sint.nat (W64 ((d.length + 1 + k : Nat) : Int)) = d.length + 1 + k by word, hgk]
  try wp_auto
  rw [decide_eq_false (show b[k] ≠ W8 47 from fun h => hs (by
    rw [show slashB = W8 47 from rfl, ← h]; exact List.getElem_mem hkb))]
  try wp_auto
  rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
    if_pos (by simp)]
  try wp_auto
  rw [show W64 ((d.length + 1 + k : Nat) : Int) - W64 1 = W64 ((d.length + k : Nat) : Int) by word]
  ihave HJ : (∃ (t : Nat), "%Ht" ∷ ⌜t ≤ k⌝ ∗ "i" ∷ i_ptr ↦ W64 ((d.length + t : Nat) : Int) ∗
      "path" ∷ path_ptr ↦ child d b ∗ "basename" ∷ basename_ptr ↦ child d b ∗
      "dirname" ∷ dirname_ptr ↦ [46#8] : IProp GF) $$ [i path basename dirname]
  · iexists k; iframe; ipureintro; exact Nat.le_refl _
  wp_for HJ
  simp only [show sint.Z (W64 0) ≤ sint.Z (W64 ((d.length + t : Nat) : Int)) by word,
    _root_.decide_true]
  try wp_auto
  rw [if_pos trivial]
  try wp_auto
  simp only [show (0 : Int) ≤ sint.Z (W64 ((d.length + t : Nat) : Int)) by word, ↓reduceIte,
    show sint.nat (W64 ((d.length + t : Nat) : Int)) = d.length + t by word]
  rcases t with _ | t
  · have hgs : (child d b)[d.length + 0]? = some slashB := by simp [child]
    simp only [hgs]
    try wp_auto
    rw [decide_eq_false (show W64 ((d.length + 0 : Nat) : Int) ≠ W64 0 by
      intro h; have := congrArg sint.Z h; rw [show sint.Z (W64 0) = 0 from rfl] at this; word)]
    try wp_auto
    rw [if_pos (by refine ⟨by word, by word, by word⟩)]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    rw [hlen]
    try wp_auto
    rw [if_pos (by refine ⟨by word, by word, by word⟩)]
    try wp_auto
    have h2 : List.take (sint.nat (W64 ((d.length + 1 + b.length : Nat) : Int)) -
          sint.nat (W64 ((d.length + 0 : Nat) : Int) + W64 1))
        (List.drop (sint.nat (W64 ((d.length + 0 : Nat) : Int) + W64 1)) (child d b)) = b := by
      rw [show sint.nat (W64 ((d.length + 1 + b.length : Nat) : Int)) = d.length + 1 + b.length by word,
        show sint.nat (W64 ((d.length + 0 : Nat) : Int) + W64 1) = d.length + 1 by word]
      simp [child]
    simp only [h2]
    try wp_auto
    iapply wp_for_post_break
    try wp_auto
    rw [show List.take (sint.nat (W64 ((d.length + 0 : Nat) : Int)) - 0) (List.drop 0 (child d b)) = d by
      rw [show sint.nat (W64 ((d.length + 0 : Nat) : Int)) = d.length by word]; simp [child]]
    iapply HΦ; itrivial
  · have htb : t < b.length := by omega
    have hgt : (child d b)[d.length + (t + 1)]? = some b[t] := by
      simp [child, List.getElem?_append_right, show d.length ≤ d.length + (t + 1) by omega,
        List.getElem?_eq_getElem htb]
    simp only [hgt]
    try wp_auto
    rw [decide_eq_false (show b[t] ≠ W8 47 from fun h => hs (by
      rw [show slashB = W8 47 from rfl, ← h]; exact List.getElem_mem htb))]
    try wp_auto
    wp_for_post
    iframe
    iexists t
    rw [show W64 ((d.length + (t + 1) : Nat) : Int) - W64 1 = W64 ((d.length + t : Nat) : Int) by word]
    iframe
    ipureintro; omega

/-- A spine to `d/b` borrowed from a spine to `d` and the whole claim on `b` (a directory). -/
theorem os.osPathS_borrow (R : Roots) (d b : GoString) (j J : Ino) (qd : Qp) (h : NamesH)
    (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    osPathS (GF := GF) R d (DFrac.own qd) j ∗ osNames j (.only [b]) (DFrac.own 1) h ⊢
      ∃ e : Qp, osPathS R (child d b) (DFrac.own e) J ∗
        (osPathS R (child d b) (DFrac.own e) J -∗
          osPathS R d (DFrac.own qd) j ∗ osNames j (.only [b]) (DFrac.own 1) h) := by
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd 1
  iintro ⟨Hp, Hn⟩
  rw [← hqd]
  rw [← hqq]
  icases (osPathS_frac R d ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h).1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R d b (DFrac.own ε) j J h hb hJ $$ Hpe Hne
  iexists ε
  iframe
  iintro Hpc
  icases os.osPathS_unchild R d b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
  subst he
  iframe
  iapply (osNames_frac j (.only [b]) ε b' h'').2
  iframe

/-- `RemoveAll`'s error pointer: `nil`, or a `*PathError` whose `Path` it owns (the model prefixes
it) and whose other fields are persistent, its `Err` one `fmt` formats. -/
def os.peOk (pe : Loc) : IProp GF :=
  iprop(⌜pe = null⌝ ∨ ∃ (op path : GoString) (err : GoInterface),
    structFieldRef io.fs.PathError go!"Op" pe ↦□ op ∗
    structFieldRef io.fs.PathError go!"Path" pe ↦ path ∗
    structFieldRef io.fs.PathError go!"Err" pe ↦□ err ∗ fmtErrorOk err)

theorem os.peOk_null : ⊢ os.peOk (GF := GF) null := by
  unfold os.peOk; iintro; ileft; ipureintro; rfl

/-- `model.pathErrorPtr op path err` of an `err` `fmt` formats. -/
theorem os.model.wp_pathErrorPtr (op path : GoString) (err : GoInterface) :
    {{ fmtErrorOk (GF := GF) err }}
      (App (App (App (Val os.model.pathErrorPtr) (Val #op)) (Val #path)) (Val #err))
    {{ (pe : Loc), RET #pe; os.peOk pe }} := by
  wp_start as #Herr
  iapply wp_fupd
  wp_auto
  iStructNamed pe
  ipersist Op
  ipersist Err
  imodintro
  iapply HΦ
  unfold os.peOk
  iright
  iexists op, path, err
  iframe; iframe #

/-- `model.prefixPath pe pre`. -/
theorem os.model.wp_prefixPath (pe : Loc) (pre : GoString) :
    {{ os.peOk (GF := GF) pe }}
      (App (App (Val os.model.prefixPath) (Val #pe)) (Val #pre))
    {{ RET #(); os.peOk pe }} := by
  wp_start as Hpe
  by_cases hn : pe = null
  · rw [decide_eq_true hn]
    wp_auto
    iapply HΦ $$ Hpe
  rw [decide_eq_false hn]
  unfold os.peOk
  icases Hpe with (%hn' | ⟨%op, %path, %err, #Hop, Hpath, #Herr, #Hok⟩)
  · exact absurd hn' hn
  wp_auto
  iapply HΦ
  iright
  iexists _, _, err
  iframe; iframe #

/-- `model.pathErrorPtr op path (Errno e)`, `e` nonzero. -/
theorem os.model.wp_pathErrorPtr_errno (op path : GoString) (e : w64) (he : e ≠ 0)
    (Φ : val → IProp GF) :
    (∀ pe : Loc, os.peOk pe -∗ Φ #pe) ⊢
      WP (App (App (App (Val os.model.pathErrorPtr) (Val #op)) (Val #path))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_errno
  wp_apply os.model.wp_pathErrorPtr op path (errnoErr e) $$ [] as %pe Hpe
  · iapply errnoErr_fmtErrorOk e he
  iapply HΦ $$ Hpe

/-- `model.pathErrorPtr "readdirnames" b (model.pathError "readdirent" b (Errno e))`, `e`
nonzero. -/
theorem os.model.wp_pathErrorPtr_rd (b : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    (∀ pe : Loc, os.peOk pe -∗ Φ #pe) ⊢
      WP (App (App (App (Val os.model.pathErrorPtr) (Val #go!"readdirnames")) (Val #b))
        (App (App (App (Val os.model.pathError) (Val #go!"readdirent")) (Val #b))
          (App (Val syscall.model.errno) (Val #e)))) {{ Φ }} := by
  iintro HΦ
  wp_apply os.wp_pathError_ok _ _ e he as %pe0 #Hok
  wp_apply os.model.wp_pathErrorPtr _ _ _ $$ Hok as %pe Hpe
  iapply HΦ $$ Hpe

end proof

end EtcdGrove
end Perennial
