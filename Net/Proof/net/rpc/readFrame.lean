/-
The proof of `readFrame` (`Net/Spec/net/rpc/readFrame.lean`): `readFull` of the 8-byte length
(`first`), `getU64`, the check against `maxFrame`, then `readFull` of the payload into a fresh
slice, its reader predicate `P` after the length's bytes.
-/
module

public import Net.Spec.net.rpc.readFrame
public import Net.Spec.net.rpc.getU64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- What `readFull` returns, an error, is one of `readErr`'s, never `nil`. -/
theorem readErr_ne_nil (la ra eof ueof ed : GoInterface) (first : Bool) (got : List w8)
    (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗ readErr la ra eof ueof ed first got err ⊢
      ⌜err ≠ interface.nil⌝ := by
  iintro ⟨#Hio, #Heof, #Hueof, HE⟩
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, HEOF, HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%x1, #Hx1, -⟩
  icases HUEOF with ⟨%x2, #Hx2, -⟩
  icombine Heof Hx1 gives %H1
  icombine Hueof Hx2 gives %H2
  subst H1 H2
  unfold readErr
  icases HE with (%H | %H | ⟨%k, HE⟩)
  · ipureintro; rw [H.1]; simp [interface.mkOk]
  · ipureintro; rw [H]; simp [interface.mkOk]
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    ipureintro; exact net.netErr_ne_nil (Hne.2 (by simp))

theorem readFrame.wp_proof (wp_readFull : readFull.spec (GF := GF) (hG := hG))
    (wp_getU64 : getU64.spec (GF := GF) (hG := hG)) :
    readFrame.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra P eof ueof ed ef
  wp_start as ⟨#Hc, #Hio, #Heof, #Hueof, #Hed, #Hef, #HefV, HP, #Hacc⟩
  unfold errors.newVar
  icases HefV with ⟨%xf, #Hxf, -⟩
  icombine Hef Hxf gives %Hf
  subst Hf
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %h ⟨Hh, Hhcap⟩
  · ipureintro; decide
  wp_apply wp_readFull t cn s a la ra h _ true P _ _ ed $$ [$Hc $Hh $Hio $Heof $Hueof $Hed $HP $Hacc]
    as %err ⟨%got, %bs', HP, Hh, %Hbs, Hres⟩
  icases Hres with (%Hok | ⟨%Hne, #HE⟩)
  rotate_left
  · -- the length could not be read
    ihave %Hnn := readErr_ne_nil _ _ _ _ _ _ _ _ $$ [$Hio $Heof $Hueof $HE]
    cases err with
    | nil => exact absurd rfl Hnn
    | ok e =>
      wp_auto
      iapply HΦ
      iexists got
      iframe HP
      iright
      isplitr
      · ipureintro; exact Hnn
      iright; iexact HE
  obtain ⟨rfl, rfl⟩ := Hok
  have hg8 : got.length = 8 := by rw [Hbs.1]; simp
  rw [← List.append_nil got]
  wp_auto
  wp_apply wp_getU64 h _ got [] hg8 $$ Hh as Hh
  wp_if_destruct
  · -- a length beyond `maxFrame`
    iapply HΦ
    iexists got
    rw [List.append_nil]
    iframe HP
    iright
    isplitr
    · ipureintro; simp [interface.mkOk]
    ileft; ipureintro; rfl
  rename_i Hsmall
  have hn : uint.Z (leToU64 got) ≤ 2 ^ 30 := by
    have : uint.Z (W64 1073741824) = 2 ^ 30 := by decide
    omega
  wp_apply (wp_slice_make2 (V := w8) (leToU64 got)) as %p ⟨Hp, Hpcap⟩
  · ipureintro; word
  wp_apply wp_readFull t cn s a la ra p _ false (fun g => P (got ++ g)) _ _ ed
      $$ [$Hc $Hp $Hio $Heof $Hueof $Hed HP]
    as %err ⟨%got2, %bs2, HP, Hp, %Hbs2, Hres⟩
  · iframe HP
    imodintro
    iintro %g %m Hg
    imod Hacc $$ %(got ++ g) %m Hg with ⟨%st, %d, HE, HD, Hcl⟩
    imodintro
    iexists st, d
    iframe HE HD
    iintro %r %d' %Hrd HE HD
    rw [← List.append_assoc]
    iapply Hcl $$ %r %d' %Hrd HE HD
  icases Hres with (%Hok | ⟨%Hne, #HE⟩)
  rotate_left
  · -- the payload could not be read
    ihave %Hnn := readErr_ne_nil _ _ _ _ _ _ _ _ $$ [$Hio $Heof $Hueof $HE]
    cases err with
    | nil => exact absurd rfl Hnn
    | ok e =>
      wp_auto
      iapply HΦ
      iexists got ++ got2
      iframe HP
      iright
      isplitr
      · ipureintro; exact Hnn
      iright
      unfold readErr
      icases HE with (%H | %H | ⟨%k, HE⟩)
      · exact absurd H.2.2 (by simp)
      · iright; ileft; ipureintro; exact H
      · iright; iright; iexists k; iexact HE
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  iapply HΦ
  iexists got ++ got2
  iframe HP
  ileft
  iexists got2
  iframe Hp Hpcap
  ipureintro
  have hl2 : got2.length = uint.nat (leToU64 got) := by rw [Hbs2.1]; simp; word
  refine ⟨rfl, ?_, by rw [hl2]; unfold maxFrameN; word⟩
  rw [frameOf]
  congr 1
  rw [← leToU64_le got hg8]
  congr 1
  rw [hl2]; word

end proof

end net.rpc
end Perennial
