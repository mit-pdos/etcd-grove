/-
The proof of `readFrame` (`Net/Spec/.../lib/remote/readFrame.lean`): `readFull` of an 8-byte
header `hdr`, `getU64` of it, the check against `MaxLen`, `readFull` of a body of that length; on
success the reader has read `hdr ++ body`, which is `frame body` since `hdr` is the encoding of its
own decoding (`leToU64_le`), the body's length.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.getU64
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFull
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFrame

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS]

theorem readFrame.wp_proof (wp_readFull : readFull.spec (GF := GF) (hG := hG))
    (wp_getU64 : getU64.spec (GF := GF) (hG := hG)) :
    readFrame.spec (GF := GF) (hG := hG) := by
  intro c cn s a P R eof ed
  wp_start as ⟨#Hc, #Heof, #Hed, Htok⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %h ⟨Hh, -⟩
  · ipureintro; decide
  wp_apply wp_readFull c cn s a P R h _ eof ed $$ [Hh Htok]
    as %ok ⟨%got, %bs', Htok, Hh, %Hbs⟩
  · iframe Hc Hh Heof Hed Htok
  cases ok with
  | false =>
    -- the header could not be read
    wp_auto
    iapply HΦ
    iexists got
    iframe Htok
    ileft; ipureintro; rfl
  | true =>
  obtain ⟨hl, -, hg⟩ := Hbs
  have hg := hg rfl
  subst hg
  have hg8 : got.length = 8 := by rw [hl]; simp
  rw [← List.append_nil got]
  wp_auto
  wp_apply wp_getU64 h _ got [] hg8 $$ Hh as Hh
  wp_if_destruct
  · -- a length beyond `MaxLen`
    iapply HΦ
    iexists got
    rw [List.append_nil]
    iframe Htok
    ileft; ipureintro; rfl
  rw [List.append_nil] at *
  have hn : uint.Z (leToU64 got) ≤ 2 ^ 20 := by
    have : uint.Z (W64 1048576) = 2 ^ 20 := by decide
    omega
  wp_apply (wp_slice_make2 (V := w8) (leToU64 got)) as %p ⟨Hp, -⟩
  · ipureintro; word
  wp_apply wp_readFull c cn s a P (R ++ got) p _ eof ed $$ [Hp Htok]
    as %ok2 ⟨%got2, %bs2, Htok, Hp, %Hbs2⟩
  · iframe Hc Hp Heof Hed Htok
  rw [List.append_assoc]
  cases ok2 with
  | false =>
    -- the body could not be read
    wp_auto
    iapply HΦ
    iexists got ++ got2
    iframe Htok
    ileft; ipureintro; rfl
  | true =>
  obtain ⟨hl2, -, hg2⟩ := Hbs2
  have hg2 := hg2 rfl
  subst hg2
  wp_auto
  iapply HΦ
  iexists got ++ got2
  iframe Htok
  iright
  iexists got2
  iframe Hp
  ipureintro
  have hl2' : got2.length = uint.nat (leToU64 got) := by rw [hl2]; simp; word
  refine ⟨rfl, ?_, by rw [hl2']; show uint.nat (leToU64 got) ≤ 2 ^ 20; word⟩
  rw [frame]
  congr 1
  rw [← leToU64_le got hg8]
  congr 1
  rw [hl2']; word

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
