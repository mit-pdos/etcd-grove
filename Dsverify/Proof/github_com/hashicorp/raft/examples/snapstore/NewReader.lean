/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc/NewReader.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
The proof of `snapstore.NewReader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.NewReader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.copyBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Reader__Read
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Reader__Close

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.NewReader.wp_proof
    (wp_copyBytes : github_com.hashicorp.raft.examples.snapstore.copyBytes.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.hashicorp.raft.examples.snapstore.Reader.Read.spec (GF := GF) (hG := hG))
    (wp_Close : github_com.hashicorp.raft.examples.snapstore.Reader.Close.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.snapstore.NewReader.spec (GF := GF) (hG := hG) :=
  fun sl dq b eof => by
  wp_start as ⟨#Heof, Hsl⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_copyBytes $$ [$Hsl] as %c ⟨Hsl, Hc⟩
  irename «$r0» => Hrd
  generalize «$r0_ptr» = rd at *
  iStructNamedPrefix Hrd "R"
  ipersist Rb
  ipersist Hc
  imodintro
  iapply HΦ
  iframe Hsl
  iexists readerSt rd
  isplitl []
  · unfold readCloserOk streamReaderOk
    isplitl
    · imodintro
      iintro %p %buf %cs %Φ %Hbuf HR Hp HΦ
      iapply wp_Read rd p buf cs eof $$ [$Hpkg $Heof $HR $Hp]
      · ipureintro; exact Hbuf
      inext
      iintro %n %err ⟨%Hn, Hp, HR⟩
      iapply HΦ $$ %n %err %Hn Hp HR
    · imodintro
      iintro %Φ HΦ
      iapply wp_Close rd $$ [$Hpkg]
      inext; iintro -; iexact HΦ
  isplitl
  · unfold readerSt
    iexists c, b, (0 : w64)
    iframe Roff
    iframe #
    ipureintro; refine ⟨by decide, by word, ?_⟩; rw [show sint.nat (0 : w64) = 0 from rfl, List.drop_zero]
  ipureintro; go_type_set

end proof

end Perennial
