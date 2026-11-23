/-
The connection reader in the head phase is a stream reader that makes progress
(`io.readerStreamNE`, over `connReader.Read.spec`), with its stream bound and the head's prefix law:
what `conn.serve`'s `bufio.Reader` (`c.bufr`) needs of it (`bufio.NewReader`, `modelReadLine`,
`modelReadMIMEHeader`).
-/
module

public import Net.Spec.net.http.connReader__Read
public import Proof.io.ReaderStreamNE

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
theorem crHead_stream (wp_crRead : connReader.Read.spec (GF := GF) (hG := hG))
    (cr : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (L : Nat) (c : Loc) (γe : GName)
    (hc : c ≠ null) (hL : L < 2 ^ 62) :
    crIs cr γ cn P hs Z ∗ readEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗ crConnOk c ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ⊢
    EtcdGrove.io.readerStreamNE ⟨go.GoType.PointerType net.http.connReader.ty, #cr⟩
      (crHead cr γ γe cn P Q L c) (crHeadErr γe) := by
  iintro ⟨#Hcr, #Henv, #Hio, #Hcok, #Hrwc, #Hca⟩
  iunfold EtcdGrove.io.readerStreamNE
  imodintro
  iintro %r0 %p %xs
  imodintro
  iintro %Φ ⟨%Hb, HS, Hp⟩ HΦ
  iapply wp_crRead cr γ t cn a la ra P Q hs Z L c γe r0 p xs $$ [HS Hp]
  · iframe Hcr Henv Hio Hcok Hrwc Hca HS Hp
    ipureintro; exact ⟨hc, hL, Hb⟩
  iexact HΦ

/-- The stream's bound: at most `L` bytes delivered. -/
theorem crHead_bound (cr : Loc) (γ : CrNames) (γe : GName) (cn : Nat) (P Q : Proto GF) (L : Nat)
    (c : Loc) (hL : L + 2 ^ 12 < 2 ^ 62) :
    ⊢ (□ ∀ r', crHead cr γ γe cn P Q L c r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) := by
  imodintro
  iintro %r' HS
  iunfold crHead at HS
  icases HS with ⟨-, %Hr, -⟩
  ipureintro; omega

end lemmas

end net.http
end Perennial
