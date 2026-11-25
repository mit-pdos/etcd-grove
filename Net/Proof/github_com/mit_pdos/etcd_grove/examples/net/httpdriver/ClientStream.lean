/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the client's connection, as the stream `ReadResponse` reads

The client's end of a connection `cn` it dialed to the server (`drvAddr`), registered in the
connection registry (`http_register`: its slots are the mono-list `γ`, `httpConn cn γ`), read through a
`*bufio.Reader` as a stream reader (`hcStream`, over `Conn.Read.specLc`) of the state `hcSt cn γ γe`:
what was read meets the server's protocol (`httpRespP drvP`, its fact without a later, kept as in
`DialHTTPPath`'s `crSt`), half of the slots' mono-list (at most `4` slots: what bounds the stream, with
`respFacts`' head bound), and after a read error nothing more is read (`γe`, `hcErr`, `readDead`).

The laws `ReadResponse.spec_resp` takes of the stream (`hcSt_bound`, `hcErr_final`, `hcSt_law`: what is
read past the answers already delivered, `D`, is the wire of the next answer, which answers the slot at
its index, `drvQ`); the lower bound of the server's bytes a reader has delivered (`ownReader_hcLb`);
adding a slot to the mono-list while the reader holds half of it (`ownReader_addSlot`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas
public import Net.Spec.net.Conn__Read
public import Net.Proof.net.ConnIo
public import GooseLang.Ext.Net.Stream
public import Proof.io.ReaderStreamNE
public import Proof.bufio.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [net.Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The client's read state of `cn` at `r` (see the file header). -/
def hcSt (cn : Nat) (γ γe : GName) (r : List w8) : IProp GF :=
  iprop(recvTok (Gg := hG.goose_globalGS) cn false (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) r ∗
    rdlTok (Gg := hG.goose_globalGS) cn false false ∗
    net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
    (∃ L : List ReqSlot, monoListAuthOwn γ (1 : Qp).half L ∗ ⌜L.length ≤ 4⌝) ∗
    ((monoListAuthOwn γe 1 [r] ∗ readDead (Gg := hG.goose_globalGS) cn false) ∨
      monoListAuthOwn γe 1 ([] : List (List w8))))

/-- The evidence of a read error at `r` (persistent). -/
def hcErr (γe : GName) (r : List w8) (_err : GoInterface) : IProp GF :=
  monoListLbOwn γe [r]

instance hcErr_persistent (γe : GName) (r : List w8) (err : GoInterface) :
    Persistent (hcErr (GF := GF) γe r err) := by
  unfold hcErr; infer_instance

/-- The server has written at least `D` on `cn` (persistent). -/
def hcLb (cn : Nat) (D : List w8) : IProp GF := sentLb (Gg := hG.goose_globalGS) cn true D

instance hcLb_persistent (cn : Nat) (D : List w8) : Persistent (hcLb (GF := GF) cn D) := by
  unfold hcLb; infer_instance

/-- Registering a dialed connection: its fresh token given up to the registry, its slots a new
mono-list. -/
theorem http_register (cn : Nat) :
    inv net.http.httpRegN (net.http.httpRegInv (Gg := hG.goose_globalGS)) ∗
      connFresh (Gg := hG.goose_globalGS) cn false ⊢
    |={⊤}=> ∃ γ : GName, net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
      monoListAuthOwn γ 1 ([] : List ReqSlot) := by
  sorry

/-- The state at the start: nothing read, no slot. -/
theorem hcSt_init (cn : Nat) (γ : GName) :
    recvTok (Gg := hG.goose_globalGS) cn false (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) [] ∗
      rdlTok (Gg := hG.goose_globalGS) cn false false ∗
      net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗ monoListAuthOwn γ (1 : Qp).half ([] : List ReqSlot) ⊢
    |==> ∃ γe : GName, hcSt cn γ γe [] := by
  sorry

/-- The client's end of `cn` is a stream reader over `hcSt` (see the file header). -/
theorem hcStream (wp_Read : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (cn : Nat) (γ γe : GName) (t : Loc) (la ra : GoInterface) (ed : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      net.connAt (GF := GF) t cn false addrS la ra ⊢
    EtcdGrove.io.readerStreamNE (net.connIface t) (hcSt cn γ γe) (hcErr γe) := by
  sorry

/-- `bufio.NewReader`'s law. -/
theorem hcSt_bound (cn : Nat) (γ γe : GName) (r : List w8) :
    hcSt cn γ γe r ⊢ ⌜r.length + 2 ^ 12 < 2 ^ 62⌝ := by
  sorry

/-- After an error at `r`, the stream stays at `r`. -/
theorem hcErr_final (cn : Nat) (γ γe : GName) (r r' : List w8) (err : GoInterface) :
    hcErr γe r err ∗ hcSt cn γ γe r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  sorry

/-- **What `ReadResponse` reads next**: past the answers `A` delivered (`D`, the server's bytes so far),
a prefix of the wire of the answer at index `A.length`, or, for one delimited by its `Content-Length`,
that wire and more; and what the client knows of it (`drvQ`), the slots being at least `L`. -/
theorem hcSt_law (cn : Nat) (γ γe : GName) (D : List w8) (A : List Resp) (L : List ReqSlot)
    (hD : D = net.http.respsWire (A.map RespSlot.ans))
    (hA : ∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false) (hL : A.length < L.length) :
    hcLb cn D ∗ monoListLbOwn γ L ⊢
    □ ∀ r, hcSt cn γ γe r -∗ ⌜r <+: D⌝ ∨ ∃ ρ : Resp, ⌜net.http.respOk ρ ∧
        (r <+: D ++ net.http.respWire ρ ∨ (ρ.close = false ∧ D ++ net.http.respWire ρ <+: r))⌝ ∗
      □ drvQ L A.length ρ := by
  sorry

/-- A reader over `hcSt` has delivered bytes the server wrote. -/
theorem ownReader_hcLb (b : Loc) (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF)
    (cn : Nat) (γ γe : GName) (D : List w8) :
    EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ⊢
      EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗ hcLb cn D := by
  sorry

/-- A slot added to the mono-list, the reader holding its other half (at most `4` slots). -/
theorem ownReader_addSlot (b : Loc) (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF)
    (cn : Nat) (γ γe : GName) (D : List w8) (L : List ReqSlot) (s : ReqSlot) (hL : L.length < 4) :
    EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗ monoListAuthOwn γ (1 : Qp).half L ⊢
      |==> EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗
        monoListAuthOwn γ (1 : Qp).half (L ++ [s]) := by
  sorry

end defs

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
