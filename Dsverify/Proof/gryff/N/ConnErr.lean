/-
# Unit N: a connection reader's errors

What the replica's read loops (`serveClient`, `replicaListener`, `clientListener`) need of an error
a `*bufio.Reader` over a connection returns (`wire.rdErr` at the connection's reader state
`connRSt t eof la ra ed`: `io.EOF`'s value, a read `*OpError`, or one of the `io` / `bufio` /
`encoding/binary` package errors): that it is an error whose `Error()` returns
(`models_lab.errAny`, for `log.Printf("… %v", err)`) and that it is pointer-typed
(`io.ptrTyped`, for the comparison `err != io.EOF`): `rdErr_conn`.

`encoding/binary`'s `errOverflow` (from `ReadVarint`/`ReadUvarint`, `wire.BinaryVarintHyps`) is
not described by Perennial's `binary` package facts: the lemma takes `errors.newVar errOverflow m`
(true of Go: `var errOverflow = errors.New("binary: varint overflows a 64-bit integer")`) as a
premise (`rdErr_conn`), which `BinaryVarintHyps.errOverflowVar` gives (`rdErr_conn'`).
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.VarintWp
public import Net.Proof.net.ConnIo
public import Net.Proof.net.Errors
public import Perennial.Proof.errors.NewVar
public import Net.Proof.models_lab.Errors
public import GooseLang.Ext.Net.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.Assumptions]

/-- The reader state of a connection `*TCPConn` `t` (`net.conn_readerOk`'s contract). -/
abbrev connRSt (t : Loc) (eof la ra ed : GoInterface) : wire.RSt GF :=
  ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩

theorem errorString_ptr_isError' :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

theorem opError_ptr_isError' :
    go.typeSetContains (go.GoType.PointerType Perennial.net.OpError.ty) go.error = true := by
  go_type_set

/-- An `errors.New` variable's value is `errAny` and a pointer. -/
theorem newVar_errAny (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗
      models_lab.errAny e ∗ ⌜_root_.Perennial.io.ptrTyped e⌝ := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  isplitl
  · unfold models_lab.errAny
    iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact errorString_ptr_isError'
    imodintro
    iintro %Φ HΦ
    iapply HE
    inext
    iapply HΦ
  · ipureintro
    intro ii T h _
    cases h
    exact ⟨x, rfl⟩

/-- Any `*OpError` whose fields are persistent is `errAny` (its `Error()`, the net model's, reads
them and returns a message of Go's form: `net.wp_OpError_Error`). -/
theorem opErrPtr_errAny (pe : Loc) (v : Perennial.net.OpError) :
    (pe ↦□ v : IProp GF) ⊢ models_lab.errAny (GF := GF)
      (interface.mkOk (go.GoType.PointerType Perennial.net.OpError.ty) #pe) := by
  iintro #Hpe
  unfold models_lab.errAny
  iexists ⟨go.GoType.PointerType Perennial.net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError'
  imodintro
  iintro %Φ HΦ
  iapply Perennial.net.wp_OpError_Error $$ Hpe
  inext
  iintro %msg -
  iapply HΦ

/-- See the file header. -/
theorem rdErr_conn (t : Loc) (eof la ra ed : GoInterface) (err : GoInterface) (m : GoString) :
    wire.rdErr (connRSt t eof la ra ed) err ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
        errors.newVar (GF := GF) encoding.binary.errOverflow m ⊢
      models_lab.errAny err ∗ ⌜_root_.Perennial.io.ptrTyped err⌝ := by
  unfold wire.rdErr
  iintro ⟨⟨-, #Hr⟩, #Hio, #Heof, #Hov⟩
  ihave Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, #HSB, #HEOF, #HUE, #HNP, -⟩
  icases Hr with (⟨%r, Hr⟩ | #H | #H | #H)
  · unfold EtcdGrove.bufio.errE connRSt Perennial.net.connReadE
    icases Hr with ((%He | ⟨%k, Hk⟩) | #H)
    · subst He
      iapply newVar_errAny $$ HEOF Heof
    · unfold Perennial.net.resErr Perennial.net.opErr
      icases Hk with ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -⟩
      subst Herr
      isplitl
      · iapply opErrPtr_errAny $$ Hpe
      · ipureintro
        intro ii T h _
        cases h
        exact ⟨pe, rfl⟩
    · iapply newVar_errAny $$ HNP H
  · iapply newVar_errAny $$ HUE H
  · iapply newVar_errAny $$ HSB H
  · iapply newVar_errAny $$ Hov H

/-- `rdErr_conn` with `errOverflow` from `BinaryVarintHyps`. -/
theorem rdErr_conn' [wire.BinaryVarintHyps GF] (t : Loc) (eof la ra ed : GoInterface)
    (err : GoInterface) :
    wire.rdErr (connRSt t eof la ra ed) err ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        globalAddr _root_.Perennial.io.EOF ↦□ eof ⊢
      models_lab.errAny err ∗ ⌜_root_.Perennial.io.ptrTyped err⌝ := by
  iintro ⟨#Hr, #Hio, #Hb, #Heof⟩
  ihave #Hov := wire.BinaryVarintHyps.errOverflowVar (GF := GF) $$ Hb
  iapply rdErr_conn $$ [$Hr $Hio $Heof $Hov]

end

end Perennial.gryff.netN
