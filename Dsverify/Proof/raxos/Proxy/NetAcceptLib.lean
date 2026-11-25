/-
Package `proxy`: lemmas of the accept routine (`waitForConnections`): the proxy's wildcard
address, the listener's invariant (taken with the exclusive `netTok γ k`), the client's handshake,
and the errors it prints (`errAny`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs
public import Dsverify.Proof.raxos.Proposer.Strings
public import Perennial.Proof.errors.NewVar
public import GooseLang.Ext.Net.Decide
public import Net.Proof.net.OpErrorMsg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

theorem proxyLis_1 : proxyLis 1 = go!"0.0.0.0:7607" := by
  unfold proxyLis
  rw [prop.decStr_four _ 7 6 0 7 '7' '6' '0' '7' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem proxyLis_2 : proxyLis 2 = go!"0.0.0.0:7608" := by
  unfold proxyLis
  rw [prop.decStr_four _ 7 6 0 8 '7' '6' '0' '8' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem proxyLis_3 : proxyLis 3 = go!"0.0.0.0:7609" := by
  unfold proxyLis
  rw [prop.decStr_four _ 7 6 0 9 '7' '6' '0' '9' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem proxyLis_4 : proxyLis 4 = go!"0.0.0.0:7610" := by
  unfold proxyLis
  rw [prop.decStr_four _ 7 6 1 0 '7' '6' '1' '0' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem proxyLis_5 : proxyLis 5 = go!"0.0.0.0:7611" := by
  unfold proxyLis
  rw [prop.decStr_four _ 7 6 1 1 '7' '6' '1' '1' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

/-- Proxy `k`'s wildcard is a valid listening address. -/
theorem proxyLis_listenOk (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) : listenOk (proxyLis k) = true := by
  obtain ⟨h1, h5⟩ := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [proxyLis_1]; decide
  · rw [proxyLis_2]; decide
  · rw [proxyLis_3]; decide
  · rw [proxyLis_4]; decide
  · rw [proxyLis_5]; decide

/-- The first four bytes of a stream the proxy's port's protocol allows are the client's
handshake. -/
theorem hs_of_prefix (n : Nat) (data ext rest : List w8) (h1 : data <+: ext)
    (h2 : ext <+: hs n ++ rest) (hl : data.length = 4) : data = hs n := by
  have h3 : data <+: hs n ++ rest := h1.trans h2
  have h4 : hs n <+: hs n ++ rest := List.prefix_append _ _
  rcases List.prefix_of_prefix_length_le h3 h4 (by simp [hl, hs]) with h
  exact List.IsPrefix.eq_of_length h (by simp [hl, hs])

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

instance netOwn_timeless (pr rm : Loc) : Timeless (netOwn (GF := GF) pr rm) := by
  unfold netOwn; infer_instance

/-- The accept routine takes the listener's state with its exclusive token (a second caller
cannot: `netTok_excl`). -/
theorem net_claim (γ : QNames) (k : Nat) (pr rm : Loc) :
    ⊢ inv netN iprop(netOwn (GF := GF) pr rm ∨ netTok γ k) -∗ netTok γ k ={⊤}=∗ netOwn pr rm := by
  iintro #Hi Htok
  iinv Hi with (>Hown | >Htok') Hclose
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro; iexact Hown
  · iexfalso
    iapply netTok_excl γ k $$ [$Htok $Htok']

omit π qv in
theorem opError_ptr_isError' [net.Assumptions] :
    go.typeSetContains (go.GoType.PointerType net.OpError.ty) go.error = true := by
  go_type_set

omit π qv in
theorem errorString_ptr_isError' [errors.Assumptions] :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

omit π qv in
theorem opError_ptr_notFormatter [net.Assumptions] [fmt.Assumptions] :
    go.typeSetContains (go.GoType.PointerType net.OpError.ty) fmt.Formatter.ty = false := by
  go_type_set

omit π qv in
theorem errorString_ptr_notFormatter [errors.Assumptions] [fmt.Assumptions] :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) fmt.Formatter.ty = false := by
  go_type_set

omit π qv in
/-- A failure's error (`resErr (some k)`, an `*OpError`) is not a `fmt.Formatter`, and is
`errAny` (`net.rpc.errAny_resErr`). -/
theorem errAny_resErr' [net.Assumptions] [fmt.Assumptions] (k : NetErr) (op : GoString)
    (src addr : GoInterface) (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    syscall.errnoOk (GF := GF) ⊢ net.resErr (some k) op src addr ed nm err -∗
      ⌜∀ ii, err = interface.ok ii → go.typeSetContains ii.ty fmt.Formatter.ty = false⌝ ∗
        models_lab.errAny err := by
  unfold net.resErr net.opErr
  iintro #Hsys ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -, #Hes, #Hs, #Ha⟩
  subst Herr
  ihave #Hok : net.opErrMsgOk (GF := GF) (net.OpError.mk op nw src addr e) $$ []
  · unfold net.opErrMsgOk; iframe Hes Hs Ha
  isplitr
  · ipureintro; intro ii hii; cases hii; exact opError_ptr_notFormatter
  unfold models_lab.errAny
  iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact opError_ptr_isError'
  imodintro
  iintro %Φ HΦ
  iapply net.wp_OpError_Error $$ Hpe Hok Hsys
  inext
  iintro %msg -
  iapply HΦ

omit π qv in
/-- An `errors.New` variable's value is not a `fmt.Formatter`, and is `errAny`
(`net.rpc.errAny_newVar`). -/
theorem errAny_newVar' [errors.Assumptions] [fmt.Assumptions] (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗
      ⌜∀ ii, e = interface.ok ii → go.typeSetContains ii.ty fmt.Formatter.ty = false⌝ ∗
        models_lab.errAny e := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩ #He
  icombine He Hx gives %Heq
  subst Heq
  isplitr
  · ipureintro; intro ii hii; cases hii; exact errorString_ptr_notFormatter
  unfold models_lab.errAny
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

omit π qv in
/-- A failed `io.ReadFull` of a connection: its error (`io.EOF`, `io.ErrUnexpectedEOF`, or a read
`*OpError`) is not a `fmt.Formatter`, and is `errAny`. -/
theorem readFull_errAny [net.Assumptions] [errors.Assumptions] [_root_.Perennial.io.Assumptions]
    [fmt.Assumptions]
    (eof ueof la ra ed : GoInterface) (r ys : List w8) (m : Nat) (err : GoInterface)
    (hne : err ≠ interface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ syscall.errnoOk ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      _root_.Perennial.io.readFullRes (net.connReadE eof la ra ed) eof ueof r ys m err ⊢
      ⌜∀ ii, err = interface.ok ii → go.typeSetContains ii.ty fmt.Formatter.ty = false⌝ ∗
        models_lab.errAny err := by
  iintro ⟨#Hio, #Hsys, #Heof, #Hueof, #Hres⟩
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  iunfold _root_.Perennial.io.readFullRes at Hres
  icases Hres with (%h | ⟨%e, %h, #HE⟩)
  · exact absurd h.2 hne
  obtain ⟨-, hen, h1, h2⟩ := h
  by_cases hc : e = eof ∧ ys ≠ []
  · rw [h1 hc]; iapply errAny_newVar' $$ HUEOF Hueof
  · rw [h2 hc]
    iunfold net.connReadE at HE
    icases HE with (%Hee | ⟨%k, #Hk⟩)
    · subst Hee; iapply errAny_newVar' $$ HEOF Heof
    · iapply errAny_resErr' $$ Hsys Hk

end lemmas

end Perennial.raxos
