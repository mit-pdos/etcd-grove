/-
The proof of `Client.input` (`Net/Spec/net/rpc/Client__input.lean`), the client's reader loop.

**The loop's invariant**: `err` is `nil` with the reader's resources (`readerOwn`: the frames of
the answers `C` read, and the shutdown flag's quarter at `false`), or a read failed and `err` is
an `inErr` error (not `nil`, not a `ServerError`, a pointer, with an `Error()`) with the quarter.
**An iteration**: the header read (`ReadResponseHeader`, through `recvTokL` and `read_au`:
`rd_acc`), the entry for its sequence number removed under `mutex` (`muInv`, not shut down: the
quarter agrees), then
* no entry: the body discarded;
* an error response: the answer the header heads (`resp_hdr`, `hdr_match`), the call's collection
  token traded for the method's answer and `reqSent` (`ans_trade`), the body discarded, the call
  done with `ServerError(msg)`;
* otherwise: the answer the header heads and the trade first (as for an error response), then the
  body decoded into the reply (`ReadResponseBody` with the call's `D` and the method's answer
  `Φ reply ""`, guarded by `body_guard`: the frame read is that answer's reply, so the call's
  decoding obligation, asked only of the method's answers, applies), the answer it is
  (`resp_body`), the call done with `nil` (decoded) or a new `errors.New` error (a decoding error,
  or a read error with `D` back).
A body read that succeeded extends `C` by the answer (`framesOf_snoc`); a failure leaves `err` an
`inErr` error (`inErr_read`, `inErr_dec`, `inErr_errorString`; `errors.New` through
`wp_errors_New'`, which names its result's type). Each iteration takes four later credits: the
header's and the body's protocol facts, and the trade's two.
**After the loop** (the `break` after a failed header read, or the condition false; one proof for
both, `all_goals`): both locks, the shutdown flag set from all its fractions (`muInv`'s half,
`sendInv`'s quarter and the reader's), `err == io.EOF` (a pointer comparison: four outcomes, the
`io.EOF` one replaced by `ErrShutdown` or `io.ErrUnexpectedEOF`), then every pending call failed
with `err` and its `D` (`wp_map_for_range` over `pending`, the entries not yet visited as the
range's resource, `rem_step`); `debugLog` is `false`.
-/
module

public import Net.Spec.net.rpc.Client__input
public import Net.Spec.net.rpc.Call__done
public import Net.Spec.net.rpc.clientCodec__ReadResponseHeader
public import Net.Spec.net.rpc.clientCodec__ReadResponseBody
public import Net.Proof.net.rpc.ClientRead
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.errors.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

theorem respHdr_length (seq : w64) (sm e : GoString) :
    (respHdr seq sm e).length = sm.length + e.length + 24 := by
  simp [respHdr, strEnc_length, u64Le_length]; omega

/-- An answer whose header is the one read (at most a frame): it answers that sequence number,
with that error message. -/
theorem hdr_match (x : Ans) (seq : w64) (sm e : GoString)
    (hx : respHdr (W64 x.idx) x.sm x.msg = respHdr seq sm e)
    (hl : (respHdr seq sm e).length ≤ maxFrameN) (hok : ansOk x) :
    x.idx = uint.nat seq ∧ x.msg = e := by
  have hl' := hl
  rw [← hx] at hl'
  rw [respHdr_length] at hl hl'
  unfold maxFrameN at hl hl'
  obtain ⟨h1, -, h3⟩ := respHdr_inj (by omega) (by omega) (by omega) (by omega) hx
  refine ⟨?_, h3⟩
  subst h1
  have := hok.2.2
  word

/-- One step of a range over a map's keys: the entries left are those of the keys not yet
visited. -/
theorem rem_step {V : Type} (keys : List w64) (m m' : GMap w64 V) (i : Int) (k : w64)
    (hi : 0 ≤ i) (hk : keys[i.toNat]? = some k) (hnd : keys.Nodup)
    (h : ∀ k', m' !! k' = if k' ∈ keys.take i.toNat then none else m !! k') :
    m' !! k = m !! k ∧
      ∀ k', (GMap.delete k m') !! k' = if k' ∈ keys.take (i + 1).toNat then none else m !! k' := by
  obtain ⟨hlt, hkv⟩ := List.getElem?_eq_some_iff.1 hk
  have hd : keys.drop i.toNat = k :: keys.drop (i.toNat + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hkv]
  have hnot : k ∉ keys.take i.toNat := by
    intro hm
    have he := List.take_append_drop i.toNat keys
    rw [hd] at he
    rw [← he] at hnd
    exact (List.nodup_append.1 hnd).2.2 k hm k List.mem_cons_self rfl
  have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [k] := by
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk]
    rfl
  refine ⟨by rw [h k]; simp [hnot], fun k' => ?_⟩
  by_cases hkk : k = k'
  · subst hkk; rw [GMap.lookup_delete, htake]; simp
  · rw [GMap.lookup_delete_ne _ hkk, h k', htake]
    simp [List.mem_append, Ne.symm hkk]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions] [errors.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The reader's error once a read failed: not `nil`, not a `ServerError`, a pointer (which
`err == io.EOF` compares), with an `Error()` (persistent). -/
def inErr (e : GoInterface) : IProp GF :=
  iprop(⌜e ≠ interface.nil ∧ notServerErr e ∧
      ∃ (T : go.GoType) (l : Loc), e = interface.mkOk (go.GoType.PointerType T) #l⌝ ∗
    models_lab.errAny e)

instance inErr_persistent (e : GoInterface) : Persistent (inErr (GF := GF) e) := by
  unfold inErr; infer_instance

theorem inErr_newVar (X msg : GoString) (e : GoInterface) :
    errors.newVar (GF := GF) X msg ⊢ globalAddr X ↦□ e -∗ inErr e := by
  iintro #Hv #He
  ihave #Ha := errAny_newVar X msg e $$ Hv He
  iunfold errors.newVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  icombine He Hx gives %Heq
  subst Heq
  unfold inErr
  iframe Ha
  ipureintro
  exact ⟨by simp [interface.mkOk], notServerErr_errorString x, _, x, rfl⟩

/-- A read's failure (`ReadResponseHeader`'s, `ReadResponseBody`'s) is `inErr`. -/
theorem inErr_read (la ra eof ueof ed ef : GoInterface) (first : Bool) (got : List w8)
    (err : GoInterface) :
    errors.newVar (GF := GF) net.rpc.errFrame go!"rpc: malformed frame" ∗
      globalAddr net.rpc.errFrame ↦□ ef ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      (⌜err = ef⌝ ∨ readErr la ra eof ueof ed first got err) ⊢ inErr err := by
  iintro ⟨#HefV, #Hef, #Hio, #Heof, #Hueof, #HE⟩
  icases HE with (%He | #HE)
  · subst He; iapply inErr_newVar $$ HefV Hef
  unfold readErr
  icases HE with (⟨%He, -⟩ | %He | ⟨%k, #HE⟩)
  · subst He
    ihave #HEOF := io.eof_of_init $$ Hio
    iapply inErr_newVar $$ HEOF Heof
  · subst He
    ihave #Hi := io.isInit_access $$ Hio
    icases Hi with ⟨-, -, -, -, -, #HU, -⟩
    iapply inErr_newVar $$ HU Hueof
  · ihave #Ha := errAny_resErr $$ HE
    ihave %Hns := notServerErr_resErr $$ HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    unfold inErr
    iframe Ha
    ipureintro
    exact ⟨by simp [interface.mkOk], Hns, _, pe, rfl⟩

/-- An `*errorString` with its `Error()` is `inErr`. -/
theorem inErr_errorString (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
      inErr (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  ihave #Ha := errAny_errorString x msg $$ H
  unfold inErr
  iframe Ha
  ipureintro
  exact ⟨by simp [interface.mkOk], notServerErr_errorString x, _, x, rfl⟩

/-- A decoding error is `inErr`. -/
theorem inErr_dec (err : GoInterface) : decErr (GF := GF) err ⊢ inErr err := by
  unfold decErr
  iintro ⟨%x, %msg, ⟨%He, -⟩, #H⟩
  subst He
  iapply inErr_errorString x msg $$ H

/-- `err.Error()` of an `inErr` error. -/
theorem wp_inErr_Error (T : go.GoType) (l : Loc) (Φ : val → IProp GF) :
    inErr (interface.mkOk (go.GoType.PointerType T) #l) ⊢ ▷ (∀ msg : GoString, Φ #msg) -∗
      WP (App (Val #(methods (go.GoType.PointerType T) go!"Error" #l)) (Val #())) {{ Φ }} := by
  unfold inErr
  iintro ⟨-, #Ha⟩ HΦ
  unfold models_lab.errAny
  icases Ha with ⟨%e, %He, -, #HW⟩
  cases He
  iapply HW $$ HΦ

theorem framesOf_snoc (C : List Ans) (y : Ans) (hdr b : List w8) (hy : ansPls y = [hdr, b]) :
    framesOf ((C ++ [y]).flatMap ansPls) = framesOf (C.flatMap ansPls) ++ frameOf hdr ++ frameOf b := by
  rw [List.flatMap_append, framesOf_append, List.flatMap_singleton, hy, framesOf_cons, framesOf_cons,
    framesOf_nil, List.append_nil, List.append_assoc]

/-- The reader predicate of a read after `R0`, and its accessor (`read_au`). -/
theorem rd_acc (W : RpcWorld GF) (a : GoString) (cn : Nat) (R0 : List w8) :
    ⊢ □ (∀ (got : List w8) (m : Nat),
      recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
        (R0 ++ got) -∗
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!false) d ∗
        ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false st -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!false) d' ={∅,⊤}=∗
            recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
              (R0 ++ (got ++ r.got))) := by
  imodintro
  iintro %got %m HP
  imod read_au (Gg := hG.goose_globalGS) cn false _ _ m $$ HP with ⟨%st, %d, Hst, Hd, Hk⟩
  imodintro
  iexists st, d
  iframe Hst Hd
  iintro %r %d' %Hro Hst Hd
  imod Hk $$ %r %d' %Hro Hst Hd with ⟨HP, -⟩
  imodintro
  rw [← List.append_assoc]
  iexact HP

/-- The guard of a reply's body read (`ReadResponseBody`'s): after a success header naming request
`seq`, answered with the reply `r` (its `ans` element), the body frame read is that reply's, one
step later. -/
theorem body_guard (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (C : List Ans)
    (seq : w64) (sm : GoString) (r : List w8) (hC : ∀ x ∈ C, ansOk x)
    (hl : (respHdr seq sm []).length ≤ maxFrameN) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
      ghostMapElem γ.ans (uint.nat seq) .discard (some (([] : GoString), r)) ⊢
    □ (∀ pl : List w8, ⌜pl.length ≤ maxFrameN⌝ -∗
      recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
        ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm [])) ++ frameOf pl) -∗
      ▷ (recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
          ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm [])) ++ frameOf pl) ∗
        ⌜pl = r⌝)) := by
  iintro ⟨#Hrpc, #Hans⟩
  imodintro
  iintro %pl %Hpl HP
  ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
  inext
  icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrL with ⟨HrT, #Hpp⟩
  icases resp_body W a cn γ C (respHdr seq sm []) pl hC
    (by unfold maxFrameN at hl; omega) (by unfold maxFrameN at Hpl; omega) $$ [$Hrpc $Hpp]
    with ⟨%y, ⟨%Hy, %Hyok⟩, #Hye⟩
  have hy0 : respHdr (W64 y.idx) y.sm y.msg = respHdr seq sm [] := by
    simp only [ansPls, List.cons.injEq] at Hy; exact Hy.1
  obtain ⟨hyi, hym⟩ := hdr_match y seq sm [] hy0 hl Hyok
  have hyr : y.reply = pl := by
    simp only [ansPls, List.cons.injEq, hym, ite_true] at Hy; exact Hy.2.1
  ihave #Hy3 : ghostMapElem γ.ans (uint.nat seq) .discard (some (y.msg, y.reply)) $$ []
  · rw [← hyi]; iexact Hye
  ihave %Hag := ghostMapElem_agree _ _ _ _ _ _ $$ Hans Hy3
  isplitl [HrT]
  · iapply recvTok_L $$ HrT
  ipureintro
  simp only [Option.some.injEq, Prod.mk.injEq] at Hag
  rw [← hyr, Hag.2]

theorem Client.input.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_ReadResponseHeader : clientCodec.ReadResponseHeader.spec (GF := GF) (hG := hG))
    (wp_ReadResponseBody : clientCodec.ReadResponseBody.spec (GF := GF) (hG := hG))
    (wp_done : Call.done.spec (GF := GF) (hG := hG)) :
    Client.input.spec (GF := GF) (hG := hG) := by
  intro c W a γ cc t cn la ra
  wp_start as ⟨#Hc, Hrd⟩
  iunfold clientAt at Hc
  icases Hc with ⟨#Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, #Henv, #Hsmu, #Hmu⟩
  ihave #Henv' := Henv
  unfold cliEnv
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #HefV' := HefV
  iunfold errors.newVar at HefV'
  icases HefV' with ⟨%xf, #Hef, -⟩
  wp_auto
  ihave HI : (∃ (e : GoInterface) (rv : net.rpc.Response), "err" ∷ err_ptr ↦ e ∗
      "response" ∷ response_ptr ↦ rv ∗
      "Hst" ∷ ((⌜e = interface.nil⌝ ∗ readerOwn γ cn W a) ∨
        (inErr e ∗ ghostVar γ.down (1 : Qp).half.half false)) : IProp GF) $$ [err response Hrd]
  · iexists interface.nil, _
    iframe err response
    ileft
    iframe Hrd
    ipureintro; rfl
  wp_for HI
  icases Hst with (⟨%He, Hrd⟩ | ⟨#He, Hdq⟩)
  -- the loop body
  subst He
  wp_auto
  rw [decide_eq_true rfl]; simp only [↓reduceIte]
  wp_auto
  iunfold readerOwn at Hrd
  icases Hrd with ⟨%C, Hrecv, Hdq, %HC⟩
  ihave HrL : recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
      (framesOf (C.flatMap ansPls) ++ []) $$ [Hrecv]
  · rw [List.append_nil]; iapply recvTok_L $$ Hrecv
  ihave #Hacc := rd_acc W a cn (framesOf (C.flatMap ansPls))
  wp_apply wp_ReadResponseHeader cc t cn false a la ra response_ptr _
      (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
        (respProto (Gg := hG.goose_globalGS) W a) (framesOf (C.flatMap ansPls) ++ got))
      eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $response $HrL $Hacc]
    as %err ⟨%got, HP, Hres⟩
  icases Hres with (⟨%seq, %sm, %e, ⟨%Hnil, %Hgot, %Hlen⟩, Hr⟩ | ⟨%Hne, Hr, #HE⟩)
  · subst Hnil Hgot
    wp_auto_lc 4
    wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
    iunfold muInv at Hinv
    icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
      %Hb, Hdown, Hnm, %HNM, Hrest⟩
    ihave %Hda := ghostVar_agree $$ Hdq Hdown
    obtain ⟨-, rfl⟩ := Hda
    simp only [Bool.false_eq_true, ite_false]
    wp_auto
    wp_apply (wp_map_lookup1 (K := w64) (V := Loc) go.uint64
      (go.GoType.PointerType net.rpc.Call.ty) mp m seq (DFrac.own 1)) $$ Hmp as Hmp
    wp_apply (wp_mapDelete (K := w64) (V := Loc) mp m seq go.uint64
      (go.GoType.PointerType net.rpc.Call.ty)) $$ Hmp as Hmp
    cases hlk : m.lookup seq with
    | none =>
      rw [GMap.delete_notin _ _ hlk]
      wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr
          Hdown Hnm Hrest]
      · iunfold muInv
        iexists sq, n, mp, m, false, cls, NM
        iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        isplitr
        · ipureintro; exact Hb
        isplitr
        · ipureintro; exact HNM
        simp only [Bool.false_eq_true, ite_false]
        iexact Hrest
      ihave #Hacc1 := rd_acc W a cn (framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e))
      ihave HP1 : recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
          ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ []) $$ [HP]
      · rw [List.append_nil]; iexact HP
      wp_apply wp_ReadResponseBody cc t cn false a la ra interface.nil
          ⟨fun _ _ => iprop(True), fun _ _ _ => iprop(True), fun _ _ => iprop(True)⟩ iprop(True)
          (fun _ => iprop(True)) (fun _ _ => iprop(True))
          (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
            (respProto (Gg := hG.goose_globalGS) W a)
            ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ got))
          eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $HP1 $Hacc1]
        as %err1 ⟨%got1, HP, Hres⟩
      · simp only [bodyDecG]
        isplitl []
        · itrivial
        iapply guard_true (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
            (respProto (Gg := hG.goose_globalGS) W a)
            ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ got))
      icases Hres with (⟨%pl, ⟨%Hgot1, %Hpl⟩, Hbr⟩ | ⟨%Hne1, -, #HE1⟩)
      · unfold bodyRes
        icases Hbr with ⟨%He1, -⟩
        subst He1 Hgot1
        ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
        iapply fupd_wp
        imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrL with HrT
        icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
        icases resp_body W a cn γ.conn C (respHdr seq sm e) pl HC
          (by unfold maxFrameN at Hlen; omega) (by unfold maxFrameN at Hpl; omega) $$ [$Hrpc $Hpp]
          with ⟨%y, ⟨%Hy, %Hyok⟩, -⟩
        imodintro
        wp_auto
        wp_for_post
        iframe
        iexists interface.nil, _
        iframe err Hr
        ileft
        isplitr
        · ipureintro; rfl
        iunfold readerOwn
        iexists C ++ [y]
        rw [framesOf_snoc C y _ _ Hy]
        iframe HrT Hdq
        ipureintro
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact HC x hx
        · simp at hx; subst hx; exact Hyok
      · ihave #Hi := inErr_read la ra eof ueof ed _ true got1 err1 $$ [$HefV $Hef $Hio $Heof $Hueof $HE1]
        ihave #Hi' := Hi
        iunfold inErr at Hi'
        icases Hi' with ⟨%Hip, -⟩
        obtain ⟨-, -, T1, l1, rfl⟩ := Hip
        wp_auto
        wp_bind (App (Val #(methods (go.GoType.PointerType T1) go!"Error" #l1)) (Val #()))
        iapply wp_inErr_Error $$ Hi
        inext
        iintro %msg
        wp_auto
        wp_apply wp_errors_New' as %x #HN
        wp_for_post
        iframe
        iexists _, _
        iframe err Hr
        iright
        iframe Hdq
        iapply inErr_errorString $$ HN
    | some pc =>
      icases (BigSepM.bigSepM_delete (Φ := fun s pc => callRes (hG := hG) γ.conn s pc)
        (by rw [gmap_get?_eq]; exact hlk)).1 $$ Hrest with ⟨Hcr, Hrest⟩
      wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr
          Hdown Hnm Hrest]
      · iunfold muInv
        iexists sq, n, mp, _, false, cls, NM
        iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        isplitr
        · ipureintro; exact Hb
        isplitr
        · ipureintro; exact HNM
        simp only [Bool.false_eq_true, ite_false]
        iexact Hrest
      iunfold callRes at Hcr
      icases Hcr with ⟨%sm', %args', %reply', %ch', %γt', %γf', %K', %Φ', %Θ', %D', %C', %post',
        %col', %ap', #Hf2, Herr2, #Htk2, Hdone2, #Hpost2, Hcol2, #Hnm2, HD2, #Hdec2,
        ⟨%Hrep', %Hpc'⟩⟩
      rw [decide_eq_false Hpc']
      simp only [Option.getD_some]
      wp_auto
      by_cases he : e = []
      · rw [show decide (true = !decide (e = [])) = false from by simp [he]]
        subst he
        ihave #Hf2' := Hf2
        iunfold callFields at Hf2'
        icases Hf2' with ⟨#Hfsm, #Hfargs, #Hfrep, #Hfch⟩
        wp_auto
        -- the answer the header heads, and the call's continuation for it, before the body
        ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
        iapply fupd_wp
        imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrL with HrT
        icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
        icases resp_hdr W a cn γ.conn C (respHdr seq sm []) HC
          (by unfold maxFrameN at Hlen; omega) $$ [$Hrpc $Hpp] with ⟨%x, ⟨%Hx0, %Hxok⟩, #Hans⟩
        obtain ⟨hxi, hxm⟩ := hdr_match x seq sm [] (by simpa [ansPls] using Hx0) Hlen Hxok
        ihave #Hans3 : ghostMapElem γ.conn.ans (uint.nat seq) .discard (some ([], x.reply)) $$ []
        · rw [← hxi, ← hxm]; iexact Hans
        imod ans_trade W a cn γ.conn (uint.nat seq) [] x.reply post' col' ap' Φ'
          $$ [$Hrpc $Hlc2 $Hlc3 $Hans3 $Hcol2 $Hnm2 $Hpost2] with ⟨HΦr, #Hsent⟩
        imodintro
        ihave #Hacc1 := rd_acc W a cn (framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm []))
        ihave HP1 : recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
            ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm [])) ++ []) $$ [HrT]
        · rw [List.append_nil]; iapply recvTok_L $$ HrT
        ihave #Hguard := body_guard W a cn γ.conn C seq sm x.reply HC Hlen $$ [$Hrpc $Hans3]
        cases reply' with
        | nil => exact absurd rfl Hrep'
        | ok r' =>
        ihave #Hdec3 : bodyDecG C' (interface.ok r') (iprop(D' ∗ Φ' x.reply []))
            (fun pl => iprop(⌜pl = x.reply⌝)) Θ' $$ []
        · simp only [bodyDecG]
          icases Hdec2 with ⟨#Hset2, #Hd2⟩
          iframe Hset2
          imodintro
          iintro ⟨HD, HΦ⟩ %pl %Hplr
          subst Hplr
          iapply Hd2 $$ HD HΦ
        wp_apply wp_ReadResponseBody cc t cn false a la ra (interface.ok r') C'
            (iprop(D' ∗ Φ' x.reply [])) (fun pl => iprop(⌜pl = x.reply⌝)) Θ'
            (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
              (respProto (Gg := hG.goose_globalGS) W a)
              ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm [])) ++ got))
            eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $Hdec3 $HD2 $HΦr $HP1
              $Hguard $Hacc1]
          as %err1 ⟨%got1, HP, Hres⟩
        icases Hres with (⟨%pl, ⟨%Hgot1, %Hpl⟩, Hbr⟩ | ⟨%Hne1, ⟨HD2, -⟩, #HE1⟩)
        · subst Hgot1
          simp only [bodyRes]
          icases Hbr with ⟨%ok, %Hok, HΘ, Hdc⟩
          ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
          iapply fupd_wp
          imod lc_fupd_elim_later (E := ⊤) $$ Hlc4 HrL with HrT
          icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp'⟩
          icases resp_body W a cn γ.conn C (respHdr seq sm []) pl HC
            (by unfold maxFrameN at Hlen; omega) (by unfold maxFrameN at Hpl; omega) $$ [$Hrpc $Hpp']
            with ⟨%y, ⟨%Hy, %Hyok⟩, -⟩
          imodintro
          cases ok
          · simp only [Bool.false_eq_true, ite_false]
            ihave #Hi := inErr_dec $$ Hdc
            ihave #Hi' := Hi
            iunfold inErr at Hi'
            icases Hi' with ⟨%Hip, -⟩
            obtain ⟨-, -, T1, l1, rfl⟩ := Hip
            wp_auto
            wp_bind (App (Val #(methods (go.GoType.PointerType T1) go!"Error" #l1)) (Val #()))
            iapply wp_inErr_Error $$ Hi
            inext
            iintro %msg
            wp_auto
            wp_apply wp_errors_New' as %x' #HN
            ihave #Hi2 := inErr_errorString $$ HN
            ihave Hpost : callPost γ.conn (some (uint.nat seq)) Φ' Θ' D'
                (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x') $$ [HΘ]
            · iunfold callPost
              iright; iright
              iunfold inErr at Hi2
              icases Hi2 with ⟨%Hi2p, #Hi2a⟩
              iframe Hi2a
              isplitr
              · ipureintro; exact ⟨Hi2p.1, Hi2p.2.1⟩
              iright
              iframe Hsent
              iexists pl
              iexact HΘ
            wp_apply wp_done pc sm' args' (interface.ok r') ch' γ.conn γt' γf' K' Φ' Θ' D' _ _
                $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost $Herr2]
            wp_for_post
            iframe
            iexists _, _
            iframe err Hr
            iright
            iframe Hdq Hi
          · have He1 : err1 = interface.nil := Hok.2 rfl
            subst He1
            wp_auto
            ihave Hpost : callPost γ.conn (some (uint.nat seq)) Φ' Θ' D' interface.nil $$ [HΘ]
            · iunfold callPost
              ileft
              iframe Hsent
              isplitr
              · ipureintro; rfl
              iexists pl
              iexact HΘ
            wp_apply wp_done pc sm' args' (interface.ok r') ch' γ.conn γt' γf' K' Φ' Θ' D' _ _
                $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost $Herr2]
            wp_for_post
            iframe
            iexists interface.nil, _
            iframe err Hr
            ileft
            isplitr
            · ipureintro; rfl
            iunfold readerOwn
            iexists C ++ [y]
            rw [framesOf_snoc C y _ _ Hy]
            iframe HrT Hdq
            ipureintro
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact HC x hx
            · simp at hx; subst hx; exact Hyok
        · ihave #Hi := inErr_read la ra eof ueof ed _ true got1 err1 $$ [$HefV $Hef $Hio $Heof $Hueof $HE1]
          ihave #Hi' := Hi
          iunfold inErr at Hi'
          icases Hi' with ⟨%Hip, -⟩
          obtain ⟨-, -, T1, l1, rfl⟩ := Hip
          wp_auto
          wp_bind (App (Val #(methods (go.GoType.PointerType T1) go!"Error" #l1)) (Val #()))
          iapply wp_inErr_Error $$ Hi
          inext
          iintro %msg
          wp_auto
          wp_apply wp_errors_New' as %x' #HN
          ihave #Hi2 := inErr_errorString $$ HN
          ihave Hpost : callPost γ.conn (some (uint.nat seq)) Φ' Θ' D'
              (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x') $$ [HD2]
          · iunfold callPost
            iright; iright
            iunfold inErr at Hi2
            icases Hi2 with ⟨%Hi2p, #Hi2a⟩
            iframe Hi2a
            isplitr
            · ipureintro; exact ⟨Hi2p.1, Hi2p.2.1⟩
            ileft
            iexact HD2
          wp_apply wp_done pc sm' args' (interface.ok r') ch' γ.conn γt' γf' K' Φ' Θ' D' _ _
              $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost $Herr2]
          wp_for_post
          iframe
          iexists _, _
          iframe err Hr
          iright
          iframe Hdq Hi
      · rw [show decide (true = !decide (e = [])) = true from by simp [he]]
        wp_auto
        -- the answer the header heads, and the call's continuation for it
        ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
        iapply fupd_wp
        imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrL with HrT
        icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
        icases resp_hdr W a cn γ.conn C (respHdr seq sm e) HC
          (by unfold maxFrameN at Hlen; omega) $$ [$Hrpc $Hpp] with ⟨%x, ⟨%Hx0, %Hxok⟩, #Hans⟩
        obtain ⟨hxi, hxm⟩ := hdr_match x seq sm e (by simpa [ansPls] using Hx0) Hlen Hxok
        ihave #Hans3 : ghostMapElem γ.conn.ans (uint.nat seq) .discard (some (e, x.reply)) $$ []
        · rw [← hxi, ← hxm]; iexact Hans
        imod ans_trade W a cn γ.conn (uint.nat seq) e x.reply post' col' ap' Φ'
          $$ [$Hrpc $Hlc2 $Hlc3 $Hans3 $Hcol2 $Hnm2 $Hpost2] with ⟨HΦr, #Hsent⟩
        imodintro
        ihave #Hacc1 := rd_acc W a cn (framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e))
        ihave HP1 : recvTokL (Gg := hG.goose_globalGS) cn false (respProto (Gg := hG.goose_globalGS) W a)
            ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ []) $$ [HrT]
        · rw [List.append_nil]; iapply recvTok_L $$ HrT
        wp_apply wp_ReadResponseBody cc t cn false a la ra interface.nil
            ⟨fun _ _ => iprop(True), fun _ _ _ => iprop(True), fun _ _ => iprop(True)⟩ iprop(True)
          (fun _ => iprop(True)) (fun _ _ => iprop(True))
            (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
              (respProto (Gg := hG.goose_globalGS) W a)
              ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ got))
            eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $HP1 $Hacc1]
          as %err1 ⟨%got1, HP, Hres⟩
        · simp only [bodyDecG]
          isplitl []
          · itrivial
          iapply guard_true (fun got => recvTokL (Gg := hG.goose_globalGS) cn false
            (respProto (Gg := hG.goose_globalGS) W a)
            ((framesOf (C.flatMap ansPls) ++ frameOf (respHdr seq sm e)) ++ got))
        ihave Hpost : callPost γ.conn (some (uint.nat seq)) Φ' Θ' D' (serverErr e) $$ [HΦr HD2]
        · iunfold callPost
          iright; ileft
          iexists e
          iframe Hsent HD2
          isplitr
          · ipureintro; exact ⟨he, rfl⟩
          iexists x.reply
          iexact HΦr
        icases Hres with (⟨%pl, ⟨%Hgot1, %Hpl⟩, Hbr⟩ | ⟨%Hne1, -, #HE1⟩)
        · unfold bodyRes
          icases Hbr with ⟨%He1, -⟩
          subst He1 Hgot1
          ihave HrL := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HP
          iapply fupd_wp
          imod lc_fupd_elim_later (E := ⊤) $$ Hlc4 HrL with HrT
          icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp'⟩
          icases resp_body W a cn γ.conn C (respHdr seq sm e) pl HC
            (by unfold maxFrameN at Hlen; omega) (by unfold maxFrameN at Hpl; omega) $$ [$Hrpc $Hpp']
            with ⟨%y, ⟨%Hy, %Hyok⟩, -⟩
          imodintro
          wp_auto
          wp_apply wp_done pc sm' args' reply' ch' γ.conn γt' γf' K' Φ' Θ' D' _ (serverErr e)
              $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost Herr2]
          · unfold serverErr; iexact Herr2
          wp_for_post
          iframe
          iexists interface.nil, _
          iframe err Hr
          ileft
          isplitr
          · ipureintro; rfl
          iunfold readerOwn
          iexists C ++ [y]
          rw [framesOf_snoc C y _ _ Hy]
          iframe HrT Hdq
          ipureintro
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact HC x hx
          · simp at hx; subst hx; exact Hyok
        · ihave #Hi := inErr_read la ra eof ueof ed _ true got1 err1 $$ [$HefV $Hef $Hio $Heof $Hueof $HE1]
          ihave #Hi' := Hi
          iunfold inErr at Hi'
          icases Hi' with ⟨%Hip, -⟩
          obtain ⟨-, -, T1, l1, rfl⟩ := Hip
          wp_auto
          wp_bind (App (Val #(methods (go.GoType.PointerType T1) go!"Error" #l1)) (Val #()))
          iapply wp_inErr_Error $$ Hi
          inext
          iintro %msg
          wp_auto
          wp_apply wp_errors_New' as %x' #HN
          wp_apply wp_done pc sm' args' reply' ch' γ.conn γt' γf' K' Φ' Θ' D' _ (serverErr e)
              $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost Herr2]
          · unfold serverErr; iexact Herr2
          wp_for_post
          iframe
          iexists _, _
          iframe err Hr
          iright
          iframe Hdq
          iapply inErr_errorString $$ HN
  -- the header's read failed: `break`
  ihave #Hi := inErr_read la ra eof ueof ed _ true got err $$ [$HefV $Hef $Hio $Heof $Hueof $HE]
  ihave #Hi' := Hi
  iunfold inErr at Hi'
  icases Hi' with ⟨%Hip, -⟩
  obtain ⟨-, -, T, l, rfl⟩ := Hip
  wp_auto
  wp_for_post
  iclear HP Hacc HE
  rotate_left
  -- the loop's condition is false
  ihave #Hi := He
  iclear He
  ihave #He' := Hi
  iunfold inErr at He'
  icases He' with ⟨%Hep, -⟩
  obtain ⟨-, -, T, l, rfl⟩ := Hep
  wp_auto
  have hne : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
  simp only [hne, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  -- after the loop (both exits): both locks, the client shut down, every pending call failed
  all_goals (
    ihave #HEOF := io.eof_of_init $$ Hio
    iunfold errors.newVar at HEOF
    icases HEOF with ⟨%x0, #Hx0, -⟩
    icombine Heof Hx0 gives %Heq0
    subst Heq0
    wp_apply wp_Lock _ _ $$ [$Hsync $Hsmu] as ⟨Hsown, Hsinv⟩
    iunfold sendInv at Hsinv
    icases Hsinv with ⟨%rq, %w0, %L, %Wd, %n1, Hreq, Hwerr, Hsend, Hreqs, Hsq1, ⟨%sd1, Hd1⟩,
      #Hw0e, %Hs⟩
    wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
    iunfold muInv at Hinv
    icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
      %Hb, Hdown, Hnm, %HNM, Hrest⟩
    ihave %Hda := ghostVar_agree $$ Hdq Hdown
    obtain ⟨-, rfl⟩ := Hda
    ihave %Hda1 := ghostVar_agree $$ Hdq Hd1
    obtain ⟨-, rfl⟩ := Hda1
    simp only [Bool.false_eq_true, ite_false]
    ihave Hdh := (ghostVar_split_half γ.down (1 : Qp).half false).2 $$ [$Hdq $Hd1]
    imod ghostVar_update_halves true γ.down false false $$ Hdh Hdown with ⟨Hdh, Hdown⟩
    icases (ghostVar_split_half γ.down (1 : Qp).half true).1 $$ Hdh with ⟨Hdq, Hd1⟩
    wp_auto
    ihave #HesV' := HesV
    iunfold errors.newVar at HesV'
    icases HesV' with ⟨%xs, #Hxs, -⟩
    ihave #Hiu := io.isInit_access $$ Hio
    icases Hiu with ⟨-, -, -, -, -, #HU, -⟩
    -- `err == io.EOF`: four outcomes (goals rotated in turn), then the same code, `err` holding
    -- an `inErr` error (`Hi2`)
    by_cases hT : T = errors.errorString.ty
    rotate_left
    -- not an `*errorString`: unchanged
    have hT' : go.GoType.PointerType T ≠ go.GoType.PointerType errors.errorString.ty := by
      intro h; injection h with h; exact hT h
    simp only [hT', ↓reduceIte]
    wp_auto
    ihave #Hi2 := Hi
    rotate_left
    subst hT
    simp only [↓reduceIte]
    wp_auto
    by_cases hl : l = x0
    rotate_left
    -- another `*errorString`: unchanged
    rw [decide_eq_false hl]
    wp_auto
    ihave #Hi2 := Hi
    rotate_left
    rotate_left
    rw [decide_eq_true hl]
    wp_auto
    cases cls
    -- `io.EOF`, not closing: `io.ErrUnexpectedEOF`
    wp_auto
    ihave #Hi2 := inErr_newVar _ _ _ $$ HU Hueof
    rotate_left
    -- `io.EOF`, closing: `ErrShutdown`
    wp_auto
    ihave #Hi2 := inErr_newVar _ _ _ $$ HesV Hxs
    all_goals (
      iclear Hi
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (K := w64) (V := Loc)
        (fun (keys : List w64) (i : Int) => iprop(⌜0 ≤ i⌝ ∗ (∃ v : Loc, call_ptr ↦ v) ∗
          (∃ e2 : GoInterface, err_ptr ↦ e2 ∗ inErr e2) ∗
          ∃ m' : GMap w64 Loc,
            ⌜∀ k', m' !! k' = if k' ∈ keys.take i.toNat then none else m !! k'⌝ ∗
            [∗map] s ↦ pc ∈ m', callRes γ.conn s pc))
        _ _ _ mp m _ $$ Hmp
      iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
      isplitl [call err Hrest]
      · isplitr
        · ipureintro; omega
        isplitl [call]
        · iexists _; iexact call
        isplitl [err]
        · iexists _; iframe err Hi2
        iexists m
        iframe Hrest
        ipureintro; intro k'; simp
      isplitr
      · imodintro
        iintro %i %key %v ⟨%Hkey, %Hv⟩ ⟨%Hi0, ⟨%v0, Hc⟩, ⟨%e2, He2, #Hie2⟩, ⟨%m', %Hm', Hrem⟩⟩
        obtain ⟨hk, hstep⟩ := rem_step keys m m' i key Hi0 Hkey Hknd Hm'
        have hk' : m' !! key = some v := hk.trans Hv
        icases (BigSepM.bigSepM_delete (Φ := fun s pc => callRes (hG := hG) γ.conn s pc)
          (by rw [gmap_get?_eq]; exact hk')).1 $$ Hrem with ⟨Hcr, Hrem⟩
        iunfold callRes at Hcr
        icases Hcr with ⟨%sm', %args', %reply', %ch', %γt', %γf', %K', %Φ', %Θ', %D', %C', %post',
          %col', %ap', #Hf2, Herr2, #Htk2, Hdone2, -, -, -, HD2, -, -⟩
        wp_auto
        ihave Hpost : callPost γ.conn (some (uint.nat key)) Φ' Θ' D' e2 $$ [HD2]
        · iunfold callPost
          iright; iright
          iunfold inErr at Hie2
          icases Hie2 with ⟨%Hie2p, #Hie2a⟩
          iframe Hie2a
          isplitr
          · ipureintro; exact ⟨Hie2p.1, Hie2p.2.1⟩
          ileft
          iexact HD2
        wp_apply wp_done v sm' args' reply' ch' γ.conn γt' γf' K' Φ' Θ' D' _ e2
            $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Hpost $Herr2]
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; omega
        isplitl [Hc]
        · iexists _; iexact Hc
        isplitl [He2]
        · iexists e2; iframe He2 Hie2
        iexists _
        iframe Hrem
        ipureintro; exact hstep
      iintro - Hmp
      wp_auto
      wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm]
      · iunfold muInv
        iexists sq, n, mp, m, true, _, NM
        iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        isplitr
        · ipureintro; exact Hb
        isplitr
        · ipureintro; exact HNM
        simp only [↓reduceIte]
        itrivial
      wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
          Hd1]
      · iunfold sendInv
        iexists rq, w0, L, Wd, n1
        iframe Hreq Hwerr Hsend Hreqs Hsq1
        isplitl [Hd1]
        · iexists true; iexact Hd1
        iframe Hw0e
        ipureintro; exact Hs
      iapply HΦ
      itrivial))

end proof

end net.rpc
end Perennial
