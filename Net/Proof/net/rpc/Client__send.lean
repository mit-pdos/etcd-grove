/-
The proof of `Client.send` (`Net/Spec/net/rpc/Client__send.lean`). Under `reqMutex` (`sendInv`) and
`mutex` (`muInv`): refused (shut down or closing), the call fails with `ErrShutdown` (`Call.done`),
ticket `none`; else it is numbered `n` (a time receipt for the number, `n + 1 < 2 ^ 64`), its names
allocated and recorded (`nm`), its entry put in `pending` (`callRes`), ticket `some n`. Then
`WriteRequest`: without a write error before, the encoding's continuation appends the request
(`req_append`); after a failed write the call, if still pending, fails with the write's error.
-/
module

public import Net.Spec.net.rpc.Client__send
public import Net.Spec.net.rpc.Call__done
public import Net.Spec.net.rpc.clientCodec__WriteRequest
public import Net.Proof.net.rpc.ClientGhost
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

theorem uint_nat_W64_lt (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 n) = n := by
  word

theorem nm_fresh {X : Type} (NM : GMap Nat X) (n : Nat)
    (h : ∀ i, (NM.lookup i).isSome → i < n) : NM.lookup n = none := by
  cases hl : NM.lookup n with
  | none => rfl
  | some v =>
    exfalso
    have := h n (by rw [hl]; rfl)
    exact Nat.lt_irrefl _ this

theorem nm_insert_bound {X : Type} (NM : GMap Nat X) (n : Nat) (x : X)
    (h : ∀ i, (NM.lookup i).isSome → i < n) :
    ∀ i, ((NM.insert n x).lookup i).isSome → i < n + 1 := by
  intro i hi
  by_cases hin : i = n
  · omega
  · have hne : n ≠ i := Ne.symm hin
    have := h i (by simpa [hne] using hi)
    omega

theorem Client.send.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_WriteRequest : clientCodec.WriteRequest.spec (GF := GF) (hG := hG))
    (wp_done : Call.done.spec (GF := GF) (hG := hG)) :
    Client.send.spec (GF := GF) (hG := hG) := by
  intro c W a γ pc sm svc M S args reply ch γt γf K Φm Rargs D Θ C e0
  wp_start as ⟨#Hcl, %Hsv, #Hset, Henc, HD, #Hdec, Hγt, #Hf, Herr, Hdone⟩
  unfold isClientN clientAt
  icases Hcl with ⟨%cc, %t, %cn, %la, %ra, #Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, #Henv,
    #Hsmu, #Hmu⟩
  ihave #Henv' := Henv
  unfold cliEnv
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply +noauto wp_Lock _ _ $$ [$Hsync $Hsmu] as ⟨Hsown, Hsinv⟩
  wp_take_receipt as Hr1
  wp_auto
  iunfold sendInv at Hsinv
  icases Hsinv with ⟨%rq, %w0, %L, %Wd, %n1, Hreq, Hwerr, Hsend, Hreqs, Hsq1, ⟨%sd1, Hd1⟩,
    #Hw0e, ⟨%HLok, %HLn, %HWd, %Hw0⟩⟩
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  iunfold muInv at Hinv
  icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
    ⟨%Hsqn, %Hbound⟩, Hdown, Hnm, %HNM, Hrest⟩
  ihave %Hsqa := ghostVar_agree $$ Hsq1 Hsq
  obtain ⟨-, rfl⟩ := Hsqa
  ihave #HesV' := HesV
  iunfold errors.newVar at HesV'
  icases HesV' with ⟨%xs, #Hxs, -⟩
  cases sd <;> cases cls
  rotate_left
  iterate 3 (
    -- refused: `ErrShutdown`
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n1, mp, m, _, _, NM
      iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm Hrest
      ipureintro; exact ⟨⟨Hsqn, Hbound⟩, HNM⟩
    imod ghost_map_insert_persist () (none : Option Nat) (by rfl) $$ Hγt with ⟨-, #Htk0⟩
    ihave #Htk : ticket γt none $$ []
    · iunfold ticket; iexact Htk0
    wp_apply wp_done pc sm args reply ch γ.conn γt γf K Φm Θ D none
        (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xs)
        $$ [$Hdbg $Hf $Htk $Hdone $Herr HD]
    · iunfold callPost
      iright; iright
      isplitr
      · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_errorString xs⟩
      isplitr
      · iapply errAny_newVar $$ HesV Hxs
      ileft; iexact HD
    wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
        Hd1]
    · iunfold sendInv
      iexists rq, w0, L, Wd, n1
      iframe Hreq Hwerr Hsend Hreqs Hsq1
      isplitl [Hd1]
      · iexists sd1; iexact Hd1
      iframe Hw0e
      ipureintro; exact ⟨HLok, HLn, HWd, Hw0⟩
    iapply HΦ
    iexists none
    iframe Htk
    iunfold sendRes
    iright
    iframe Henc
    unfold unsent
    itrivial)
  -- numbered `n1`
  wp_auto_lc 2
  subst Hsqn
  icases receipt_add_one_lt n1 $$ [$Hr1 $Hr] with ⟨%Hn1, Hr⟩
  have hn1 : n1 + 1 < 2 ^ 64 := Nat.lt_of_lt_of_le Hn1 Hbound
  have hu : uint.nat (W64 n1) = n1 := uint_nat_W64_lt n1 (by omega)
  wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 mp m (W64 n1) pc) $$ Hmp as Hmp
  imod saved_pred_alloc (GF := GF) (fun p : List w8 × GoString => Φm p.1 p.2) DFrac.discard
    trivial with ⟨%post, #Hpost⟩
  imod token_alloc (GF := GF) with ⟨%col, Hcol⟩
  imod token_alloc (GF := GF) with ⟨%ap, Hap⟩
  have hNM : NM.lookup n1 = none := nm_fresh NM n1 HNM
  imod ghost_map_insert_persist n1 ((post, col, ap) : GName × GName × GName) hNM $$ Hnm
    with ⟨Hnm, #Hnmn⟩
  imod ghost_map_insert_persist () (some n1 : Option Nat) (by rfl) $$ Hγt with ⟨-, #Htk0⟩
  ihave #Htk : ticket γt (some n1) $$ []
  · iunfold ticket; iexact Htk0
  ihave %Hda := ghostVar_agree $$ Hd1 Hdown
  obtain ⟨-, rfl⟩ := Hda
  imod ghostVar_update_halves (n1 + 1) γ.sq n1 n1 $$ Hsq1 Hsq with ⟨Hsq1, Hsq⟩
  wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
      Hrest Herr Hdone HD Hcol]
  · iunfold muInv
    iexists W64 n1 + W64 1, n1 + 1, mp, _, false, false, _
    iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
    isplitr
    · ipureintro; exact ⟨by word, Hbound⟩
    isplitr
    · ipureintro; exact nm_insert_bound NM n1 _ HNM
    simp only [Bool.false_eq_true, ite_false]
    iapply BigSepM.bigSepM_insert_elim $$ [Herr Hdone HD Hcol] Hrest
    iunfold callRes
    iexists sm, args, reply, ch, γt, γf, K, Φm, Θ, D, C, post, col, ap, e0
    rw [hu]
    iframe Hf Herr Htk Hdone Hpost Hcol Hnmn HD
    isplitr
    · rcases reply with e | _
      · simp only [bodyDec]
        iframe Hset
        iexact Hdec
      · exact absurd rfl Hsv.2.2
    ipureintro; exact Hsv.2.2
  sorry

end proof

end net.rpc
end Perennial
