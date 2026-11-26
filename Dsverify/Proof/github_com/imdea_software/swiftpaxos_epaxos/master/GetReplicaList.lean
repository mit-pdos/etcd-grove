/-
`m.GetReplicaList(args, reply)` (`masterGetReplicaList.spec`, `NetRpc/Specs.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]

open replica.defs in
theorem grlReply_combine (pr : Loc) (h : pr ≠ null) (a b : GoSlice) (c : Bool) :
    pr.[GetReplicaListReply, go!"ReplicaList"] ↦ a ∗ pr.[GetReplicaListReply, go!"AliveList"] ↦ b ∗
      pr.[GetReplicaListReply, go!"Ready"] ↦ c ⊢
      (pr ↦ GetReplicaListReply.mk a b c : IProp GF) := by
  iintro ⟨H1, H2, H3⟩
  iapply typedPointsto_combine (V := GetReplicaListReply) pr _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe

set_option goose.wp.extras true in
open replica.defs in
theorem masterGetReplicaList.wp_proof (hP : dlog.Logger.Printf.spec (GF := GF)) (γ : EpNames) :
    masterGetReplicaList.spec (GF := GF) (isMaster γ) := by
  intro m pa pr
  wp_start as ⟨#Hm, Hpa, Hpr⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %hprnn⟩
  iStructNamedPrefix Hpr "r"
  unfold isMaster
  icases Hm with ⟨#Hpkg, %mu, %cfg, %logger, %ic, %c, #Hlock, #Hmu, #Hic, #Hcond, #HN, #Hcfgf, #Hcfg, %Hld, #Hlogf, #Hlog⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcond' : (sync.isCond ic (interface.mk (go.GoType.PointerType sync.Mutex.ty) #mu)
      : IProp GF) $$ []
  · iexact Hcond
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  ihave HI : (sync.ownMutex mu ∗ masterLockInv γ m : IProp GF) $$ [Hlocked Hinv]
  · iframe
  wp_for HI
  icases HI with ⟨Hlocked, Hinv⟩
  ihave #Hlk := sync.Mutex_is_Locker mu _ $$ Hsync Hmu
  icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks, %nl, %al, %pl, %ldsl, %alsl, %latsl, %ld, %alv, %lat, %fi, %Hks, Hlists, #Hldf, Hld, #Half, Halv, #Hlatf, Hlat, Hfi⟩
  wp_auto
  cases fi
  · simp only [Bool.not_false]
    cleanup_bool_decide
    wp_auto
    wp_apply sync.Cond.wp_Wait ic (interface.mk (go.GoType.PointerType sync.Mutex.ty) #mu)
        iprop(sync.ownMutex mu ∗ masterLockInv γ m)
      $$ [Hlocked Hlists Hld Halv Hlat Hfi] as ⟨Hlocked, Hinv⟩
    · isplitr
      · iexact Hcond'
      isplitr
      · iexact Hlk
      iframe
      iapply (masterLockInv_iff γ m).2
      iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, false
      iframe
      iframe Hldf Half Hlatf
      ipureintro; exact Hks
    wp_for_post
    iframe
    unfold named
    iframe Hlocked Hinv
  simp only [Bool.not_true]
  rw [decide_eq_false (show ¬ ((#false : val) = #true) by intro h; have := go.intoVal_inj h; simp at this)]
  simp only [Bool.false_eq_true, ↓reduceIte, decide_True_any]
  wp_auto
  obtain ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩ := Hks
  icases lists_view γ m ks nl al pl $$ Hlists with ⟨%dq, Hnlf, Hnl, Hback⟩
  ihave %Hnll := ownSlice_len _ _ _ $$ Hnl
  have hks5 := ks_le ks hnd hsub
  wp_auto
  wp_join iprop(∃ rd : Bool, pr.[GetReplicaListReply, go!"Ready"] ↦ rd ∗ master_ptr ↦ m ∗
      reply_ptr ↦ pr ∗ mfld m go!"nodeList" ↦{dq} nl)
    with [rReady master reply Hnlf] as ⟨%rd, rReady, master, reply, Hnlf⟩
  wp_apply (wp_slice_make2 (V := GoString) (W64 0)) $$ [] as %rl0 ⟨Hrl, Hrlc⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Bool) (W64 0)) $$ [] as %al0 ⟨Hal0, Hal0c⟩
  · ipureintro; decide
  rename_i key_ptr
  irename : (key_ptr ↦ (zero_val w64) : IProp GF) => Hkey
  ihave %Halvl := ownSlice_len _ _ _ $$ Halv
  ihave HI : (∃ (iw kv : w64) (nodev : GoString) (rl alL : GoSlice),
      "i" ∷ i_ptr ↦ iw ∗ "Hkey" ∷ key_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nodev ∗
      "rReplicaList" ∷ pr.[GetReplicaListReply, go!"ReplicaList"] ↦ rl ∗
      "Hrl" ∷ rl ↦* (ks.map peerAddrOf).take (sint.nat iw) ∗
      "Hrlc" ∷ ownSliceCap GoString rl (DFrac.own 1) ∗
      "rAliveList" ∷ pr.[GetReplicaListReply, go!"AliveList"] ↦ alL ∗
      "Hal" ∷ alL ↦* alv.take (sint.nat iw) ∗
      "Halc" ∷ ownSliceCap Bool alL (DFrac.own 1) ∗
      "Hnl" ∷ nl ↦*{dq} List.map peerAddrOf ks ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ sint.Z nl.len⌝ : IProp GF)
      $$ [i Hkey node rReplicaList Hrl Hrlc rAliveList Hal0 Hal0c Hnl]
  · iexists (W64 0), _, _, rl0, al0
    have h0 : sint.nat (W64 0) = 0 := rfl
    simp only [h0, List.take_zero, List.replicate_zero]
    iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · list_elem (List.map peerAddrOf ks) (sint.nat iw) as x
    rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z nl.len by word)]
    wp_apply wp_load_slice_index nl (sint.Z iw) _ _ x (by word) $$ [$Hnl] as Hnl
    · ipureintro; simpa [sint.nat] using Hx_lookup
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoString) (t := go.string) [x]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hrl $Hrlc $Hsl1] as %rl' ⟨Hrl, Hrlc, -⟩
    have hkl : ks.length = sint.nat nl.len := by simpa using Hnll.1
    have hiw5 : sint.nat iw < 5 := by word
    list_elem alv (sint.nat iw) as y
    rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z alsl.len by simp [halvl] at Halvl; word)]
    wp_apply wp_load_slice_index alsl (sint.Z iw) _ _ y (by word) $$ [$Halv] as Halv
    · ipureintro; simpa [sint.nat] using Hy_lookup
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.bool))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Bool) (t := go.bool) [y]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hal $Halc $Hsl2] as %al' ⟨Hal, Halc, -⟩
    wp_for_post
    iframe
    iexists _, _, _, _, _
    iframe
    have hn1 : sint.nat (iw + W64 1) = sint.nat iw + 1 := by word
    have hx1 : sint.nat iw < (ks.map peerAddrOf).length := by rw [List.length_map, hkl]; word
    have hy1 : sint.nat iw < alv.length := by rw [halvl]; exact hiw5
    rw [hn1, List.take_succ_eq_append_getElem hx1, List.take_succ_eq_append_getElem hy1]
    rw [List.getElem?_eq_some_iff] at Hx_lookup Hy_lookup
    rw [Hx_lookup.2, Hy_lookup.2]
    iframe
    ipureintro; constructor <;> word
  have hiw : iw = nl.len := by word
  subst hiw
  have hkl : ks.length = sint.nat nl.len := by simpa using Hnll.1
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk (go.GoType.SliceType go.string) #rl]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl3 ⟨-, -⟩
  wp_auto
  wp_apply (wp_Master_Printf hP) $$ [$Hlogf $Hlog]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hback Hnlf Hnl Hld Halv Hlat Hfi]
  · iapply (masterLockInv_iff γ m).2
    iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, true
    ispecialize Hback $$ Hnlf Hnl
    inext
    iframe
    iframe Hldf Half Hlatf
    ipureintro; exact ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩
  iapply HΦ
  iexists rl, alL, ks.map peerAddrOf, alv.take (sint.nat nl.len), rd
  isplitl [rReplicaList rAliveList rReady]
  · iapply grlReply_combine pr hprnn
    iframe
  rw [← hkl, List.take_of_length_le (by simp)]
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
