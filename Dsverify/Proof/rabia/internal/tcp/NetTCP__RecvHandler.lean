/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/NetTCP__RecvHandler.lean`,
run `rabia-r1wake-1`: the reader is `rdOwn` (the revised bufio's over `Net/`'s connection); the
message's facts come from the protocol one step later (`rdOwn_proto`, a later credit per message).)

The proof of `rabia/internal/tcp.(*NetTCP).RecvHandler(X)`: server `k`'s receive routine of the
connection from server `X` pushes `X`'s messages on `RecvChan` in order (producer `X`), each with
its push log's prefix, `B_X`'s prefix, and, for a broadcast, its facts and its receipt (minted
here: the only routine reading `X`'s connection).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.NetLemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

instance ite_persistent'' {P : Prop} [Decidable P] (A B : IProp GF) [Persistent A] [Persistent B] :
    Persistent (if P then A else B) := by split <;> assumption

/-- The receive routine of `X`'s connection has read and pushed `l`. -/
def recvSt (γ : Names) (k : Nat) (γl : SrvNames) (X : Nat) (γr : OrdNames) (br : Loc)
    (cid : Nat) (l : List MsgV) : IProp GF :=
  iprop(rdOwn br cid true (netP γ k) (hsBytes X ++ frames (l.map encMsg)) ∗
    ⌜∀ m ∈ l, (encMsg m).length < 2 ^ 32⌝ ∗ pushAuth γl X l ∗
    (∃ J : GMap Nat Unit, rcptAuth γl X J ∗ ⌜∀ x, J.lookup x ≠ none → x < (bcastPart l).length⌝) ∗
    ordProd γr X l.length)

theorem wp_NetTCP_RecvHandler (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (t : Loc)
    (fr : w64) (X : Nat) (hX : sint.Z fr = X) (hXn : X < cf.n) (rc : GoChan) (γr : OrdNames) (wg : Loc)
    (rds : GoSlice) (rs : List Loc) (br : Loc) (cid : Nat) (hbr : rs[X]? = some br) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ shared γ ∗ confRO cf ∗ cfgIs γ.rab cf ∗
      t.[NetTCP, go!"RecvChan"] ↦□ rc ∗ isOrdChan (V := Msg) γr rc cf.n (recvP γ cf k γl) ∗
      t.[NetTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗
      t.[NetTCP, go!"Readers"] ↦□ rds ∗ rds ↦*□ rs ∗
      recvSt γ k γl X γr br cid [] }}
    (App (Val (t @!! go.GoType.PointerType NetTCP.ty @!! go!"RecvHandler")) (Val #fr))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hsh, #Hconf, #Hcf, #HRC, #Hord, #HWg, Htok, #HRD, #Hrds, Hst⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hXm : X < maxS := Nat.lt_of_lt_of_le hXn (RCfg.n_le_maxS cf Hok)
  wp_apply wp_with_defer as %defer Hdefer
  iunfold confRO at Hconf
  icases Hconf with ⟨-, %ps, #Hc, -⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) _) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.nat sl.len = 16384000 := by rw [← Hsl0.1, List.length_replicate]
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrds
  have hXl : X < rs.length := (List.getElem?_eq_some_iff.1 hbr).1
  have hb : 0 ≤ sint.Z fr ∧ sint.Z fr < sint.Z rds.len := by
    have h1 := Hrl.1; rw [hX]; constructor
    · omega
    · word
  have hfX : (sint.Z fr).toNat = X := by rw [hX]; simp
  ihave HI : (∃ (l : List MsgV) (ds : List w8), "Hsl" ∷ sl ↦* ds ∗
      "Hst" ∷ recvSt γ k γl X γr br cid l :
      IProp GF) $$ [Hsl Hst]
  · iexists [], _; iframe
  irename «from» => Hfrom
  wp_for HI
  unfold recvSt
  icases Hst with ⟨Hbr, %Hl, Hpush, ⟨%J, HJ, %HJ⟩, Hprod⟩
  ihave %Hdl := ownSlice_len _ _ _ $$ Hsl
  have hdl : ds.length = 16384000 := by rw [Hdl.1, hsl]
  ihave #HF := netP_frameIs γ k cid X hXm l Hl
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index rds _ rs _ br hb.1 $$ [Hrds] with -
  · iframe #; ipureintro; rw [hfX]; exact hbr
  wp_apply (lc := 1) wp_msgReadUnmarshal D m_ptr br cid true (netP γ k) _ sl ds $$ [$m $Hbr $HF $Hsl]
    as %e %n ⟨%ds', Hsl, Hres⟩
  icases Hres with (⟨%He, %v, %msg, %Hq, Hcmd, #Hrep, Hbr⟩ | ⟨%He, %R', %v, %HR', Hcmd, Hbr⟩)
  · subst He
    have Hq' : (encMsg msg).length < 2 ^ 32 := by omega
    ihave ⟨Hbr, Hpp⟩ := rdOwn_proto br cid true (netP γ k) _ $$ Hbr
    iapply fupd_wp
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hpp with #Hpp
    imodintro
    ihave ⟨#Hlb, #Hrp⟩ := netP_read γ cf k cid X hXm l Hl msg Hq' $$ [$Hcf $Hpp]
    iunfold pushAuth at Hpush
    imod monoListAuthOwn_update_app [msg] $$ Hpush with ⟨Hpush, #Hplb⟩
    -- the value pushed, with its facts and (a broadcast) its receipt
    ihave HP : |={⊤}=> (recvP γ cf k γl X l.length v ∗
        ∃ J' : GMap Nat Unit, rcptAuth γl X J' ∗
          ⌜∀ x, J'.lookup x ≠ none → x < (bcastPart (l ++ [msg])).length⌝) $$ [HJ]
    · by_cases hty : msg.ty = tyProposalReply
      · simp only [hty, ↓reduceIte]
        imodintro
        isplitl []
        · unfold recvP
          iexists msg, l ++ [msg]
          iframe #
          isplitr
          · unfold pushLb; iexact Hplb
          isplitr
          · ipureintro; simp
          simp only [hty, ↓reduceIte]
          iexact Hrp
        iexists J
        iframe HJ
        ipureintro
        intro x hx
        have := HJ x hx
        simp [bcastPart_append, bcastPart, hty] at this ⊢
        omega
      · simp only [hty, ↓reduceIte]
        have hbp : bcastPart (l ++ [msg]) = bcastPart l ++ [msg] := by
          simp [bcastPart_append, bcastPart, hty]
        have hfresh : J.lookup (bcastPart l).length = none := by
          cases hc : J.lookup (bcastPart l).length with
          | none => rfl
          | some u => exfalso; have := HJ _ (by rw [hc]; simp); omega
        unfold rcptAuth
        imod ghost_map_insert (bcastPart l).length () hfresh $$ HJ with ⟨HJ, Hr⟩
        imod bcast_elem γ cf X hXm (bcastPart (l ++ [msg])) (bcastPart l).length msg
          (by rw [hbp]; simp) $$ [$Hsh $Hcf $Hlb] with #Hm
        imodintro
        isplitl [Hr]
        · unfold recvP
          iexists msg, l ++ [msg]
          iframe #
          isplitr
          · unfold pushLb; iexact Hplb
          isplitr
          · ipureintro; simp
          simp only [hty, ↓reduceIte]
          iframe #
          rw [hbp]
          unfold rcpt
          simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
          iexact Hr
        iexists _
        iframe HJ
        ipureintro
        intro x hx
        rw [hbp]
        simp only [GMap.lookup_insert_eq_iff] at hx
        simp only [List.length_append, List.length_singleton]
        split at hx
        · omega
        · have := HJ x hx; omega
    imod HP with ⟨HP, HJ⟩
    wp_auto
    wp_apply wp_ord_send γr rc cf.n (recvP γ cf k γl) X l.length v $$ [$Hord $Hprod $HP] as Hprod
    wp_for_post
    iframe
    iexists l ++ [msg], ds'
    simp only [List.map_append, List.map_cons, List.map_nil, frames_append, frames_cons, frames_nil,
      List.append_nil, List.append_assoc, List.length_append, List.length_singleton]
    unfold named pushAuth
    iframe Hsl Hbr Hpush HJ Hprod
    ipureintro
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact Hl r hr
    · exact Hq'
  · rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · exact absurd rfl He

end proof

end Perennial.rabia.internal.tcp
