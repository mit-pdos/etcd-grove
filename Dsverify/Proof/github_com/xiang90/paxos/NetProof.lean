/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/NetProof.lean (lab master 7a84fb35;
notes/dsv-paxos.md): the transport's proofs (`tcpnet.go`, `marshal.go`), over the net extension's
canonical `net` specs (`Net/Spec/net/`, taken as hypotheses, linked in `Link.lean`) and the laws of
`GooseLang/Ext/Net/Proto.lean` (the lab's `net.TCPConn.*.wp_proof` replaced by `net.Conn.*` with
`writeP`/`write_acc`, `read_au`, `accept_au`, `dial_au`, `close_au`, `deadline_au`, `listen_au`).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Net
public import Dsverify.Proof.github_com.xiang90.paxos.Pkg
public import Net.Spec.net.Listen
public import Net.Spec.net.DialTimeout
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__SetReadDeadline
public import Net.Spec.net.Conn__SetWriteDeadline
public import GooseLang.Ext.Net.Stream
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace Transport

/-! ### Nonblocking operations on a bag channel -/

section bag
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- A nonblocking send of `v` on a bag channel, with `P v` (copied from the harness's
`Harness/Mux.lean`, which this module does not import). -/
theorem bag_nonblocking_send_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V)
    (Φ : IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ P v -∗ ▷ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro Hlc ⟨#Hch, #Hinv⟩ HP HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals itrivial

/-- A nonblocking receive on a bag channel: what it receives meets `P`. -/
theorem bag_nonblocking_recv_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF)
    (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAuInner γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
  iintro Hlc1 ⟨#Hch, #Hinv⟩ HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered buff'; iframe
    imodintro
    iapply HΦ $$ HP
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

end bag

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : paxos.Assumptions]
variable [π : NetProtoGS]

set_option goose.wp.extras true

local notation "pkg" => pkg_id.github_com.xiang90.paxos

theorem wp_marshalMessage (m : message) (hwf : msgWf m) :
  {{ isPkgInit (PROP := IProp GF) pkg }}
    (App (Val (@! marshalMessage)) (Val #m))
  {{ (s : GoSlice), RET #s; s ↦* encMsg m ∗ ownSliceCap w8 s (DFrac.own 1) }} := by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  unfold msgWf at hwf
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 48 + W64 m.value'.length) (by word)) as %b ⟨Hb, Hbcap, %Hbc⟩
  rw [List.replicate_zero]
  wp_apply github_com.tchajed.marshal.wp_WriteInt b m.from' [] (by simp) $$ [$Hb $Hbcap] as %b1 ⟨Hb, Hbcap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteInt _ m.to' _ (by simp [u64Le_length]) $$ [$Hb $Hbcap] as %b2 ⟨Hb, Hbcap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteInt _ m.typ' _ (by simp [u64Le_length]) $$ [$Hb $Hbcap] as %b3 ⟨Hb, Hbcap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteInt _ m.n' _ (by simp [u64Le_length]) $$ [$Hb $Hbcap] as %b4 ⟨Hb, Hbcap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteInt _ m.prevn' _ (by simp [u64Le_length]) $$ [$Hb $Hbcap] as %b5 ⟨Hb, Hbcap⟩
  wp_apply wp_string_to_bytes as %vs ⟨Hvs, Hvscap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteLenPrefixedBytes _ _ _ _ _ (by simp [u64Le_length]) $$ [$Hb $Hbcap $Hvs] as %b6 ⟨Hb, Hbcap, Hvs⟩
  unfold encMsg
  rw [List.nil_append]
  wp_end

theorem encMsg_assoc (m : message) :
    encMsg m = u64Le m.from' ++ (u64Le m.to' ++ (u64Le m.typ' ++ (u64Le m.n' ++
      (u64Le m.prevn' ++ (u64Le (W64 m.value'.length) ++ m.value' ++ []))))) := by
  simp [encMsg]

theorem encMsg_drop40 (m : message) :
    (encMsg m).drop 40 = u64Le (W64 m.value'.length) ++ m.value' := by
  have : encMsg m = (u64Le m.from' ++ u64Le m.to' ++ u64Le m.typ' ++ u64Le m.n' ++ u64Le m.prevn') ++
      (u64Le (W64 m.value'.length) ++ m.value') := by simp [encMsg]
  rw [this, List.drop_left' (by simp [u64Le_length])]

theorem wp_unmarshalMessage (b : GoSlice) (dq : DFrac) (m : message) (hwf : msgWf m) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ b ↦*{dq} encMsg m }}
    (App (Val (@! unmarshalMessage)) (Val #b))
  {{ RET #m; True }} := by
  wp_start as Hb
  rw [encMsg_assoc]
  wp_auto
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb] as %b1 Hb
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb] as %b2 Hb
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb] as %b3 Hb
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb] as %b4 Hb
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb] as %b5 Hb
  unfold msgWf at hwf
  wp_apply github_com.tchajed.marshal.wp_ReadLenPrefixedBytes _ _ _ _ _ (by word) $$ [$Hb] as %v %b6 ⟨Hv, Hb⟩
  wp_apply wp_bytes_to_string $$ [$Hv] as Hv
  wp_end

theorem wp_encodeFrame (m : message) (hwf : msgWf m) :
  {{ isPkgInit (PROP := IProp GF) pkg }}
    (App (Val (@! encodeFrame)) (Val #m))
  {{ (s : GoSlice), RET #s; s ↦* frame m }} := by
  wp_start
  wp_auto
  wp_apply wp_marshalMessage m hwf as %body ⟨Hbody, Hbodycap⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hbody
  have he := encMsg_length m
  unfold msgWf at hwf
  wp_apply (wp_slice_make3 (V := w8) (W64 0) (W64 8 + body.len) (by word)) as %b ⟨Hb, Hbcap, %Hbc⟩
  rw [List.replicate_zero]
  wp_apply github_com.tchajed.marshal.wp_WriteInt b _ [] (by simp) $$ [$Hb $Hbcap] as %b1 ⟨Hb, Hbcap⟩
  wp_apply github_com.tchajed.marshal.wp_WriteBytes $$ [$Hb $Hbcap $Hbody] as %b2 ⟨Hb, Hbcap, Hbody⟩
  rw [List.nil_append, show body.len = W64 (encMsg m).length by word]
  iapply HΦ; unfold frame; iexact Hb

/-- `writeFrame(c, f)`: sets the write deadline and writes `f`; `true` only if all of it was
written. The writer's token grows by what was written, a prefix of `f`'s bytes. -/
theorem wp_writeFrame (wp_SetWriteDeadline : net.Conn.SetWriteDeadline.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (cv : GoInterface) (cn : Nat) (a : GoString) (f : GoSlice) (bs : List w8) (dq : DFrac)
    (P : Proto GF) (W : List w8) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn cv cn false a ∗
      sendTok (Gg := hG.goose_globalGS) cn false P W ∗ □ P cn (W ++ bs) ∗ f ↦*{dq} bs }}
    (App (App (Val (@! writeFrame)) (Val #cv)) (Val #f))
  {{ (ok : Bool), RET #ok; f ↦*{dq} bs ∗
      ∃ w, ⌜w <+: bs ∧ (ok = true → w = bs)⌝ ∗ sendTok (Gg := hG.goose_globalGS) cn false P (W ++ w) }} := by
  wp_start as ⟨#Hc, Hs, #HP, Hf⟩
  ihave ⟨%ed, #Hed⟩ := ed_init $$ Hpkg
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  ihave #Hconn := sendTok_connIs cn false P W $$ Hs
  wp_auto
  wp_apply time.wp_Now as %tm -
  wp_apply time.Time.wp_Add as %tm' -
  wp_apply wp_SetWriteDeadline t cn false a la ra tm' (fun _ => iprop(True)) $$ [] as %err1 -
  · iframe Hca
    imod deadline_w_au cn false _ $$ Hconn with ⟨%st, Hst, Hcl⟩
    imodintro
    iexists st
    iframe Hst
    iintro %res %st' %Hd Hst
    imod Hcl $$ %res %st' %Hd Hst with -
    imodintro
    itrivial
  wp_apply wp_Write t cn false a la ra f bs dq ed (writeP cn false P W) $$ [Hf Hs]
    as %n %err ⟨%w, %res, Hs, Hf, %Hw, #HE⟩
  · iframe Hca Hf Hed
    isplitl [Hs]
    · iapply writeP_init $$ Hs
    · iapply write_acc cn false P W bs $$ HP
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
  obtain ⟨hw, -, hnone, -⟩ := Hw
  unfold writeP
  cases res with
  | none =>
    have herr := Hne.1 rfl
    subst herr
    wp_auto
    iapply HΦ
    iframe Hf
    iexists w
    iframe Hs
    ipureintro; exact ⟨hw, fun _ => hnone rfl⟩
  | some k =>
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    iframe Hf
    iexists w
    iframe Hs
    ipureintro; exact ⟨hw, fun h => by cases h⟩

theorem buf_rejoin (buf : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    slice.slice buf w8 (W64 0) k ↦* xs -∗ slice.slice buf w8 k buf.len ↦* ys -∗
      (buf ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice buf (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k buf (DFrac.own 1) xs ys (W64 0) buf.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

/-- `readFull(c, buf)`: reads until `buf` is full; `false` on the first error. What it read
extends the reader's token, a prefix of `buf`'s new contents; all of them if `true`. -/
theorem wp_readFull (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (P : Proto GF) (R : List w8)
    (buf : GoSlice) (bs0 : List w8) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn s a ∗ buf ↦* bs0 ∗
      recvTokL (Gg := hG.goose_globalGS) cn s P R }}
    (App (App (Val (@! readFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (got bs' : List w8), recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ got) ∗
      buf ↦* bs' ∗ ⌜bs'.length = bs0.length ∧ got <+: bs' ∧ (ok = true → got = bs')⌝ }} := by
  wp_start as ⟨#Hc, Hbuf, HP⟩
  ihave ⟨%eof, #Heof⟩ := eof_init $$ Hpkg
  ihave ⟨%ed, #Hed⟩ := ed_init $$ Hpkg
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hc⟩
  subst Hct
  wp_auto
  ihave %Hlen0 := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave HI : (∃ (k : w64) (bsn got : List w8),
      "n" ∷ n_ptr ↦ k ∗ "Hbuf" ∷ buf ↦* bsn ∗ "HP" ∷ recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ got) ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len ∧ bsn.length = bs0.length ∧
        got.length = sint.nat k ∧ bsn.take (sint.nat k) = got⌝ : IProp GF)
      $$ [n Hbuf HP]
  · iexists W64 0, bs0, []
    rw [List.append_nil]
    iframe n Hbuf HP
    ipureintro
    exact ⟨by decide, by word, rfl, rfl, by simp⟩
  wp_for HI
  wp_if_destruct
  · -- the loop body: a read into `buf[k:]`
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    rw [ite_eq_left ⟨Hk0, Hkl, Hwf.2⟩]
    icases (ownSlice_split_all k buf _ bsn ⟨Hk0, Hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    wp_apply wp_Read t cn s a la ra (slice.slice buf w8 k buf.len) (bsn.drop (sint.nat k)) eof ed
        (fun r => iprop(recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ (got ++ r.got)) ∗
          ⌜r.got.length ≤ (slice.slice buf w8 k buf.len).len.toNat ∧
            (r = .bytes [] → (slice.slice buf w8 k buf.len).len.toNat = 0)⌝)) $$ [Hb2 HP]
      as %k' %err ⟨%r, %bs', ⟨HP, %Hrl0⟩, Hb2, %Hout, HE⟩
    · iframe Hc Hb2 Heof Hed
      imod read_au cn s P (R ++ got) ((slice.slice buf w8 k buf.len).len.toNat) $$ HP
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r %d' %Hrd HE HD
      imod Hcl $$ %r %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      rw [← List.append_assoc]
      iframe HP
      ipureintro
      exact readOutcome_got_le Hrd
    have hdl : (bsn.drop (sint.nat k)).length = sint.nat buf.len - sint.nat k := by
      rw [List.length_drop, Hbl, Hlen0.1]
    have hsl : (slice.slice buf w8 k buf.len).len = buf.len - k := rfl
    have hlenk : BitVec.toNat (buf.len - k) = sint.nat buf.len - sint.nat k := by word
    obtain ⟨Hrl, Hr0⟩ := Hrl0
    rw [hsl, hlenk] at Hrl Hr0
    cases r with
    | bytes bs =>
      obtain ⟨hk', rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      simp only [ReadRes.got] at Hrl
      rw [show (ReadRes.bytes bs).got = bs from rfl]
      have hb1 : 1 ≤ bs.length := by
        rcases bs with _ | ⟨b, bs⟩
        · have := Hr0 rfl; word
        · simp
      have hbl : bs.length ≤ (bsn.drop (sint.nat k)).length := by rw [hdl]; omega
      have hk'' : sint.nat k' = bs.length := by rw [hk']; omega
      have hkk : sint.nat (k + k') = sint.nat k + bs.length := by
        have : sint.nat k + sint.nat k' ≤ sint.nat buf.len := by rw [hk'']; word
        have : 1 ≤ sint.nat k' := by rw [hk'']; exact hb1
        rw [← hk'']; word
      rw [List.take_of_length_le hbl]
      wp_auto
      wp_for_post
      iframe
      iexists (k + k'), (bsn.take (sint.nat k) ++ (bs ++ (bsn.drop (sint.nat k)).drop bs.length)),
        got ++ bs
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      iframe n Hbuf HP
      ipureintro
      have hlt : (bsn.take (sint.nat k)).length = sint.nat k := by simp; omega
      refine ⟨by word, by word, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_take, List.length_drop]; omega
      · simp only [List.length_append, Hgl, hkk]
      · rw [hkk, List.take_append, hlt, show sint.nat k + bs.length - sint.nat k = bs.length by omega,
          List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil,
          List.take_of_length_le (show (bsn.take (sint.nat k)).length ≤ sint.nat k + bs.length
            by rw [hlt]; omega), Hgt]
    | eof =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      have hk0 : k + 0 = k := BitVec.add_zero k
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      cases err with
      | nil =>
        -- a nil `io.EOF` is not an error: the loop goes on
        wp_auto
        wp_for_post
        iframe
        iexists (k + 0), bsn, got
        rw [hk0]
        iframe n Hbuf HP
        ipureintro; exact ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩
      | ok i =>
        wp_auto
        wp_for_post
        iapply HΦ
        iexists got, bsn
        iframe HP Hbuf
        ipureintro
        refine ⟨Hbl, ⟨bsn.drop (sint.nat k), by rw [← Hgt, List.take_append_drop]⟩, ?_⟩
        intro h; cases h
    | err e =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      wp_auto
      wp_for_post
      iapply HΦ
      iexists got, bsn
      iframe HP Hbuf
      ipureintro
      refine ⟨Hbl, ⟨bsn.drop (sint.nat k), by rw [← Hgt, List.take_append_drop]⟩, ?_⟩
      intro h; cases h
  · -- the loop ends: `buf` is full
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    have hk : sint.Z k = sint.Z buf.len := by omega
    have hkn : sint.nat k = bs0.length := by
      rw [Hlen0.1]; show (sint.Z k).toNat = (sint.Z buf.len).toNat; rw [hk]
    (try wp_auto)
    iapply HΦ
    iexists got, bsn
    iframe HP Hbuf
    ipureintro
    have hg : got = bsn := by rw [← Hgt, List.take_of_length_le (by omega)]
    subst hg
    exact ⟨Hbl, List.prefix_refl _, fun _ => rfl⟩

/-- A whole frame read after whole frames `done`: it is the frame of a message of the stream's
protocol, which fits and meets `Φ`. -/
theorem recv_frame (Φ : message → IProp GF) (cn : Nat) (done : List message)
    (hdwf : ∀ m ∈ done, msgWf m) (n : w64) (body : List w8) (hn : uint.nat n = body.length) :
    recvTok (Gg := hG.goose_globalGS) cn true (wireProto Φ) (frames done ++ (u64Le n ++ body)) ⊢
      recvTok (Gg := hG.goose_globalGS) cn true (wireProto Φ) (frames done ++ (u64Le n ++ body)) ∗
      ∃ m, ⌜u64Le n ++ body = frame m ∧ msgWf m⌝ ∗ □ Φ m := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto $$ H
  isplitl [H]
  · iexact H
  unfold protoPrefix
  icases Hp with (%h | ⟨%ext, %hext, #Hext⟩)
  · exfalso
    have := congrArg List.length h
    simp [u64Le_length] at this
  unfold wireProto
  icases Hext with ⟨%ms, %hms, #Hall⟩
  obtain ⟨rfl, hwf⟩ := hms
  obtain ⟨m, hpre, hfr⟩ := parse_frames_prefix_wf done ms n body hwf hdwf hn hext
  have hm : m ∈ ms := hpre.subset (by simp)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  iexists m
  isplitr
  · ipureintro; exact ⟨hfr, hwf m hm⟩
  imodintro
  iapply BigSepL.bigSepL_lookup hi $$ Hall

theorem wp_readFrame (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (a : GoString) (Ψ : message → IProp GF) (done : List message)
    (hdwf : ∀ m ∈ done, msgWf m) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn true a ∗
      recvTok (Gg := hG.goose_globalGS) cn true (wireProto Ψ) (frames done) }}
    (App (Val (@! readFrame)) (Val #c))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok);
      if ok then ∃ m, b ↦*□ encMsg m ∗ □ Ψ m ∗ ⌜msgWf m⌝ ∗
        recvTok (Gg := hG.goose_globalGS) cn true (wireProto Ψ) (frames (done ++ [m]))
      else True }} := by
  wp_start as ⟨#Hc, Hr⟩
  wp_auto_lc 1
  ihave Hr := recvTok_L $$ Hr
  wp_apply wp_slice_make2 (V := w8) $$ [] as %hdr ⟨Hh, -⟩
  · ipureintro; decide
  wp_apply wp_readFull wp_Read c cn true a _ _ hdr _ $$ [Hc Hr Hh] as %ok ⟨%hd, %hb, Hr, Hh, %Hok⟩
  · iframe Hc Hr Hh
  cases ok
  · wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain ⟨hl, -, hg⟩ := Hok
  have hg := hg rfl
  subst hg
  simp only [List.length_replicate] at hl
  obtain ⟨n, rfl⟩ : ∃ n, hd = u64Le n := ⟨leToU64 hd, (leToU64_le hd hl).symm⟩
  wp_auto
  wp_apply github_com.tchajed.marshal.wp_ReadInt [] hdr _ n $$ [Hh] as %hdr' -
  · rw [List.append_nil]; iexact Hh
  wp_if_destruct
  · wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  wp_if_destruct
  · wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rename_i Hlo
  have hnZ : sint.Z n = uint.Z n := by word
  wp_apply wp_slice_make2 (V := w8) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; word
  wp_apply wp_readFull wp_Read c cn true a _ _ b _ $$ [Hc Hr Hb] as %ok ⟨%body, %bb, Hr, Hb, %Hok⟩
  · iframe Hc Hr Hb
  cases ok
  · wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain ⟨hbl, -, hg⟩ := Hok
  have hg := hg rfl
  subst hg
  simp only [List.length_replicate] at hbl
  have hn : uint.nat n = body.length := by rw [hbl]; word
  rw [List.append_assoc]
  ihave Hr := recvTokL_later $$ Hr
  iapply fupd_wp
  imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hr with Hr
  imodintro
  ihave ⟨Hr, %m, %hm, #HΨ⟩ := recv_frame Ψ cn done hdwf n body hn $$ Hr
  obtain ⟨hfr, hwf⟩ := hm
  have hbody : body = encMsg m := by
    unfold frame at hfr
    exact (List.append_inj hfr (by simp [u64Le_length])).2
  subst hbody
  have he := encMsg_length m
  unfold msgWf at hwf
  have hnv : sint.Z n = 48 + m.value'.length := by word
  wp_auto
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hb
  ihave %Hblen := ownSlice_len _ _ _ $$ Hb
  have h40 : sint.Z (W64 40) = 40 := rfl
  simp only [show 0 ≤ sint.Z (W64 40) ∧ sint.Z (W64 40) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap by word, _root_.and_self, ↓reduceIte]
  ipersist Hb
  ihave ⟨-, #Hb2⟩ := (ownSlice_split_all (W64 40) b DFrac.discard _ ⟨by word, by word⟩).1 $$ Hb
  rw [show sint.nat (W64 40) = 40 from rfl, encMsg_drop40]
  wp_apply github_com.tchajed.marshal.wp_ReadInt $$ [$Hb2] as %b2 -
  wp_if_destruct
  · wp_end
    simp only [↓reduceIte]
    iexists m
    iframe Hb HΨ
    rw [frames_append, frames_cons, show frames ([] : List message) = [] from rfl, List.append_nil, ← hfr]
    iframe Hr
    ipureintro; exact hwf
  · wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

theorem wp_deliver (nd : Loc) (Ψ : message → IProp GF) (amap : GMap w64 GoString)
    (ids : List w64) (m : message) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Ψ amap ids ∗ Ψ m ∗ ⌜msgWf m⌝ }}
    (App (Val (nd @!! go.GoType.PointerType tcpNode.ty @!! go!"deliver")) (Val #m))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hnd, HΨ, %hwf⟩
  unfold is_node
  icases Hnd with ⟨%am, %im, %ib, #Ham, #Him, #Hamap, #Hib, %Hids, #Hbags, #Hprotos⟩
  wp_auto
  wp_apply (lc := 1) wp_map_lookup2 $$ [$Hib] as -
  wp_if_destruct
  rotate_left
  · wp_end
  obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.1 Hif
  rw [hch]
  simp only [Option.getD_some]
  ihave #Hbag := BigSepM.bigSepM_lookup hch $$ Hbags
  icases Hbag with ⟨%γch, #Hbag⟩
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists message, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch, m
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    unfold nonblockingSendAu
    isplit
    · iapply bag_nonblocking_send_au γch ch _ m _ $$ Hlc1 Hbag [HΨ]
      · unfold inboxP
        iframe HΨ
        ipureintro; exact ⟨rfl, hwf⟩
      inext
      wp_auto
      wp_end
    · itrivial
  · wp_auto
    wp_end


theorem wp_readLoop (wp_SetReadDeadline : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (nd : Loc) (Ψ : message → IProp GF) (amap : GMap w64 GoString)
    (ids : List w64) (c : GoInterface) (cn : Nat) (a : GoString) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Ψ amap ids ∗ net.isConn c cn true a ∗
      recvTok (Gg := hG.goose_globalGS) cn true (wireProto Ψ) [] ∗
      rdlTok (Gg := hG.goose_globalGS) cn true false }}
    (App (Val (nd @!! go.GoType.PointerType tcpNode.ty @!! go!"readLoop")) (Val #c))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hnd, #Hc, Hr, Hrdl⟩
  ihave #Hconn := recvTok_connIs cn true (wireProto Ψ) [] $$ Hr
  wp_auto
  ihave HI : (∃ done : List message,
      "Hr" ∷ recvTok (Gg := hG.goose_globalGS) cn true (wireProto Ψ) (frames done) ∗
      "Hrdl" ∷ (∃ b, rdlTok (Gg := hG.goose_globalGS) cn true b) ∗
      "%Hd" ∷ ⌜∀ m ∈ done, msgWf m⌝ : IProp GF) $$ [Hr Hrdl]
  · iexists []
    rw [show frames ([] : List message) = [] from rfl]
    iframe Hr
    isplitl [Hrdl]
    · iexists false; iexact Hrdl
    ipureintro; simp
  wp_for HI
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  wp_apply time.wp_Now as %tm -
  wp_apply time.Time.wp_Add as %tm' -
  icases Hrdl with ⟨%b0, Hrdl⟩
  wp_apply wp_SetReadDeadline t cn true a la ra tm'
      (fun _ => iprop(∃ b, rdlTok (Gg := hG.goose_globalGS) cn true b)) $$ [Hrdl]
    as %err1 ⟨%res1, Hrdl, -⟩
  · iframe Hca
    imod deadline_au cn true (W64 1) _ b0 $$ Hrdl with ⟨%st, Hst, Hcl⟩
    imodintro
    iexists st
    iframe Hst
    iintro %res %st' %Hd Hst
    imod Hcl $$ %res %st' %Hd Hst with ⟨-, Hrdl⟩
    imodintro
    iexists st'.rdl
    iexact Hrdl
  wp_apply wp_readFrame wp_Read _ cn a Ψ done Hd $$ [$Hc $Hr] as %b %ok Hb
  cases ok
  · wp_auto
    wp_for_post
    wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) $$ [] as %err -
    · iframe Hca
      imod close_au cn true $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
      imodintro
      iexists st, dd
      iframe Hst Hdd
      iintro %res %st' %d' %Hd' Hst Hdd
      imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
      imodintro
      itrivial
    wp_end
  simp only [↓reduceIte]
  icases Hb with ⟨%m, #Hb, #HΨ, %hwf, Hr⟩
  wp_auto
  wp_apply wp_unmarshalMessage b DFrac.discard m hwf $$ [$Hb]
  wp_apply wp_deliver nd Ψ amap ids m $$ [$Hnd $HΨ]
  · ipureintro; exact hwf
  wp_for_post
  iframe
  iexists (done ++ [m])
  first | iframe Hr Hrdl | iframe Hr
  ipureintro
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Hd x hx
  · exact hwf

theorem wp_acceptLoop (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_SetReadDeadline : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (nd : Loc) (Ψ : message → IProp GF) (amap : GMap w64 GoString)
    (ids : List w64) (li : GoInterface) (l : w64) (a : GoString) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Ψ amap ids ∗ net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      addrProto (Gg := hG.goose_globalGS) a (wireProto Ψ) noProto }}
    (App (Val (nd @!! go.GoType.PointerType tcpNode.ty @!! go!"acceptLoop")) (Val #li))
  {{ RET #(); True }} := by
  -- the valid-address shape of `Accept` (the wildcard-aware spec's instance, `AtAddr.lean`)
  have wp_Accept := net.Listener.Accept.spec_addrOk wp_Accept
  wp_start as ⟨#Hnd, #Hli, Hlis, #Hla, #Hp⟩
  unfold net.isListener
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  wp_auto
  ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true : IProp GF)
    $$ [Hlis]
  · iframe Hlis
  wp_for HI
  wp_apply wp_Accept t l x a
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        connEnd (Gg := hG.goose_globalGS) cn true noProto (wireProto Ψ) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true ∗
        rdlTok (Gg := hG.goose_globalGS) cn true false))
      $$ [Hlis]
    as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hend, -, Hrdl⟩ | ⟨%k, Hlis, #Herr⟩)
  · iframe Hlt Hla
    iapply accept_rdl_au a (wireProto Ψ) noProto _ l true $$ Hp Hlis
  · subst Herr
    unfold connEnd
    icases Hend with ⟨-, Hr⟩
    wp_auto
    wp_apply wp_fork $$ [Hr Hrdl]
    · wp_apply wp_readLoop wp_SetReadDeadline wp_Read wp_Close nd Ψ amap ids c cn a $$ [$Hnd $Hc $Hr $Hrdl]
      itrivial
    wp_for_post
    iframe
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

/-- Appending the frame of a message that fits and meets `Ψ` keeps a stream whole frames of
the wire. -/
theorem wireProto_snoc (Ψ : message → IProp GF) (cid : Nat) (W : List w8) (m : message)
    (hwf : msgWf m) :
    □ wireProto Ψ cid W ∗ □ Ψ m ⊢ □ wireProto Ψ cid (W ++ frame m) := by
  iintro ⟨#HW, #HΨ⟩
  unfold wireProto
  icases HW with ⟨%ms, %hms, #Hall⟩
  obtain ⟨rfl, hwfs⟩ := hms
  imodintro
  iexists (ms ++ [m])
  isplitr
  · ipureintro
    refine ⟨by rw [frames_append, frames_cons]; simp [frames], ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hwfs x hx
    · exact hwf
  iapply BigSepL.bigSepL_append.2
  iframe Hall
  iapply BigSepL.bigSepL_singleton.2
  iexact HΨ


theorem connOK_open (Ψ : message → IProp GF) (cv : GoInterface) :
    connOK Ψ cv ⊢ ∃ (cn : Nat) (a : GoString) (W : List w8),
      net.isConn cv cn false a ∗ sendTok (Gg := hG.goose_globalGS) cn false (wireProto Ψ) W ∗
      □ wireProto Ψ cn W := by
  unfold connOK; exact .rfl

theorem connOK_close (Ψ : message → IProp GF) (cv : GoInterface) (cn : Nat) (a : GoString)
    (W : List w8) :
    net.isConn cv cn false a ∗ sendTok (Gg := hG.goose_globalGS) cn false (wireProto Ψ) W ∗
      □ wireProto Ψ cn W ⊢ connOK Ψ cv := by
  unfold connOK
  iintro ⟨#Hc, Hs, #HW⟩
  iexists cn, a, W
  iframe Hs
  iframe #

theorem wireProto_nil (Ψ : message → IProp GF) (cid : Nat) : ⊢ □ wireProto Ψ cid [] := by
  unfold wireProto
  imodintro
  iexists []
  isplitr
  · ipureintro; exact ⟨rfl, by simp⟩
  iapply BigSepL.bigSepL_nil.2
  iempintro


end specs

end Transport

open Transport

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : paxos.Assumptions]
variable [π : NetProtoGS]

set_option goose.wp.extras true

theorem tcpNode.serve.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_SetReadDeadline : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    tcpNode.serve.spec (GF := GF) (hG := hG) :=
    fun Ψ _ nd amap ids a tries => by
  -- the valid-address shape of `Listen` (the wildcard-aware spec's instance, `AtAddr.lean`)
  have wp_Listen := net.Listen.spec_addrOk wp_Listen
  wp_start as ⟨#Hnd, #Hp⟩
  ihave %Hok := addrTok_ok a $$ [Hp]
  · iapply addrProto_tok $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i : IProp GF) $$ [i]
  · iexists _; iexact i
  wp_for HI
  wp_if_destruct
  · wp_apply wp_Listen go!"tcp" net.tcpNet_tcp a as %lv %err Hres
    · iframe %Hok
      iapply listen_au $$ Hp
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · subst He
      wp_auto
      wp_apply wp_fork $$ [Hlis]
      · wp_apply wp_acceptLoop wp_Accept wp_SetReadDeadline wp_Read wp_Close nd Ψ amap ids lv l a
          $$ [$Hnd $Hl $Hlis $Hla $Hp]
        itrivial
      wp_for_post
      iapply HΦ
      itrivial
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists _
      iexact i
  · wp_end

theorem tcpNetwork.send.wp_proof (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG))
    (wp_SetWriteDeadline : net.Conn.SetWriteDeadline.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    tcpNetwork.send.spec (GF := GF) (hG := hG) :=
    fun Ψ _ nt nd amap ids me m => by
  wp_start as ⟨#Hnd, Hnet, #HΨ, %hwf⟩
  ihave ⟨%et, #Het⟩ := et_init $$ Hpkg
  ihave ⟨%ed, #Hed⟩ := ed_init $$ Hpkg
  unfold is_node
  icases Hnd with ⟨%am, %im, %ib, #Ham, #Him, #Hamap, #Hib, %Hids, #Hbags, #Hprotos⟩
  unfold own_net
  icases Hnet with ⟨%cm, %conns, #Hnode, #Hme, #Hconns, Hcm, Hall⟩
  wp_auto
  wp_apply wp_encodeFrame m hwf as %f Hf
  wp_apply wp_map_lookup2 $$ [$Hcm] as Hcm
  wp_if_destruct
  · obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.1 Hif
    rw [hcv]
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_delete hcv).1 $$ Hall with ⟨Hok, Hall⟩
    icases connOK_open Ψ cv $$ Hok with ⟨%cn, %a, %W, #Hc, Hs, #HW⟩
    ihave #HW' := wireProto_snoc Ψ cn W m hwf $$ [$HW $HΨ]
    wp_apply wp_writeFrame wp_SetWriteDeadline wp_Write cv cn a f (frame m) _ _ W $$ [$Hc $Hs $HW' $Hf]
      as %ok ⟨Hf, %w, %hw, Hs⟩
    cases ok
    · ihave #Hconn := sendTok_connIs cn false _ _ $$ Hs
      iunfold net.isConn at Hc
      icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
      subst Hct
      wp_auto
      wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %err -
      · iframe Hca
        imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd' Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
        imodintro
        itrivial
      wp_apply wp_mapDelete $$ [$Hcm] as Hcm
      rw [show GMap.delete m.to' conns = Iris.Std.PartialMap.delete conns m.to' from rfl]
      ihave Hst : (∃ conns' : GMap w64 GoInterface, cm ↦$ conns' ∗
          ([∗map] cv ∈ conns', connOK Ψ cv) ∗ ⌜conns' !! m.to' = none⌝ : IProp GF) $$ [Hcm Hall]
      · iexists _
        iframe Hcm
        isplitl [Hall]
        · iexact Hall
        ipureintro; exact GMap.lookup_delete conns m.to'
      icases Hst with ⟨%conns', Hcm, Hall, %hnone⟩
      wp_apply wp_map_lookup2 $$ [$Hamap] as -
      wp_if_destruct
      · obtain ⟨a2, ha⟩ := Option.isSome_iff_exists.1 Hif
        rw [ha]
        simp only [Option.getD_some]
        ihave #Hpa := BigSepM.bigSepM_lookup ha $$ Hprotos
        ihave %Hok2 := addrTok_ok a2 $$ [Hpa]
        · iapply addrProto_tok $$ Hpa
        wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp a2 _ et ed iprop(True)
            (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (wireProto Ψ) noProto [] [] ∗
              connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
          as %c2 %err (⟨%Herr, %cn2, #Hc2, ⟨Hend, -⟩⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
        · iframe Het Hed
          isplitr
          · ipureintro; exact Hok2
          isplit
          · itrivial
          · iapply dial_au a2 (wireProto Ψ) noProto $$ Hpa
        · subst Herr
          iunfold connEnd at Hend
          icases Hend with ⟨Hs2, -⟩
          wp_auto
          ihave #HW0 := wireProto_nil Ψ cn2
          ihave #HW1 := wireProto_snoc Ψ cn2 [] m hwf $$ [$HW0 $HΨ]
          wp_apply wp_writeFrame wp_SetWriteDeadline wp_Write c2 cn2 a2 f (frame m) _ _ [] $$ [$Hc2 $Hs2 $HW1 $Hf]
            as %ok ⟨Hf, %w2, %hw2, Hs2⟩
          cases ok
          · ihave #Hconn2 := sendTok_connIs cn2 false _ _ $$ Hs2
            iunfold net.isConn at Hc2
            icases Hc2 with ⟨%t2, %la2, %ra2, %Hct2, #Hca2⟩
            subst Hct2
            wp_auto
            wp_apply wp_Close t2 cn2 false a2 la2 ra2 (fun _ => iprop(True)) $$ [] as %err -
            · iframe Hca2
              imod close_au cn2 false $$ Hconn2 with ⟨%st, %dd, Hst, Hdd, Hcl⟩
              imodintro
              iexists st, dd
              iframe Hst Hdd
              iintro %res %st' %d' %Hd' Hst Hdd
              imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
              imodintro
              itrivial
            iapply HΦ
            iexists cm, conns'
            iframe Hcm Hall
            iframe #
          · wp_auto
            wp_apply wp_mapInsert $$ [$Hcm] as Hcm
            have hw2e := hw2.2 rfl
            subst hw2e
            iapply HΦ
            iexists cm, _
            iframe Hcm
            iframe #
            iapply (BigSepM.bigSepM_insert hnone).2
            iframe Hall
            iapply connOK_close Ψ c2 cn2 a2 _ $$ [$Hc2 $Hs2 $HW1]
        · icases net.opErr_netErr _ _ _ _ _ $$ Herr with %Hne
          obtain ⟨pe, rfl⟩ := Hne
          wp_auto
          iapply HΦ
          iexists cm, conns'
          iframe Hcm Hall
          iframe #
      · iapply HΦ
        iexists cm, conns'
        iframe Hcm Hall
        iframe #
    · wp_auto
      have hwe := hw.2 rfl
      subst hwe
      iapply HΦ
      iexists cm, conns
      iframe Hcm
      iframe #
      iapply (BigSepM.bigSepM_delete hcv).2
      iframe Hall
      iapply connOK_close Ψ cv cn a _ $$ [$Hc $Hs $HW']
  · ihave Hst : (∃ conns' : GMap w64 GoInterface, cm ↦$ conns' ∗
        ([∗map] cv ∈ conns', connOK Ψ cv) ∗ ⌜conns' !! m.to' = none⌝ : IProp GF) $$ [Hcm Hall]
    · iexists _
      iframe Hcm
      isplitl [Hall]
      · iexact Hall
      ipureintro; simpa using Hif
    icases Hst with ⟨%conns', Hcm, Hall, %hnone⟩
    wp_apply wp_map_lookup2 $$ [$Hamap] as -
    wp_if_destruct
    · obtain ⟨a2, ha⟩ := Option.isSome_iff_exists.1 Hif
      rw [ha]
      simp only [Option.getD_some]
      ihave #Hpa := BigSepM.bigSepM_lookup ha $$ Hprotos
      ihave %Hok2 := addrTok_ok a2 $$ [Hpa]
      · iapply addrProto_tok $$ Hpa
      wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp a2 _ et ed iprop(True)
          (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (wireProto Ψ) noProto [] [] ∗
            connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
        as %c2 %err (⟨%Herr, %cn2, #Hc2, ⟨Hend, -⟩⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
      · iframe Het Hed
        isplitr
        · ipureintro; exact Hok2
        isplit
        · itrivial
        · iapply dial_au a2 (wireProto Ψ) noProto $$ Hpa
      · subst Herr
        iunfold connEnd at Hend
        icases Hend with ⟨Hs2, -⟩
        wp_auto
        ihave #HW0 := wireProto_nil Ψ cn2
        ihave #HW1 := wireProto_snoc Ψ cn2 [] m hwf $$ [$HW0 $HΨ]
        wp_apply wp_writeFrame wp_SetWriteDeadline wp_Write c2 cn2 a2 f (frame m) _ _ [] $$ [$Hc2 $Hs2 $HW1 $Hf]
          as %ok ⟨Hf, %w2, %hw2, Hs2⟩
        cases ok
        · ihave #Hconn2 := sendTok_connIs cn2 false _ _ $$ Hs2
          iunfold net.isConn at Hc2
          icases Hc2 with ⟨%t2, %la2, %ra2, %Hct2, #Hca2⟩
          subst Hct2
          wp_auto
          wp_apply wp_Close t2 cn2 false a2 la2 ra2 (fun _ => iprop(True)) $$ [] as %err -
          · iframe Hca2
            imod close_au cn2 false $$ Hconn2 with ⟨%st, %dd, Hst, Hdd, Hcl⟩
            imodintro
            iexists st, dd
            iframe Hst Hdd
            iintro %res %st' %d' %Hd' Hst Hdd
            imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
            imodintro
            itrivial
          iapply HΦ
          iexists cm, conns'
          iframe Hcm Hall
          iframe #
        · wp_auto
          wp_apply wp_mapInsert $$ [$Hcm] as Hcm
          have hw2e := hw2.2 rfl
          subst hw2e
          iapply HΦ
          iexists cm, _
          iframe Hcm
          iframe #
          iapply (BigSepM.bigSepM_insert hnone).2
          iframe Hall
          iapply connOK_close Ψ c2 cn2 a2 _ $$ [$Hc2 $Hs2 $HW1]
      · icases net.opErr_netErr _ _ _ _ _ $$ Herr with %Hne
        obtain ⟨pe, rfl⟩ := Hne
        wp_auto
        iapply HΦ
        iexists cm, conns'
        iframe Hcm Hall
        iframe #
    · iapply HΦ
      iexists cm, conns'
      iframe Hcm Hall
      iframe #

theorem tcpNode.network.wp_proof : tcpNode.network.spec (GF := GF) (hG := hG) :=
    fun Ψ nd amap ids id => by
  wp_start as #Hnd
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %cm Hcm
  rename_i nt
  irename «$r0» => Hnt
  iStructNamed Hnt
  ipersist node
  ipersist me
  ipersist conns
  imodintro
  iapply HΦ
  unfold own_net
  iexists cm, ∅
  iframe Hcm
  isplitr
  · iexact node
  isplitr
  · iexact me
  isplitr
  · iexact conns
  iapply BigSepM.bigSepM_empty.2
  iempintro

theorem tcpNetwork.recv.wp_proof : tcpNetwork.recv.spec (GF := GF) (hG := hG) :=
    fun Ψ nt nd amap ids me tmo hme => by
  wp_start as ⟨#Hnd, Hnet⟩
  unfold is_node
  icases Hnd with ⟨%am, %im, %ib, #Ham, #Him, #Hamap, #Hib, %Hids, #Hbags, #Hprotos⟩
  unfold own_net
  icases Hnet with ⟨%cm, %conns, #Hnode, #Hme, #Hconns, Hcm, Hall⟩
  wp_auto
  obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.1 ((Hids me).2 hme)
  wp_apply (lc := 4) wp_map_lookup1 $$ [$Hib] as -
  rw [hch]
  simp only [Option.getD_some]
  ihave #Hbag := BigSepM.bigSepM_lookup hch $$ Hbags
  icases Hbag with ⟨%γch, #Hbag⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply time.After.spec_pkgInit time.wp_After _ $$ [$Htime] as %ach %γa #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists message, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au γch ch _ _ $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %v HP
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe HP
    iexists cm, conns
    iframe
    iframe #
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γa ach _ _ $$ [$Hlc3 $Hlc4] Hafter
    inext
    iintro %t -
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · iexists cm, conns
      iframe
      iframe #
    · itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem tcpNetwork.poll.wp_proof : tcpNetwork.poll.spec (GF := GF) (hG := hG) :=
    fun Ψ nt nd amap ids me hme => by
  wp_start as ⟨#Hnd, Hnet⟩
  unfold is_node
  icases Hnd with ⟨%am, %im, %ib, #Ham, #Him, #Hamap, #Hib, %Hids, #Hbags, #Hprotos⟩
  unfold own_net
  icases Hnet with ⟨%cm, %conns, #Hnode, #Hme, #Hconns, Hcm, Hall⟩
  wp_auto
  obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.1 ((Hids me).2 hme)
  wp_apply (lc := 1) wp_map_lookup1 $$ [$Hib] as -
  rw [hch]
  simp only [Option.getD_some]
  ihave #Hbag := BigSepM.bigSepM_lookup hch $$ Hbags
  icases Hbag with ⟨%γch, #Hbag⟩
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists message, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    unfold nonblockingRecvAu
    isplit
    · iapply bag_nonblocking_recv_au γch ch _ _ $$ Hlc1 Hbag
      inext
      iintro %v HP
      wp_auto
      iapply HΦ
      simp only [↓reduceIte]
      iframe HP
      iexists cm, conns
      iframe
      iframe #
    · itrivial
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl
    · iexists cm, conns
      iframe
      iframe #
    · itrivial


theorem newTCPNode.wp_proof : newTCPNode.spec (GF := GF) (hG := hG) :=
    fun Ψ _ am amap sl ids dq => by
  wp_start as ⟨Ham, Hsl, #Hprotos⟩
  iapply fupd_wp
  imod ownMap_persist $$ Ham with #Ham
  imodintro
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %im Him
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
  ihave HI : (∃ (i : w64) (idv : w64) (ib : GMap w64 Loc),
      "i" ∷ i_ptr ↦ i ∗
      "id" ∷ id_ptr ↦ idv ∗
      "Him" ∷ im ↦$ ib ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ ∗
      "%Hdom" ∷ ⌜∀ id, (ib !! id).isSome ↔ id ∈ ids.take (sint.nat i)⌝ ∗
      "#Hbags" ∷ ([∗map] id ↦ ch ∈ ib, ∃ γ, isChanBag γ ch (inboxP Ψ id)) : IProp GF)
      $$ [i id Him]
  · iexists W64 0, _, ∅
    iframe
    isplitr
    · ipureintro; constructor
      · decide
      · word
    isplitr
    · ipureintro; intro id; simp [show sint.nat (0#64) = 0 from rfl]
    · iapply BigSepM.bigSepM_empty.2; iempintro
  wp_for HI
  wp_if_destruct
  · simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    list_elem ids (sint.nat i) as x
    wp_apply wp_load_slice_index sl (sint.Z i) ids dq x Hi.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hx_lookup
    wp_apply (chan.wp_make2 (V := message) (W64 1024)) as %ch %γch ⟨#Hch, %Hcap, Hown⟩
    · ipureintro; decide
    iapply fupd_wp
    imod (start_bag (V := message) (inboxP Ψ x) (.Buffered []) ch γch trivial) $$ Hch Hown with #Hbag
    imodintro
    wp_apply wp_mapInsert $$ [$Him] as Him
    wp_for_post
    iframe
    iexists i + W64 1, x, _
    iframe
    isplitr
    · ipureintro; constructor <;> word
    isplitr
    · ipureintro
      intro id
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn, List.take_add_one, Hx_lookup]
      by_cases h : x = id
      · subst h; simp
      · rw [GMap.lookup_insert_ne _ _ h, Hdom]
        simp [Ne.symm h]
    rw [show (<[x := ch]>ib : GMap w64 Loc) = Iris.Std.PartialMap.insert ib x ch from rfl]
    iapply BigSepM.bigSepM_insert_elim $$ [] Hbags
    iexists γch
    iexact Hbag
  · have hlen : sint.nat i = ids.length := by
      rw [Hsllen.1]; word
    rw [hlen, List.take_length] at Hdom
    rename_i nd
    irename «$r0» => Hnd
    iStructNamed Hnd
    ipersist addrs
    ipersist inbox
    imod ownMap_persist $$ Him with #Him
    imodintro
    iapply HΦ
    iframe Hsl
    unfold is_node
    iexists am, im, ib
    iframe #
    ipureintro; exact Hdom

end proofs

end github_com.xiang90.paxos

end Perennial
