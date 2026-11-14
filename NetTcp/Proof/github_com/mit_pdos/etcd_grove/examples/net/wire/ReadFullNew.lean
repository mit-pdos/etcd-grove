/-
The proof of `wire.ReadFull` (`NetTcp/Spec/.../wire/ReadFull.lean`): a loop over `c.Read(buf[n:])`
(`net.Conn.Read.spec`), each read's update made from the caller's accessor (its outcome kept as
`ReadInfo`: `ReadPost` without the end's state, which goes back through the accessor); the
invariant: `n` bytes read, the first `n` of `buf` the bytes after `r` of a prefix `sent` of the
other end's bytes. Also `ReadFull.owned`, the spec for a thread that owns its end.
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFullNew
public import NetTcp.Spec.net.Conn__Read

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem buf_rejoin (buf : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    slice.slice buf w8 (W64 0) k ↦* xs -∗ slice.slice buf w8 k buf.len ↦* ys -∗
      (buf ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice buf (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k buf (DFrac.own 1) xs ys (W64 0) buf.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

theorem readRes_inj {bs bs' : List w8} {c c' : w64} (h : readRes bs c = readRes bs' c') :
    bs = bs' ∧ c = c' := by
  unfold readRes at h
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

/-- What a read returned, without the end's state (`ReadPost`'s cases): the position after it is
`r'`. -/
def ReadInfo (hT : TcpGS GF) (cn : Nat) (s : Bool) (n : w64) (r : Nat) (res : val) (r' : Nat) :
    IProp GF :=
  iprop(⌜res = readRes [] 2 ∧ r' = r⌝ ∨ ⌜n = 0 ∧ res = readRes [] 0 ∧ r' = r⌝ ∨
    (∃ (bs sent : GoString), ⌜1 ≤ bs.length ∧ bs.length ≤ n.toNat ∧
        sent.length = r + bs.length ∧ sent.drop r = bs ∧ res = readRes bs 0 ∧ r' = r + bs.length⌝ ∗
      tcpOutLb hT cn (!s) sent) ∨
    (∃ sent : GoString, ⌜sent.length = r ∧ res = readRes [] 1 ∧ r' = r⌝ ∗ tcpFin hT cn (!s) sent))

theorem readPost_info (hT : TcpGS GF) (cn : Nat) (s : Bool) (n : w64) (st : TcpEnd) (r : Nat)
    (res : val) :
    ReadPost hT cn s n st r res ⊢ ∃ st' r', tcpEnd hT cn s st' r' ∗ ReadInfo hT cn s n r res r' := by
  iintro H
  unfold ReadPost ReadInfo
  icases H with (⟨%Hr, Hend⟩ | ⟨%Hr, Hend⟩ | ⟨%bs, %sent, %Hr, #Hlb, Hend⟩ | ⟨%sent, %Hr, #Hfin, Hend⟩)
  · iexists _, r
    iframe Hend
    ileft
    ipureintro; exact ⟨Hr, rfl⟩
  · iexists st, r
    iframe Hend
    iright; ileft
    ipureintro; exact ⟨Hr.2.1, Hr.2.2, rfl⟩
  · iexists st, (r + bs.length)
    iframe Hend
    iright; iright; ileft
    iexists bs, sent
    iframe Hlb
    ipureintro
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := Hr
    exact ⟨h1, h2, h3, h4, h5, rfl⟩
  · iexists st, r
    iframe Hend
    iright; iright; iright
    iexists sent
    iframe Hfin
    ipureintro
    obtain ⟨-, h1, h2⟩ := Hr
    exact ⟨h1, h2, rfl⟩

theorem ReadFull.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    ReadFull.spec (GF := GF) (hG := hG) := by
  intro c cn s a buf bs0 P r sent0 eof hsent0
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, Hbuf, #Heof, Hend, #Hlb0, #Hacc⟩
  subst Hct
  wp_auto
  ihave %Hlen0 := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave HI : (∃ (k : w64) (bsn : List w8) (sent : GoString),
      "n" ∷ n_ptr ↦ k ∗ "Hbuf" ∷ buf ↦* bsn ∗
      "Hend" ∷ P (r + sint.nat k) ∗
      "#Hlb" ∷ tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len ∧ bsn.length = bs0.length ∧
        sent.length = r + sint.nat k ∧ sent.drop r = bsn.take (sint.nat k)⌝ : IProp GF)
      $$ [n Hbuf Hend]
  · iexists W64 0, bs0, sent0
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.add_zero]
    iframe n Hbuf Hlb0 Hend
    ipureintro
    refine ⟨by decide, by word, rfl, hsent0, ?_⟩
    rw [← hsent0]; simp
  wp_for HI
  wp_if_destruct
  · -- the loop body: a read into `buf[k:]`
    obtain ⟨Hk0, Hkl, Hbl, Hsl, Hsd⟩ := Hinv
    rw [if_pos ⟨Hk0, Hkl, Hwf.2⟩]
    icases (ownSlice_split_all k buf _ bsn ⟨Hk0, Hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    wp_apply wp_Read t cn s a (slice.slice buf w8 k buf.len) (bsn.drop (sint.nat k)) eof
        (fun res => iprop(∃ r', P r' ∗ ReadInfo (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s
          (slice.slice buf w8 k buf.len).len (r + sint.nat k) res r')) $$ [Hb2 Hend]
      as %k' %err ⟨%bs, %code, %bs', ⟨%r', Hend, HQ⟩, Hb2, %Hout⟩
    · iframe Hc Hb2 Heof
      imod Hacc $$ %(r + sint.nat k) Hend with ⟨%st, HE, Hcl⟩
      imodintro
      iexists st, (r + sint.nat k)
      iframe HE
      iintro %res Hpost
      icases readPost_info _ cn s _ st _ res $$ Hpost with ⟨%st', %r', HE, Hinfo⟩
      imod Hcl $$ %st' %r' HE with HP
      imodintro
      iexists r'
      iframe HP Hinfo
    have hdl : (bsn.drop (sint.nat k)).length = sint.nat buf.len - sint.nat k := by
      rw [List.length_drop, Hbl, Hlen0.1]
    have hsl : (slice.slice buf w8 k buf.len).len = buf.len - k := rfl
    have hsn : sint.nat (buf.len - k) = sint.nat buf.len - sint.nat k := by word
    iunfold ReadInfo at HQ
    icases HQ with (%Hr | %Hr | ⟨%bs2, %sent2, %Hr, #Hlb2⟩ | ⟨%sent2, %Hr, #Hfin⟩)
    · -- a failure
      obtain ⟨Hr, rfl⟩ := Hr
      obtain ⟨rfl, rfl⟩ := readRes_inj Hr
      rcases Hout with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, -, rfl, ⟨pe, rfl⟩, rfl⟩
      · cases h0
      · cases h1
      wp_auto
      wp_for_post
      iapply HΦ
      iexists (r + sint.nat k), _
      iframe Hend
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      iframe Hbuf
      have hne : k + 0 ≠ buf.len := by
        intro h; rw [show k + 0 = k from BitVec.add_zero k] at h; subst h; omega
      rw [decide_eq_false hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitl
      · ipureintro
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      · itrivial
    · -- an empty buffer: not with `k < len(buf)`
      obtain ⟨hz, -⟩ := Hr
      exfalso
      have : sint.Z buf.len - sint.Z k = 0 := by word
      omega
    · -- the next bytes
      obtain ⟨hb1, hbn, hsl2, hsd2, hres, rfl⟩ := Hr
      obtain ⟨rfl, rfl⟩ := readRes_inj hres
      rcases Hout with ⟨-, hk', rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h0, -⟩
      · have hlenk : BitVec.toNat (buf.len - k) = sint.nat buf.len - sint.nat k := by word
        have hbl : bs.length ≤ (bsn.drop (sint.nat k)).length := by rw [hdl]; omega
        have hk'' : sint.nat k' = bs.length := by rw [hk']; omega
        have hkk : sint.nat (k + k') = sint.nat k + bs.length := by
          have : sint.nat k + bs.length ≤ sint.nat buf.len := by omega
          rw [← hk'']; word
        rw [List.take_of_length_le hbl]
        icases tcpOutLb_valid _ cn (!s) sent sent2 $$ Hlb Hlb2 with %Hpre
        have hpre : sent <+: sent2 := by
          rcases Hpre with h | h
          · exact h
          · have := h.length_le; omega
        obtain ⟨tl, rfl⟩ := hpre
        have htl : tl = bs := by
          rw [← hsd2, ← Hsl, List.drop_left]
        subst htl
        wp_auto
        wp_for_post
        iframe
        iexists (k + k'), (bsn.take (sint.nat k) ++ (tl ++ (bsn.drop (sint.nat k)).drop tl.length)),
          sent ++ tl
        ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
        rw [hkk, Nat.add_assoc]
        iframe n Hbuf Hend Hlb2
        ipureintro
        have hlt : (bsn.take (sint.nat k)).length = sint.nat k := by simp; omega
        refine ⟨by word, by word, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_take, List.length_drop]; omega
        · simp only [List.length_append, Hsl]; omega
        · have key : (bsn.take (sint.nat k) ++ (tl ++ (bsn.drop (sint.nat k)).drop tl.length)).take
              (sint.nat k + tl.length) = bsn.take (sint.nat k) ++ tl := by
            rw [List.take_append, hlt, show sint.nat k + tl.length - sint.nat k = tl.length by omega,
              List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil,
              List.take_of_length_le (show (bsn.take (sint.nat k)).length ≤ sint.nat k + tl.length
                by rw [hlt]; omega)]
          rw [List.drop_append_of_le_length (by omega), Hsd, key]
      · cases h1
      · exact absurd rfl h0
    · -- EOF
      obtain ⟨hsl2, hres, rfl⟩ := Hr
      obtain ⟨rfl, rfl⟩ := readRes_inj hres
      rcases Hout with ⟨h0, -⟩ | ⟨-, rfl, Herr, rfl⟩ | ⟨-, h1, -⟩
      · cases h0
      · subst Herr
        have hk0 : k + 0 = k := BitVec.add_zero k
        ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
        rw [List.take_append_drop]
        cases err with
        | nil =>
          -- a nil `io.EOF` would not end the loop: it goes on
          wp_auto
          wp_for_post
          iframe
          iexists (k + 0), bsn, sent
          rw [hk0]
          iframe n Hbuf Hend Hlb
          ipureintro; exact ⟨Hk0, Hkl, Hbl, Hsl, Hsd⟩
        | ok i =>
          have hne : k + 0 ≠ buf.len := by rw [hk0]; intro h; subst h; omega
          wp_auto
          rw [decide_eq_false hne]
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iexists (r + sint.nat k), bsn
          iframe Hend Hbuf
          simp only [Bool.false_eq_true, ↓reduceIte]
          isplitl
          · ipureintro; exact Hbl
          · itrivial
      · exact absurd rfl h1
  · -- the loop ends: `buf` is full
    obtain ⟨Hk0, Hkl, Hbl, Hsl, Hsd⟩ := Hinv
    have hk : sint.Z k = sint.Z buf.len := by omega
    have hkn : sint.nat k = bs0.length := by
      rw [Hlen0.1]; show (sint.Z k).toNat = (sint.Z buf.len).toNat; rw [hk]
    (try wp_auto)
    iapply HΦ
    iexists (r + sint.nat k), bsn
    iframe Hend Hbuf
    simp only [↓reduceIte]
    isplitl
    · ipureintro; exact Hbl
    iexists sent
    iframe Hlb
    ipureintro
    refine ⟨by rw [hkn], Hsl, ?_⟩
    rw [Hsd, List.take_of_length_le (by omega)]

/-- `ReadFull` on an end the calling thread owns: the end's state is the caller's before and
after (`P r := ∃ st, tcpEnd .. st r`). -/
theorem ReadFull.owned (wp_ReadFull : ReadFull.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (buf : GoSlice) (bs0 : List w8)
    (st : TcpEnd) (r : Nat) (sent0 : GoString) (eof : GoInterface) (hsent0 : sent0.length = r) :
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
      tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent0 }}
    (App (App (Val (@! wire.ReadFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (st' : TcpEnd) (r' : Nat) (bs' : List w8),
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r' ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length⌝ ∗
      if ok then ∃ sent : GoString,
        tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent ∗
        ⌜r' = r + bs0.length ∧ sent.length = r' ∧ sent.drop r = bs'⌝
      else True }} := by
  iintro %Φ ⟨#Hc, Hbuf, #Heof, Hend, #Hlb0⟩ HΦ
  iapply wp_ReadFull c cn s a buf bs0
      (fun r => iprop(∃ st, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r)) r
      sent0 eof hsent0 $$ [Hbuf Hend]
  · iframe Hc Hbuf Heof Hlb0
    isplitl [Hend]
    · iexists st
      iexact Hend
    imodintro
    iintro %r0 ⟨%st0, HE⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    iexists st0
    iframe HE
    iintro %st' %r' HE
    imod Hcl
    imodintro
    iexists st'
    iexact HE
  inext
  iintro %ok ⟨%r', %bs', ⟨%st', HE⟩, Hbuf, Hrest⟩
  iapply HΦ
  iexists st', r', bs'
  iframe HE Hbuf Hrest

end proof

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
