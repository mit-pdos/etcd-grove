/-
`epaxos.Accept`'s `Unmarshal` (internal to the wire package).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosDecode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Marshal.EpaxosFixed

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem list20 {α} (d : List α) (h : d.length = 20) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19,
      d = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
      a19, rfl⟩

theorem msg_accept (m : Msg) (h : m.kind = some MsgKind.accept ∧ m.wf) :
    ∃ p, m = .accept p ∧ cmdsWf p.command ∧ depsWf p.deps := by
  obtain ⟨hk, hw⟩ := h
  cases m <;> simp [Msg.kind] at hk
  exact ⟨_, rfl, hw⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]
variable [EpBufioDeps GF]

set_option goose.wp.extras true

theorem epaxos.Unmarshal.spec_accept : epaxos.Unmarshal.spec (GF := GF) MsgKind.accept := by
  dsimp only [epaxos.Unmarshal.spec, MsgKind.ty]
  intro l br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  iunfold ownAny at Hl
  icases Hl with ⟨%v0, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨LeaderId, Replica, Instance, Ballot, Command, Seq, Deps, -⟩
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) epaxos.byteReader.ty = true := by
    go_type_set
  wp_auto
  rw [hts]
  simp only [↓reduceIte]
  wp_auto
  ihave Hb := zero_array b_ptr (W64 20) 20 rfl 20 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 20) (W64 20) 20 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 20) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
    as %n %err ⟨%d, %Hd, Hbs, Hown⟩
  obtain ⟨-, hdl, hiff⟩ := Hd
  rcases err with ei | _
  · -- an error
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    iexists d
    iframe Hown
    iunfold ownAny
    iexists v0
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe LeaderId Replica Instance Ballot Command Seq Deps

  have hd20 : d.length = 20 := by
    have := hiff.mp rfl
    have h20 : sint.Z (W64 20) = 20 := rfl
    simp only [List.length_take, List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, rfl⟩ :=
    list20 d hd20
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.take_replicate,
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil, Nat.min_self]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 w0, ← encoding.binary.leToU32_4 w4,
    ← encoding.binary.leToU32_4 w8', ← encoding.binary.leToU32_4 w12,
    ← encoding.binary.leToU32_4 w16]
  -- the commands' count
  have hdr : ∀ (p : model.Accept) (t ext : List w8),
      [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++ t <+:
        Msg.body (.accept p) ++ ext →
      t <+: encLen p.command.length ++ ((p.command.map encCommand).flatten ++
        encDeps p.deps ++ ext) := by
    intro p t ext hp
    simp only [Msg.body, encAccept, encCmds] at hp
    exact pfx_skip (P := [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19])
      (P' := u32Le p.leaderId ++ u32Le p.replica ++ u32Le p.inst ++ u32Le p.ballot ++ u32Le p.seq)
      (by simp [u32Le_length]) (by simpa only [List.append_assoc] using hp)
  ihave #Hn1 := nextIs_shift rd R [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] Msg.body _ varintEnc (fun _ => True) (fun m ext t hwf hp => by
      obtain ⟨p, rfl, hc, -⟩ := msg_accept m hwf
      exact varint_next _ (by unfold cmdsWf at hc; omega) _ _ (hdr p t ext hp)) $$ Hnext
  have hrv := epaxos.readVarint.spec_holds (GF := GF)
  unfold epaxos.readVarint.spec at hrv
  wp_apply hrv br rd _ $$ [$Hpkg $Hpkg2 $Hown $Hn1] as %x %err1 H1
  icases H1 with (⟨%he1, Hown⟩ | ⟨%he1, %d1, Hown⟩)
  rotate_left
  · -- an error
    rcases err1 with ei | _
    · wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; simp
      iexists _ ++ d1
      simp only [List.append_assoc]
      iframe Hown
      iunfold ownAny
      iexists epaxos.Accept.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7])
          (leToU32 [w8', w9, w10, w11]) (leToU32 [w12, w13, w14, w15]) v0.Command' (leToU32 [w16, w17, w18, w19]) v0.Deps'
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe LeaderId Replica Instance Ballot Command Seq Deps
    · exact absurd rfl he1
  subst he1
  rw [List.append_assoc]
  ihave ⟨Hown, Hp1⟩ := nextIs_read br rd R (_ ++ varintEnc x) Msg.body _ $$ [$Hnext $Hown]
  imod Hp1 with %Hp1
  obtain ⟨n, hn, hxn⟩ : ∃ n : Nat, n < 2 ^ 62 ∧ x = W64 (n : Int) := by
    obtain ⟨m, ext, hwf, hp⟩ := Hp1
    obtain ⟨p, rfl, hc, -⟩ := msg_accept m hwf
    have := hdr p (varintEnc x) ext hp
    exact ⟨_, hc.1, (varint_head x _ (by unfold cmdsWf at hc; omega) [] _ (by simpa using this)).1⟩
  subst hxn
  have hnZ : sint.Z (W64 (n : Int)) = n := sint_Z_W64_length (by omega)
  wp_auto
  wp_apply (wp_slice_make2 (V := state.Command)) as %cs ⟨Hcs, -⟩
  · ipureintro; omega
  (try wp_auto)
  have hsn : sint.nat (W64 (n : Int)) = n := by
    show (sint.Z (W64 (n : Int))).toNat = n; rw [hnZ]; simp
  rw [hsn]
  -- after the header and the count, the stream is the commands, then the rest
  have hafter : ∀ (p : model.Accept) (u ext : List w8), cmdsWf p.command →
      [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
        (varintEnc (W64 (n : Int)) ++ u) <+: Msg.body (.accept p) ++ ext →
      n = p.command.length ∧
        u <+: (p.command.map encCommand).flatten ++ (encDeps p.deps ++ ext) := by
    intro p u ext hc hp
    have h1 := hdr p _ ext hp
    obtain ⟨h2, h3⟩ := varint_head _ p.command.length (by unfold cmdsWf at hc; omega) _ _
      (by simpa only [List.append_assoc] using h1)
    refine ⟨W64_nat_inj n p.command.length (by omega) (by unfold cmdsWf at hc; omega) h2, ?_⟩
    simpa only [List.append_assoc] using h3
  ihave HL : (∃ (j : Nat) (rdc : List WCmd) (vsd : List state.Command),
      "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "Hown" ∷ rdOwn br rd (R ++ ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
        (varintEnc (W64 (n : Int)) ++ (rdc.map encCommand).flatten))) ∗
      "Hcs" ∷ cs ↦* (vsd ++ List.replicate (n - j) (zero_val state.Command)) ∗
      "#Hcl" ∷ ([∗list] k ↦ c ∈ vsd, ∃ wc, ⌜rdc[k]? = some wc⌝ ∗ cmdOk c wc) ∗
      "%Hinv" ∷ ⌜rdc.length = j ∧ vsd.length = j ∧ j ≤ n ∧ ∀ c ∈ rdc, cmdWf c⌝ : IProp GF)
    $$ [i Hown Hcs]
  · iexists 0, [], []
    simp only [List.map_nil, List.flatten_nil, List.append_nil, Nat.sub_zero, List.nil_append,
      List.length_nil]
    iframe
    isplit
    · iempintro
    ipureintro; simp
  wp_for HL
  obtain ⟨hrl, hvl, hjn, hrw⟩ := Hinv
  have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
  by_cases hlt : j < n
  · rw [decide_eq_true (show sint.Z (W64 (j : Int)) < sint.Z (W64 (n : Int)) by omega)]
    simp only [ite_true]
    wp_auto
    ihave %hcsl := ownSlice_len _ _ _ $$ Hcs
    have hcsZ : sint.Z cs.len = n := by
      have := slice_len_int _ _ hcsl; simp only [List.length_append, List.length_replicate] at this
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    rw [hjZ]
    have hlk : (vsd ++ List.replicate (n - j) (zero_val state.Command))[(j : Int).toNat]? =
        some (zero_val state.Command) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by omega), hvl, Nat.sub_self]
      rw [List.getElem?_replicate, if_pos (by omega)]
    ihave ⟨Hc, Hcback⟩ := ownSlice_elem_acc (j : Int) _ cs _ _ (by omega) hlk $$ Hcs
    -- the next command's stream fact
    ihave #Hn2 := nextIs_shift rd R ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++ (varintEnc (W64 (n : Int)) ++ (rdc.map encCommand).flatten)) Msg.body _
      encCommand cmdWf (fun m ext t hwf hp => by
        obtain ⟨p, rfl, hc, -⟩ := msg_accept m hwf
        obtain ⟨hn', hu⟩ := hafter p _ ext hc (by simpa only [List.append_assoc] using hp)
        exact cmds_next p.command rdc hc.2 hrw (by omega) t _ hu) $$ Hnext
    ihave #Hst : pkgInit_state $$ []
    · iPkgInit
    wp_apply state.Command.Unmarshal.spec_holds _ _ br rd _
      $$ [$Hst $Hpkg2 $Hown $Hn2 $Hc] as %e2 H2
    icases H2 with (⟨%he2, %wc, %hwc, Hown, %cv, Hc, #Hcok⟩ | ⟨%he2, %d2, Hown, %cv, Hc⟩)
    rotate_left
    · -- an error
      rcases e2 with ei | _
      · wp_auto
        wp_for_post
        iapply HΦ
        iright
        isplitr
        · ipureintro; simp
        iexists ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
          (varintEnc (W64 (n : Int)) ++ (rdc.map encCommand).flatten)) ++ d2
        simp only [List.append_assoc]
        iframe Hown
        iunfold ownAny
        iexists epaxos.Accept.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7])
          (leToU32 [w8', w9, w10, w11]) (leToU32 [w12, w13, w14, w15]) cs (leToU32 [w16, w17, w18, w19]) v0.Deps'
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Deps
        iframe LeaderId Replica Instance Ballot Command Seq Deps
      · exact absurd rfl he2
    subst he2
    ihave Hcs := Hcback $$ Hc
    have hset : (vsd ++ List.replicate (n - j) (zero_val state.Command)).set (j : Int).toNat cv =
        (vsd ++ [cv]) ++ List.replicate (n - (j + 1)) (zero_val state.Command) := by
      rw [Int.toNat_natCast, ← hvl, List.set_append_right _ _ (by omega), Nat.sub_self,
        show n - vsd.length = (n - (vsd.length + 1)) + 1 by omega, List.replicate_succ,
        List.set_cons_zero]
      simp
    rw [hset]
    ihave #Hcl' := cmds_snoc vsd rdc (by omega) cv wc $$ [$Hcl $Hcok]
    wp_auto
    wp_for_post
    rw [w64_succ]
    iframe
    iexists j + 1, rdc ++ [wc], vsd ++ [cv]
    simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at *
    iframe
    isplitl []
    · iexact Hcl'
    ipureintro
    refine ⟨by simp; omega, by simp; omega, by omega, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hrw c h
    · simp at h; subst h; exact hwc
  · rw [decide_eq_false (show ¬ sint.Z (W64 (j : Int)) < sint.Z (W64 (n : Int)) by omega)]
    have hjn' : n = j := by omega
    subst hjn'
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.sub_self, List.replicate_zero, List.append_nil]
    wp_auto
    ihave Hb := Hback $$ %_ %(by simp) Hbs
    ihave Harr := arrBytes_intro b_ptr (W64 20) _ (by simp; rfl) $$ Hb
    -- after the commands
    have hafter2 : ∀ (p : model.Accept) (u ext : List w8), cmdsWf p.command →
        [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
          (varintEnc (W64 (n : Int)) ++ ((rdc.map encCommand).flatten ++ u))
          <+: Msg.body (.accept p) ++ ext →
        rdc = p.command ∧ u <+: encDeps p.deps ++ ext := by
      intro p u ext hc hp
      obtain ⟨hn', hu⟩ := hafter p _ ext hc hp
      exact cmds_done p.command rdc hc.2 hrw (by omega) _ _ hu
    ihave #Hn3 := nextIs_shift rd R ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++ (varintEnc (W64 (n : Int)) ++ (rdc.map encCommand).flatten))
      Msg.body _ varintEnc (fun _ => True) (fun m ext t hwf hp => by
        obtain ⟨p, rfl, hc, hd⟩ := msg_accept m hwf
        obtain ⟨-, h2⟩ := hafter2 p t ext hc (by simpa only [List.append_assoc] using hp)
        unfold encDeps at h2
        exact varint_next p.deps.length (by unfold depsWf at hd; omega) t
          ((p.deps.map u32Le).flatten ++ ext) (by simpa only [List.append_assoc] using h2)) $$ Hnext
    simp only [List.append_assoc] at *
    wp_apply hrv br rd _ $$ [$Hpkg $Hpkg2 $Hown $Hn3] as %y %err4 H4
    icases H4 with (⟨%he4, Hown⟩ | ⟨%he4, %d4, Hown⟩)
    rotate_left
    · -- an error
      rcases err4 with ei | _
      · wp_auto
        iapply HΦ
        iright
        isplitr
        · ipureintro; simp
        iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
          (varintEnc (W64 (n : Int)) ++ ((rdc.map encCommand).flatten ++ d4))
        simp only [List.append_assoc]
        iframe Hown
        iunfold ownAny
        iexists epaxos.Accept.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7])
          (leToU32 [w8', w9, w10, w11]) (leToU32 [w12, w13, w14, w15]) cs (leToU32 [w16, w17, w18, w19]) v0.Deps'
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Deps
        iframe LeaderId Replica Instance Ballot Command Seq Deps
      · exact absurd rfl he4
    subst he4
    rw [List.append_assoc R]
    ihave ⟨Hown, Hp4⟩ := nextIs_read br rd R _ Msg.body _ $$ [$Hnext $Hown]
    imod Hp4 with %Hp4
    obtain ⟨nd, hnd, hyn⟩ : ∃ nd : Nat, nd < 2 ^ 62 ∧ y = W64 (nd : Int) := by
      obtain ⟨m, ext, hwf, hp⟩ := Hp4
      obtain ⟨p, rfl, hc, hd⟩ := msg_accept m hwf
      obtain ⟨-, h2⟩ := hafter2 p (varintEnc y) ext hc (by simpa only [List.append_assoc] using hp)
      unfold encDeps at h2
      exact ⟨_, hd, (varint_head y _ (by unfold depsWf at hd; omega) [] _
        (by simpa only [List.append_assoc, List.append_nil] using h2)).1⟩
    subst hyn
    have hndZ : sint.Z (W64 (nd : Int)) = nd := sint_Z_W64_length (by omega)
    wp_auto
    wp_apply (wp_slice_make2 (V := w32)) as %ds ⟨Hds, -⟩
    · ipureintro; omega
    (try wp_auto)
    have hsnd : sint.nat (W64 (nd : Int)) = nd := by
      show (sint.Z (W64 (nd : Int))).toNat = nd; rw [hndZ]; simp
    rw [hsnd]
    ihave HL2 : (∃ (j : Nat) (rdd : List w32) (sv : GoSlice),
        "i" ∷ i_ptr ↦ W64 (j : Int) ∗
        "Hown" ∷ rdOwn br rd (R ++ ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++ (varintEnc (W64 (n : Int)) ++
          ((rdc.map encCommand).flatten ++ (varintEnc (W64 (nd : Int)) ++ (rdd.map u32Le).flatten))))) ∗
        "Hds" ∷ ds ↦* (rdd ++ List.replicate (nd - j) (zero_val w32)) ∗
        "bs" ∷ bs_ptr ↦ sv ∗
        "Harr" ∷ arrBytes b_ptr (W64 20) ∗
        "%Hinv2" ∷ ⌜rdd.length = j ∧ j ≤ nd⌝ : IProp GF)
      $$ [i Hown Hds bs Harr]
    · iexists 0, [], _
      simp only [List.map_nil, List.flatten_nil, List.append_nil, Nat.sub_zero, List.nil_append,
        List.length_nil, List.append_assoc]
      iframe
      ipureintro; simp
    wp_for HL2
    obtain ⟨hrdl, hjd⟩ := Hinv2
    have hjZ2 : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
    by_cases hlt2 : j < nd
    · rw [decide_eq_true (show sint.Z (W64 (j : Int)) < sint.Z (W64 (nd : Int)) by omega)]
      simp only [ite_true]
      wp_auto
      ihave ⟨%L4, %hL4, Hbs, Hback2⟩ := arrBytes_slice b_ptr (W64 4) (W64 20) 4 rfl (by decide)
        (by decide) $$ Harr
      wp_apply wp_ReadAtLeast_br br rd _ _ _ (W64 4) (by rw [hL4]; exact Int.le_refl _)
        $$ [$Hpkg2 $Hown $Hbs] as %n5 %err5 ⟨%y4, %Hd5, Hbs, Hown⟩
      obtain ⟨-, hdl5, hiff5⟩ := Hd5
      rcases err5 with ei | _
      · -- an error
        wp_auto
        wp_for_post
        iapply HΦ
        iright
        isplitr
        · ipureintro; simp
        iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19] ++
          (varintEnc (W64 (n : Int)) ++ ((rdc.map encCommand).flatten ++
            (varintEnc (W64 (nd : Int)) ++ ((rdd.map u32Le).flatten ++ y4))))
        simp only [List.append_assoc]
        iframe Hown
        iunfold ownAny
        iexists epaxos.Accept.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7])
          (leToU32 [w8', w9, w10, w11]) (leToU32 [w12, w13, w14, w15]) cs (leToU32 [w16, w17, w18, w19]) ds
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe LeaderId Replica Instance Ballot Command Seq Deps
      have hy4 : y4.length = 4 := by
        have := hiff5.mp rfl
        have h4 : sint.Z (W64 4) = 4 := rfl
        omega
      obtain ⟨z0, z1, z2, z3, rfl⟩ := list4 y4 hy4
      rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
      wp_auto
      wload; wload; wload; wload
      ihave Harr := Hback2 $$ %_ %(by rfl) Hbs
      ihave %hdsl := ownSlice_len _ _ _ $$ Hds
      have hdsZ : sint.Z ds.len = nd := by
        have := slice_len_int _ _ hdsl
        simp only [List.length_append, List.length_replicate] at this
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), hjZ2,
        ← encoding.binary.leToU32_4 z0]
      wp_apply wp_store_slice_index ds (j : Int) _ (leToU32 [z0, z1, z2, z3]) $$ [Hds] as Hds
      · iframe Hds; ipureintro; simp; omega
      have hset2 : (rdd ++ List.replicate (nd - j) (zero_val w32)).set (j : Int).toNat
          (leToU32 [z0, z1, z2, z3]) = (rdd ++ [leToU32 [z0, z1, z2, z3]]) ++
            List.replicate (nd - (j + 1)) (zero_val w32) := by
        rw [Int.toNat_natCast, ← hrdl, List.set_append_right _ _ (by omega), Nat.sub_self,
          show nd - rdd.length = (nd - (rdd.length + 1)) + 1 by omega, List.replicate_succ,
          List.set_cons_zero]
        simp
      rw [hset2]
      wp_for_post
      rw [w64_succ]
      iframe
      iexists j + 1, rdd ++ [leToU32 [z0, z1, z2, z3]], _
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
        leToU32_le [z0, z1, z2, z3] rfl] at *
      iframe
      ipureintro
      refine ⟨by simp; omega, by omega⟩
    · rw [decide_eq_false (show ¬ sint.Z (W64 (j : Int)) < sint.Z (W64 (nd : Int)) by omega)]
      have hjd' : nd = j := by omega
      subst hjd'
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Nat.sub_self, List.replicate_zero, List.append_nil]
      wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists Msg.accept ⟨leToU32 [w0, w1, w2, w3], leToU32 [w4, w5, w6, w7],
        leToU32 [w8', w9, w10, w11], leToU32 [w12, w13, w14, w15], rdc, leToU32 [w16, w17, w18, w19],
        rdd⟩
      isplitr
      · ipureintro
        refine ⟨rfl, ⟨show rdc.length < 2 ^ 62 by omega, hrw⟩, show rdd.length < 2 ^ 62 by omega⟩
      isplitl [Hown]
      · simp only [Msg.body, encAccept, encCmds, encDeps, leToU32_le [w0, w1, w2, w3] rfl,
          leToU32_le [w4, w5, w6, w7] rfl, leToU32_le [w8', w9, w10, w11] rfl,
          leToU32_le [w12, w13, w14, w15] rfl, leToU32_le [w16, w17, w18, w19] rfl,
          hrl, hrdl, encLen_varint n (by omega), encLen_varint nd (by omega), List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        iexact Hown
      iunfold ownMsg, ownAccept
      iexists cs, ds
      isplitl [LeaderId Replica Instance Ballot Command Seq Deps]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe LeaderId Replica Instance Ballot Command Seq Deps
      isplitl [Hcs]
      · iunfold ownCmds
        iexists vsd
        iframe Hcs Hcl
        ipureintro; show vsd.length = rdc.length; omega
      iunfold ownDeps
      iexact Hds

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
