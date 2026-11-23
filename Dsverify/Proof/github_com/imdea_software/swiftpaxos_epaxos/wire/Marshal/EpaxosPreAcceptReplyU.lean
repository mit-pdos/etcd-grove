/-
`epaxos.PreAcceptReply`'s `Unmarshal` (internal to the wire package).
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

private theorem list21' {α} (d : List α) (h : d.length = 21) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20,
      d = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19, a20] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
      a19, a20, rfl⟩

theorem msg_preAcceptReply (m : Msg) (h : m.kind = some MsgKind.preAcceptReply ∧ m.wf) :
    ∃ p, m = .preAcceptReply p ∧ depsWf p.deps ∧ depsWf p.committedDeps := by
  obtain ⟨hk, hw⟩ := h
  cases m <;> simp [Msg.kind] at hk
  exact ⟨_, rfl, hw⟩

/-- After all the expected `int32`s of a slice, the stream is the rest. -/
theorem deps_done (ds rdd : List w32) (hl : rdd.length = ds.length) (t rest : List w8)
    (h : (rdd.map u32Le).flatten ++ t <+: (ds.map u32Le).flatten ++ rest) : t <+: rest := by
  obtain ⟨u, hu⟩ := h
  rw [List.append_assoc] at hu
  exact ⟨u, (flatten_map_prefix (fun _ => True) u32Le (fun a b _ _ => u32Le_prefix a b) rdd ds
    (by simp) (by simp) hl _ _ hu).2⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]
variable [EpBufioDeps GF]

set_option goose.wp.extras true

theorem epaxos.Unmarshal.spec_preAcceptReply : epaxos.Unmarshal.spec (GF := GF) MsgKind.preAcceptReply := by
  dsimp only [epaxos.Unmarshal.spec, MsgKind.ty]
  intro l br rd R
  wp_start as ⟨Hown, #Hnext, Hl⟩
  iunfold ownAny at Hl
  icases Hl with ⟨%v0, Hl⟩
  ihave ⟨Hl, %Hnn⟩ := typedPointsto_not_null_dup $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨Replica, Instance, Ballot, VBallot, Seq, Deps, CommittedDeps, Status, -⟩
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) epaxos.byteReader.ty = true := by
    go_type_set
  wp_auto
  rw [hts]
  simp only [↓reduceIte]
  wp_auto
  ihave Hb := zero_array b_ptr (W64 21) 21 rfl 21 rfl $$ b
  ihave ⟨Hbs, Hback⟩ := array_slice_acc b_ptr _ (W64 21) (W64 21) 21 rfl
    (by simp only [List.length_replicate]; rfl) (by simp) (by simp) $$ Hb
  wp_apply wp_ReadAtLeast_br br rd R _ _ (W64 21) (by simp; decide) $$ [$Hpkg2 $Hown $Hbs]
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
    iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
  have hd21 : d.length = 21 := by
    have := hiff.mp rfl
    have h21 : sint.Z (W64 21) = 21 := rfl
    simp only [List.length_take, List.length_replicate] at hdl; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, rfl⟩ :=
    list21' d hd21
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.take_replicate,
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil, Nat.min_self]
  wp_auto
  wload; wload; wload; wload; wload; wload; wload; wload; wload; wload
  wload; wload; wload; wload; wload; wload; wload; wload; wload; wload; wload
  rw [← encoding.binary.leToU32_4 w0, ← encoding.binary.leToU32_4 w4,
    ← encoding.binary.leToU32_4 w8', ← encoding.binary.leToU32_4 w12,
    ← encoding.binary.leToU32_4 w16]
  ihave Hb := Hback $$ %_ %(by simp) Hbs
  ihave Harr := arrBytes_intro b_ptr (W64 21) _ (by simp; rfl) $$ Hb
  -- the stream after the header
  have hdr : ∀ (p : model.PreAcceptReply) (t ext : List w8),
      [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ t <+: Msg.body (.preAcceptReply p) ++ ext →
      t <+: encLen p.deps.length ++ ((p.deps.map u32Le).flatten ++
        (encLen p.committedDeps.length ++ ((p.committedDeps.map u32Le).flatten ++ ext))) := by
    intro p t ext hp
    simp only [Msg.body, encPreAcceptReply, encDeps] at hp
    exact pfx_skip (P := [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20])
      (P' := u32Le p.replica ++ u32Le p.inst ++ u32Le p.ballot ++ u32Le p.vballot ++
        u32Le p.seq ++ [p.status])
      (by simp [u32Le_length])
      (by simpa only [List.append_assoc, List.cons_append, List.singleton_append] using hp)
  ihave #Hn1 := nextIs_shift rd R [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] Msg.body _ varintEnc (fun _ => True)
    (fun m ext t hwf hp => by
      obtain ⟨p, rfl, hd, -⟩ := msg_preAcceptReply m hwf
      exact varint_next _ (by unfold depsWf at hd; omega) _ _ (hdr p t ext hp)) $$ Hnext
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
      iexists epaxos.PreAcceptReply.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) (leToU32 [w8', w9, w10, w11])
          (leToU32 [w12, w13, w14, w15]) (leToU32 [w16, w17, w18, w19]) v0.Deps' v0.CommittedDeps' w20
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
    · exact absurd rfl he1
  subst he1
  rw [List.append_assoc]
  ihave ⟨Hown, Hp1⟩ := nextIs_read br rd R (_ ++ varintEnc x) Msg.body _ $$ [$Hnext $Hown]
  imod Hp1 with %Hp1
  obtain ⟨nd, hnd, hxn⟩ : ∃ nd : Nat, nd < 2 ^ 62 ∧ x = W64 (nd : Int) := by
    obtain ⟨m, ext, hwf, hp⟩ := Hp1
    obtain ⟨p, rfl, hd, -⟩ := msg_preAcceptReply m hwf
    have := hdr p (varintEnc x) ext hp
    exact ⟨_, hd, (varint_head x _ (by unfold depsWf at hd; omega) [] _ (by simpa using this)).1⟩
  subst hxn
  have hndZ : sint.Z (W64 (nd : Int)) = nd := sint_Z_W64_length (by omega)
  wp_auto
  wp_apply (wp_slice_make2 (V := w32)) as %ds ⟨Hds, -⟩
  · ipureintro; omega
  (try wp_auto)
  have hsnd : sint.nat (W64 (nd : Int)) = nd := by
    show (sint.Z (W64 (nd : Int))).toNat = nd; rw [hndZ]; simp
  rw [hsnd]
  have hafter : ∀ (p : model.PreAcceptReply) (u ext : List w8), depsWf p.deps →
      [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ u) <+: Msg.body (.preAcceptReply p) ++ ext →
      nd = p.deps.length ∧ u <+: (p.deps.map u32Le).flatten ++
        (encLen p.committedDeps.length ++ ((p.committedDeps.map u32Le).flatten ++ ext)) := by
    intro p u ext hd hp
    have h1 := hdr p _ ext hp
    obtain ⟨h2, h3⟩ := varint_head _ p.deps.length (by unfold depsWf at hd; omega) _ _
      (by simpa only [List.append_assoc] using h1)
    exact ⟨W64_nat_inj nd p.deps.length (by omega) (by unfold depsWf at hd; omega) h2, h3⟩
  -- the deps' loop (`bs = b[:4]` in its body)
  ihave HL : (∃ (j : Nat) (rdd : List w32) (sv : GoSlice),
      "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "Hown" ∷ rdOwn br rd (R ++ ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ (rdd.map u32Le).flatten))) ∗
      "Hds" ∷ ds ↦* (rdd ++ List.replicate (nd - j) (zero_val w32)) ∗
      "bs" ∷ bs_ptr ↦ sv ∗
      "Harr" ∷ arrBytes b_ptr (W64 21) ∗
      "%Hinv" ∷ ⌜rdd.length = j ∧ j ≤ nd ∧ (j = 0 → sv = slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b_ptr) (W64 21 - W64 0) (W64 21 - W64 0)) ∧
        (0 < j → sv = slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b_ptr) (W64 4 - W64 0) (W64 21 - W64 0))⌝ : IProp GF)
    $$ [i Hown Hds bs Harr]
  · iexists 0, [], _
    simp only [List.map_nil, List.flatten_nil, List.append_nil, Nat.sub_zero, List.nil_append,
      List.length_nil, List.append_assoc]
    iframe
    ipureintro; simp
  wp_for HL
  obtain ⟨hrdl, hjd, hsv0, hsv1⟩ := Hinv
  have hjZ : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
  by_cases hlt : j < nd
  · rw [decide_eq_true (show sint.Z (W64 (j : Int)) < sint.Z (W64 (nd : Int)) by omega)]
    simp only [ite_true]
    wp_auto
    ihave ⟨%L4, %hL4, Hbs, Hback2⟩ := arrBytes_slice b_ptr (W64 4) (W64 21) 4 rfl (by decide)
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
      iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ ((rdd.map u32Le).flatten ++ y4))
      simp only [List.append_assoc]
      iframe Hown
      iunfold ownAny
      iexists epaxos.PreAcceptReply.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) (leToU32 [w8', w9, w10, w11])
          (leToU32 [w12, w13, w14, w15]) (leToU32 [w16, w17, w18, w19]) ds v0.CommittedDeps' w20
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
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
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), hjZ,
      ← encoding.binary.leToU32_4 z0]
    wp_apply wp_store_slice_index ds (j : Int) _ (leToU32 [z0, z1, z2, z3]) $$ [Hds] as Hds
    · iframe Hds; ipureintro; simp; omega
    have hset : (rdd ++ List.replicate (nd - j) (zero_val w32)).set (j : Int).toNat
        (leToU32 [z0, z1, z2, z3]) = (rdd ++ [leToU32 [z0, z1, z2, z3]]) ++
          List.replicate (nd - (j + 1)) (zero_val w32) := by
      rw [Int.toNat_natCast, ← hrdl, List.set_append_right _ _ (by omega), Nat.sub_self,
        show nd - rdd.length = (nd - (rdd.length + 1)) + 1 by omega, List.replicate_succ,
        List.set_cons_zero]
      simp
    rw [hset]
    wp_for_post
    rw [w64_succ]
    iframe
    iexists j + 1, rdd ++ [leToU32 [z0, z1, z2, z3]], _
    simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
      leToU32_le [z0, z1, z2, z3] rfl] at *
    iframe
    ipureintro
    refine ⟨by simp; omega, by omega, by omega, fun _ => rfl⟩
  · rw [decide_eq_false (show ¬ sint.Z (W64 (j : Int)) < sint.Z (W64 (nd : Int)) by omega)]
    have hjd' : nd = j := by omega
    subst hjd'
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.sub_self, List.replicate_zero, List.append_nil]
    wp_auto
    -- after the deps
    have hafter2 : ∀ (p : model.PreAcceptReply) (u ext : List w8), depsWf p.deps →
        [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ ((rdd.map u32Le).flatten ++ u))
          <+: Msg.body (.preAcceptReply p) ++ ext →
        u <+: encLen p.committedDeps.length ++ ((p.committedDeps.map u32Le).flatten ++ ext) := by
      intro p u ext hd hp
      obtain ⟨hn', hu⟩ := hafter p _ ext hd hp
      exact deps_done p.deps rdd (by omega) _ _ hu
    ihave #Hn3 := nextIs_shift rd R ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ (rdd.map u32Le).flatten))
      Msg.body _ varintEnc (fun _ => True) (fun m ext t hwf hp => by
        obtain ⟨p, rfl, hd, hcd⟩ := msg_preAcceptReply m hwf
        have h2 := hafter2 p t ext hd (by simpa only [List.append_assoc] using hp)
        exact varint_next p.committedDeps.length (by unfold depsWf at hcd; omega) t
          ((p.committedDeps.map u32Le).flatten ++ ext) h2) $$ Hnext
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
        iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ ((rdd.map u32Le).flatten ++ d4))
        simp only [List.append_assoc]
        iframe Hown
        iunfold ownAny
        iexists epaxos.PreAcceptReply.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) (leToU32 [w8', w9, w10, w11])
          (leToU32 [w12, w13, w14, w15]) (leToU32 [w16, w17, w18, w19]) ds v0.CommittedDeps' w20
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iNamed CommittedDeps
        iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
      · exact absurd rfl he4
    subst he4
    rw [List.append_assoc R]
    ihave ⟨Hown, Hp4⟩ := nextIs_read br rd R _ Msg.body _ $$ [$Hnext $Hown]
    imod Hp4 with %Hp4
    obtain ⟨nc, hnc, hync⟩ : ∃ nc : Nat, nc < 2 ^ 62 ∧ y = W64 (nc : Int) := by
      obtain ⟨m, ext, hwf, hp⟩ := Hp4
      obtain ⟨p, rfl, hd, hcd⟩ := msg_preAcceptReply m hwf
      have h2 := hafter2 p (varintEnc y) ext hd (by simpa only [List.append_assoc] using hp)
      exact ⟨_, hcd, (varint_head y _ (by unfold depsWf at hcd; omega) [] _
        (by simpa only [List.append_assoc, List.append_nil] using h2)).1⟩
    subst hync
    have hncZ : sint.Z (W64 (nc : Int)) = nc := sint_Z_W64_length (by omega)
    wp_auto
    wp_apply (wp_slice_make2 (V := w32)) as %cds ⟨Hcds, -⟩
    · ipureintro; omega
    (try wp_auto)
    have hsnc : sint.nat (W64 (nc : Int)) = nc := by
      show (sint.Z (W64 (nc : Int))).toNat = nc; rw [hncZ]; simp
    rw [hsnc]
    -- `bs = b[:4]` before the second loop (the fork's fix PAR-UNM, net @6417836)
    (try wp_auto)
    ihave ⟨%L, %hL, Hbs, -⟩ := arrBytes_slice b_ptr (W64 4) (W64 21) 4 rfl (by decide)
      (by decide) $$ Harr
    ihave HL2 : (∃ (j : Nat) (rdc : List w32) (L : List w8),
        "i" ∷ i_ptr ↦ W64 (j : Int) ∗
        "Hown" ∷ rdOwn br rd (R ++ ([w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++
          ((rdd.map u32Le).flatten ++ (varintEnc (W64 (nc : Int)) ++ (rdc.map u32Le).flatten))))) ∗
        "Hcds" ∷ cds ↦* (rdc ++ List.replicate (nc - j) (zero_val w32)) ∗
        "Hbs" ∷ slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b_ptr) (W64 4 - W64 0) (W64 21 - W64 0) ↦* L ∗
        "%Hinv2" ∷ ⌜rdc.length = j ∧ j ≤ nc ∧ L.length = 4⌝ : IProp GF)
      $$ [i Hown Hcds Hbs]
    · iexists 0, [], _
      simp only [List.map_nil, List.flatten_nil, List.append_nil, Nat.sub_zero, List.nil_append,
        List.length_nil, List.append_assoc]
      iframe
      ipureintro; simp; exact hL
    wp_for HL2
    obtain ⟨hrcl, hjc, hLl⟩ := Hinv2
    have hjZ2 : sint.Z (W64 (j : Int)) = j := sint_Z_W64_length (by omega)
    by_cases hlt2 : j < nc
    · rw [decide_eq_true (show sint.Z (W64 (j : Int)) < sint.Z (W64 (nc : Int)) by omega)]
      simp only [ite_true]
      wp_auto
      wp_apply wp_ReadAtLeast_br br rd _ _ _ (W64 4) (by rw [hLl]; exact Int.le_refl _)
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
        iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8', w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20] ++ (varintEnc (W64 (nd : Int)) ++ ((rdd.map u32Le).flatten ++
          (varintEnc (W64 (nc : Int)) ++ ((rdc.map u32Le).flatten ++ y4))))
        simp only [List.append_assoc]
        iframe Hown
        iunfold ownAny
        iexists epaxos.PreAcceptReply.mk (leToU32 [w0, w1, w2, w3]) (leToU32 [w4, w5, w6, w7]) (leToU32 [w8', w9, w10, w11])
          (leToU32 [w12, w13, w14, w15]) (leToU32 [w16, w17, w18, w19]) ds cds w20
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
      have hy4 : y4.length = 4 := by
        have := hiff5.mp rfl
        have h4 : sint.Z (W64 4) = 4 := rfl
        omega
      obtain ⟨z0, z1, z2, z3, rfl⟩ := list4 y4 hy4
      rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
      wp_auto
      wload; wload; wload; wload
      ihave %hcdsl := ownSlice_len _ _ _ $$ Hcds
      have hcdsZ : sint.Z cds.len = nc := by
        have := slice_len_int _ _ hcdsl
        simp only [List.length_append, List.length_replicate] at this
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), hjZ2,
        ← encoding.binary.leToU32_4 z0]
      wp_apply wp_store_slice_index cds (j : Int) _ (leToU32 [z0, z1, z2, z3]) $$ [Hcds] as Hcds
      · iframe Hcds; ipureintro; simp; omega
      have hset2 : (rdc ++ List.replicate (nc - j) (zero_val w32)).set (j : Int).toNat
          (leToU32 [z0, z1, z2, z3]) = (rdc ++ [leToU32 [z0, z1, z2, z3]]) ++
            List.replicate (nc - (j + 1)) (zero_val w32) := by
        rw [Int.toNat_natCast, ← hrcl, List.set_append_right _ _ (by omega), Nat.sub_self,
          show nc - rdc.length = (nc - (rdc.length + 1)) + 1 by omega, List.replicate_succ,
          List.set_cons_zero]
        simp
      rw [hset2]
      wp_for_post
      rw [w64_succ]
      iframe
      iexists j + 1, rdc ++ [leToU32 [z0, z1, z2, z3]], [z0, z1, z2, z3]
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
        leToU32_le [z0, z1, z2, z3] rfl] at *
      iframe
      ipureintro
      refine ⟨by simp; omega, by omega, rfl⟩
    · rw [decide_eq_false (show ¬ sint.Z (W64 (j : Int)) < sint.Z (W64 (nc : Int)) by omega)]
      have hjc' : nc = j := by omega
      subst hjc'
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Nat.sub_self, List.replicate_zero, List.append_nil]
      wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists Msg.preAcceptReply ⟨leToU32 [w0, w1, w2, w3], leToU32 [w4, w5, w6, w7],
        leToU32 [w8', w9, w10, w11], leToU32 [w12, w13, w14, w15], leToU32 [w16, w17, w18, w19],
        rdd, rdc, w20⟩
      isplitr
      · ipureintro
        refine ⟨rfl, show rdd.length < 2 ^ 62 by omega, show rdc.length < 2 ^ 62 by omega⟩
      isplitl [Hown]
      · simp only [Msg.body, encPreAcceptReply, encDeps, leToU32_le [w0, w1, w2, w3] rfl,
          leToU32_le [w4, w5, w6, w7] rfl, leToU32_le [w8', w9, w10, w11] rfl,
          leToU32_le [w12, w13, w14, w15] rfl, leToU32_le [w16, w17, w18, w19] rfl,
          hrdl, hrcl, encLen_varint nd (by omega), encLen_varint nc (by omega),
          List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        iexact Hown
      iunfold ownMsg, ownPreAcceptReply
      iexists ds, cds
      isplitl [Replica Instance Ballot VBallot Seq Deps CommittedDeps Status]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe Replica Instance Ballot VBallot Seq Deps CommittedDeps Status
      isplitl [Hds]
      · iunfold ownDeps
        iexact Hds
      iunfold ownDeps
      iexact Hcds

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
