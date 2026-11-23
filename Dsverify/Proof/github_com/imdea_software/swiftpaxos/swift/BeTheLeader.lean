/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/BeTheLeader.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.BeTheLeader(args, reply)` (swift.go) from an rpc goroutine: if the replica executed
something (`deliveredAny.Load()`, fork change P2-A: no reader bundle of `delivered`), ask the run loop for a recovery (`recover <- BallotAt(1)`) and answer with its id;
else answer with the current leader, read under `ballotL` (R6). `NextLeader` is the leader of
`BallotAt(1)` (`-1`: no quorum file). Zero ids are sent as `-2` (gob's zero).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AnyFlag
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `r.BeTheLeader(args, reply)` (see the file header): no error, a reply `btlOk` admits. -/
abbrev swift.Replica.BeTheLeader.spec : Prop :=
  ∀ (r : Loc) (γc γm : GName) (args reply : Loc) (rv : replica.defs.BeTheLeaderReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.rcvrRes r γc γm ∗ reply ↦ rv }}
    (App (App (Val (r @!! go.GoType.PointerType swift.Replica.ty @!! go!"BeTheLeader"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface); ∃ (ld nl : w32),
      reply ↦ replica.defs.BeTheLeaderReply.mk ld nl ∗
      ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.btlOk N ld nl⌝ }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions]

/-- Go's `b % N` of a non-negative ballot is in `[0, N)`. -/
theorem swift.srem_nonneg (b : w32) (N : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hb : 0 ≤ sint.Z b) :
    0 ≤ sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ∧
      sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) < N := by
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  rw [hN', replica.quorum.leader_val b N (by omega) hb]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- The leader of ballot `-1` (`BallotAt(1)` without a quorum file): `-1`, or `0` for `N = 1`. -/
theorem swift.srem_m1 (N : Nat) (h : 1 ≤ N ∧ N ≤ 7) :
    BitVec.srem (W32 (-1)) (W32 (sint.Z (W64 (N : Int)))) = W32 (-1) ∨
      BitVec.srem (W32 (-1)) (W32 (sint.Z (W64 (N : Int)))) = W32 0 := by
  obtain ⟨h1, h2⟩ := h
  have : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `btlOk` of the answers. -/
theorem swift.btlOk_of (N : Nat) (_hN : 1 ≤ N ∧ N ≤ 7) (ld nl : w32)
    (hld : ld = W32 (-2) ∨ (1 ≤ sint.Z ld ∧ sint.Z ld < N))
    (hnl : nl = W32 (-2) ∨ nl = W32 (-1)) : sp.btlOk N ld nl := by
  unfold sp.btlOk
  refine ⟨?_, ?_⟩
  · rcases hld with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hnl with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem swift.Replica.BeTheLeader.wp_proof
    (wp_Load : sync.atomic.Bool.Load.spec (GF := netDistGF) (hG := hG))
    (wp_BallotAt : replica.QuorumSystem.BallotAt.spec)
    (wp_Leader : replica.Leader.spec) :
    swift.Replica.BeTheLeader.spec := by
  intro r γc γm args reply rv
  wp_start as ⟨#Hres, Hrep⟩
  iunfold swift.rcvrRes at Hres
  icases Hres with ⟨%rr, %N, %fr, %l, %me, %dm, %qs, %rc, %γrc, %γdl, #Hrr, #HN, #Hid, #Hcfg, %HNme,
    #Hdm, #Hcm, #Hany, #Hqs, #HisQS, #Hrc, #Hbag, #Hmu⟩
  wp_auto
  wp_apply swift.wp_anyLoad wp_Load r $$ [$Hany] as %emp -
  cases emp
  rotate_left
  · -- executed something: ask for a recovery, answer with the replica's id
    wp_auto
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_bag_send (t := go.int32) γrc rc (W32 (-1)) (swift.recoverOk r)
      $$ [$Hbag]
    · iunfold swift.recoverOk; ileft; ipureintro; rfl
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_Leader
    · ipureintro; word
    simp only
    have hm1 := swift.srem_m1 N ⟨HNme.1, HNme.2.1⟩
    have hN' : 1 ≤ N ∧ N ≤ 7 := ⟨HNme.1, HNme.2.1⟩
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inr (hm1.resolve_right Hif))
    · have hme := Hif
      have hme' : 1 ≤ sint.Z me ∧ sint.Z me < N := by
        have : sint.Z me ≠ 0 := fun h => hme (by word)
        have := HNme.2.2.1; have := HNme.2.2.2; omega
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' me _ (Or.inr hme') (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' me _ (Or.inr hme') (Or.inr (hm1.resolve_right Hif))
  · -- nothing executed: the current leader, read under `ballotL`
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold swift.ballotLInv at HR
    icases HR with ⟨%b, Hb, %Hb0⟩
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_Leader
    · ipureintro; word
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hb]
    · iunfold swift.ballotLInv
      iexists b
      iframe
      ipureintro; exact Hb0
    have hlb := swift.srem_nonneg b N ⟨HNme.1, HNme.2.1⟩ Hb0
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_Leader
    · ipureintro; word
    simp only
    have hm1 := swift.srem_m1 N ⟨HNme.1, HNme.2.1⟩
    have hN' : 1 ≤ N ∧ N ≤ 7 := ⟨HNme.1, HNme.2.1⟩
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inr (hm1.resolve_right Hif))
    · have hme := Hif
      have hme' : 1 ≤ sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ∧
          sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) < N := by
        have : sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ≠ 0 := fun h => hme (by word)
        omega
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inr hme') (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inr hme') (Or.inr (hm1.resolve_right Hif))

end proof

end Perennial.github_com.imdea_software.swiftpaxos
