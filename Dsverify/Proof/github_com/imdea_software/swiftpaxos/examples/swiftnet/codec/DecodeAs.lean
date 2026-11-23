/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecodeAs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's `rpcDecodeAs_*` (decoding a tagged value as one listed type, as gob would): the
encoding of a well-formed value of the type decodes to it; other bytes give an error or some
value of the type.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecStruct
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.RoundTrip

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section wps

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

open sp

/-- A decoding error: not a `ServerError`, with a message. -/
def decErr (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝ ∗ ∃ msg, net.rpc.errMsg err msg)

theorem wp_errors_New_decErr (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (err : GoInterface), RET #err; decErr err }} := by
  iintro %Φ - HΦ
  wp_apply errors.wp_New_errorString as %x #Hx
  iapply HΦ
  unfold decErr
  isplitr
  · ipureintro
    refine ⟨by simp [interface.mkOk], ?_⟩
    intro e he
    simp [interface.mkOk] at he
    subst he
    simp only
    with_unfolding_all exact fun h => go.GoType.noConfusion h
  iexists msg
  unfold net.rpc.errMsg
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; go_type_set
  iexact Hx

theorem wp_rpcErrDecode :
    {{ (True : IProp GF) }}
      (App (Val (@! rpcErrDecode)) (Val #()))
    {{ (err : GoInterface), RET #err; decErr err }} := by
  wp_start
  wp_auto
  wp_apply wp_errors_New_decErr as %err Herr
  iapply HΦ $$ Herr

/-- `rpcDecodeAs_T`'s postcondition: the input back, and nil with a value holding the decoded
`x` (the encoded value itself when the input encodes a well-formed value of the type, tag `t`;
`conv` maps it to what the Go value holds), or a decoding error (then the input encodes no
such value). -/
def decAsPost {G A : Type} (own : G → A → IProp GF) (t : Nat) (conv : KitVal → A)
    (data : GoSlice) (dq : DFrac) (bs : List w8) (v : G) (err : GoInterface) : IProp GF :=
  iprop(data ↦*{dq} bs ∗
    ((⌜err = interface.nil⌝ ∗ ∃ x : A, own v x ∗
        ⌜∀ y : KitVal, y.tag = t → kitWf y → bs = y.encode → x = conv y⌝) ∨
     (decErr err ∗ ⌜∀ y : KitVal, y.tag = t → kitWf y → bs ≠ y.encode⌝)))

theorem wp_rpcDecodeAs_defs_RegisterReply (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_RegisterReply)) (Val #data))
    {{ (v : replica.defs.RegisterReply) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownRR 2 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pRegisterReply 2 id rtU_registerReply bs rest H hbs
    wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 2 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerReply 0 [] false false
      isplitr
      · unfold ownRR; isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 2 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerReply 0 [] false false
      isplitr
      · unfold ownRR; isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 2 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerReply 0 [] v.Ready' false
      isplitr
      · unfold ownRR; isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 2 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerReply 0 [] false false
      isplitr
      · unfold ownRR; isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 2 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerReply 0 [] false false
      isplitr
      · unfold ownRR; isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 2 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 2 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 2 H Hne

theorem wp_rpcDecodeAs_defs_GetLeaderArgs (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_GetLeaderArgs)) (Val #data))
    {{ (v : replica.defs.GetLeaderArgs) (err : GoInterface), RET (PairV #v #err);
        decAsPost (ownEmpty .getLeaderArgs) 3 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts (pEmpty .getLeaderArgs) 3 id rtU_getLeaderArgs bs rest H hbs
    wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 3 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_CommandId $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_state_Command $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_MSync $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 3 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 3 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 3 H Hne

theorem wp_rpcDecodeAs_defs_GetLeaderReply (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_GetLeaderReply)) (Val #data))
    {{ (v : replica.defs.GetLeaderReply) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownGLR 4 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pGetLeaderReply 4 id rtU_getLeaderReply bs rest H hbs
    wp_apply wp_rpcDec_defs_GetLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 4 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderReply 0
      isplitr
      · unfold ownGLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 4 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderReply 0
      isplitr
      · unfold ownGLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 4 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderReply 0
      isplitr
      · unfold ownGLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 4 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getLeaderReply 0
      isplitr
      · unfold ownGLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 4 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 4 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 4 H Hne

theorem wp_rpcDecodeAs_defs_GetReplicaListArgs (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_GetReplicaListArgs)) (Val #data))
    {{ (v : replica.defs.GetReplicaListArgs) (err : GoInterface), RET (PairV #v #err);
        decAsPost (ownEmpty .getReplicaListArgs) 5 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts (pEmpty .getReplicaListArgs) 5 id rtU_getReplicaListArgs bs rest H hbs
    wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 5 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_CommandId $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_state_Command $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_MSync $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 5 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 5 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 5 H Hne

theorem wp_rpcDecodeAs_defs_GetReplicaListReply (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_GetReplicaListReply)) (Val #data))
    {{ (v : replica.defs.GetReplicaListReply) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownGRLR 6 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pGetReplicaListReply 6 id rtU_getReplicaListReply bs rest H hbs
    wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 6 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListReply [] [] v.Ready'
      isplitr
      · unfold ownGRLR; isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 6 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListReply [] [] false
      isplitr
      · unfold ownGRLR; isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 6 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListReply [] [] false
      isplitr
      · unfold ownGRLR; isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 6 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListReply [] [] false
      isplitr
      · unfold ownGRLR; isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 6 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .getReplicaListReply [] [] false
      isplitr
      · unfold ownGRLR; isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        iapply ownSlice_nil
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 6 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 6 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 6 H Hne

theorem wp_rpcDecodeAs_defs_PingArgs (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_PingArgs)) (Val #data))
    {{ (v : replica.defs.PingArgs) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownPA 7 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pPingArgs 7 id rtU_pingArgs bs rest H hbs
    wp_apply wp_rpcDec_defs_PingArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 7 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingArgs 0
      isplitr
      · unfold ownPA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 7 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingArgs 0
      isplitr
      · unfold ownPA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 7 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingArgs 0
      isplitr
      · unfold ownPA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 7 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingArgs 0
      isplitr
      · unfold ownPA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 7 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 7 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 7 H Hne

theorem wp_rpcDecodeAs_defs_PingReply (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_PingReply)) (Val #data))
    {{ (v : replica.defs.PingReply) (err : GoInterface), RET (PairV #v #err);
        decAsPost (ownEmpty .pingReply) 8 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts (pEmpty .pingReply) 8 id rtU_pingReply bs rest H hbs
    wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 8 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_CommandId $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_state_Command $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_MSync $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .pingReply
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 8 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 8 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 8 H Hne

theorem wp_rpcDecodeAs_defs_BeTheLeaderArgs (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_BeTheLeaderArgs)) (Val #data))
    {{ (v : replica.defs.BeTheLeaderArgs) (err : GoInterface), RET (PairV #v #err);
        decAsPost (ownEmpty .beTheLeaderArgs) 9 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts (pEmpty .beTheLeaderArgs) 9 id rtU_beTheLeaderArgs bs rest H hbs
    wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 9 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_RegisterReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_CommandId $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_state_Command $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_swift_MSync $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderArgs
      isplitr
      · unfold ownEmpty; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 9 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 9 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 9 H Hne

theorem wp_rpcDecodeAs_defs_BeTheLeaderReply (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_BeTheLeaderReply)) (Val #data))
    {{ (v : replica.defs.BeTheLeaderReply) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownBTLR 10 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pBeTheLeaderReply 10 id rtU_beTheLeaderReply bs rest H hbs
    wp_apply wp_rpcDec_defs_BeTheLeaderReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 10 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderReply 0 0
      isplitr
      · unfold ownBTLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 10 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderReply 0 0
      isplitr
      · unfold ownBTLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 10 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderReply 0 0
      isplitr
      · unfold ownBTLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 10 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .beTheLeaderReply 0 0
      isplitr
      · unfold ownBTLR; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 10 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 10 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 10 H Hne

theorem wp_rpcDecodeAs_swift_MSync (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_swift_MSync)) (Val #data))
    {{ (v : swift.MSync) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownSync 17 syncOf data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pMSync 17 syncOf rtU_msync bs rest H hbs
    wp_apply wp_rpcDec_swift_MSync $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 17 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists (⟨0, 0, none, none, none⟩ : SyncVal)
      isplitr
      · unfold ownSync; simp only [optMapOwn]; ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 17 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists (⟨0, 0, none, none, none⟩ : SyncVal)
      isplitr
      · unfold ownSync; simp only [optMapOwn]; ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 17 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists (⟨0, 0, none, none, none⟩ : SyncVal)
      isplitr
      · unfold ownSync; simp only [optMapOwn]; ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 17 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists (⟨0, 0, none, none, none⟩ : SyncVal)
      isplitr
      · unfold ownSync; simp only [optMapOwn]; ipureintro; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 17 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 17 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 17 H Hne

theorem wp_rpcDecodeAs_defs_RegisterArgs (data : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (data ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDecodeAs_defs_RegisterArgs)) (Val #data))
    {{ (v : replica.defs.RegisterArgs) (err : GoInterface), RET (PairV #v #err);
        decAsPost ownRA 1 id data dq bs v err }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hbs : bs.length < 2 ^ 64 := by have := Hlen.1; word
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %tag %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    wp_apply wp_rpcErrDecode as %err Herr
    iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
    intro y _ _ hb
    rw [pU64_encode y bs hb] at H; cases H
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_if_destruct
  · have hF := decAsFacts pRegisterArgs 1 id rtU_registerArgs bs rest H hbs
    wp_apply wp_rpcDec_defs_RegisterArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact hF.none H2
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · have hr2 : rest2 = [] := by
        have : sint.nat r2.len = 0 := by rw [Hif]; rfl
        rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
      subst hr2
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists x; iframe Hown
      ipureintro; exact hF.ok x H2
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      refine hF.part x rest2 H2 ?_
      intro h; subst h; apply Hif; simp at Hl2; word
  have Hne : ¬ tag = W64 1 := Hif
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerArgs [] 0
      isplitr
      · unfold ownRA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 1 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_GetReplicaListArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerArgs [] 0
      isplitr
      · unfold ownRA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 1 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_PingReply $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerArgs [] 0
      isplitr
      · unfold ownRA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 1 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
  wp_if_destruct
  · wp_apply wp_rpcDec_defs_BeTheLeaderArgs $$ Hr as %v %r2 %ok2 Hpost
    unfold decPost
    icases Hpost with (⟨%H2, Hr⟩ | ⟨%x, %rest2, %H2, Hown, Hrest2⟩)
    · obtain ⟨H2, rfl⟩ := H2
      wp_auto
      wp_apply wp_rpcErrDecode as %err Herr
      ihave Hb := Hback $$ Hr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
    obtain ⟨H2, rfl⟩ := H2
    icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
    ihave Hr := Hback2 $$ Hr2
    ihave Hb := Hback $$ Hr
    wp_auto
    wp_if_destruct
    · 
      iapply HΦ; unfold decAsPost; iframe Hb; ileft
      isplitr
      · ipureintro; rfl
      iexists .registerArgs [] 0
      isplitr
      · unfold ownRA; ipureintro; rfl
      ipureintro; intro y hy hwf hb; exact absurd hb (notEnc_of_tag bs rest _ 1 H (by decide) y hy hwf)
    · wp_apply wp_rpcErrDecode as %err Herr
      iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
      exact notEnc_of_tag bs rest _ 1 H (by decide)
  wp_apply wp_errors_New_decErr as %err Herr
  ihave Hb := Hback $$ Hr
  iapply HΦ; unfold decAsPost; iframe Hb; iright; iframe Herr; ipureintro
  exact notEnc_of_tag bs rest tag 1 H Hne

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
