/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Sync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`MSync`'s decoded value as the codec's ownership states it (`structOwnC`, `mapOwnC`: model
command ids, entries by index), and its merge into a zero target (`rpcMerge_swift_MSync`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Decode

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

open sp

/-- The wire value of a decoded `MSync`'s Go contents (model command ids). -/
def kitOfSync (sv : SyncVal) : KitVal :=
  .msync ⟨sv.rep, sv.bal, sv.phases.map (·.map fun p => (goCmdIdC p.1, p.2)),
    sv.cmds.map (·.map fun p => (goCmdIdC p.1, p.2)),
    sv.deps.map (·.map fun p => (goCmdIdC p.1, p.2.map goCmdIdC))⟩

theorem goCmdIdC_cmdIdGo (x : CmdId) : goCmdIdC (cmdIdGo x) = x := rfl

theorem kitOfSync_goSync (m : SyncWire) : kitOfSync (goSync m) = .msync m := by
  obtain ⟨rep, bal, ph, cm, dp⟩ := m
  simp only [kitOfSync, goSync]
  congr 2
  · cases ph <;> simp [Function.comp_def, goCmdIdC_cmdIdGo]
  · cases cm <;> simp [Function.comp_def, goCmdIdC_cmdIdGo]
  · cases dp <;> simp [goCmdIdC_cmdIdGo, Function.comp_def]

theorem valsOwn_bigSep {G A B : Type} (own : G → A → IProp GF) (R : G → B → IProp GF)
    (f : A → B) (hR : ∀ g a, own g a ⊢ R g (f a)) (gs : List (swift.CommandId × G))
    (es : List (swift.CommandId × A)) :
    valsOwn own gs es ⊢ [∗list] i ↦ e ∈ es.map (fun p => (goCmdIdC p.1, f p.2)),
      ∃ p : swift.CommandId × G, ⌜gs[i]? = some p⌝ ∗ R p.2 e.2 := by
  induction gs generalizing es with
  | nil =>
    cases es with
    | nil => simp only [valsOwn, List.map_nil]; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
    | cons a es => simp only [valsOwn]; iintro H; iexfalso; iexact H
  | cons g gs ih =>
    cases es with
    | nil => simp only [valsOwn]; iintro H; iexfalso; iexact H
    | cons a es =>
      simp only [valsOwn, List.map_cons]
      iintro ⟨%hk, Ho, H⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Ho]
      · iexists g
        isplitr
        · ipureintro; rfl
        iapply hR $$ Ho
      simp only [List.getElem?_cons_succ]
      iapply ih $$ H

theorem optMapOwn_mapOwnC {G A B : Type} [ZeroVal G] (own : G → A → IProp GF)
    (R : G → B → IProp GF) (f : A → B) (hR : ∀ g a, own g a ⊢ R g (f a)) (mp : GoMap)
    (o : Option (List (swift.CommandId × A))) :
    optMapOwn own mp o ⊢
      mapOwnC (V := G) mp (DFrac.own 1) R (o.map (·.map (fun p => (goCmdIdC p.1, f p.2)))) := by
  cases o with
  | none => simp only [optMapOwn, Option.map_none, mapOwnC]; iintro H; iexact H
  | some es =>
    simp only [optMapOwn, Option.map_some, mapOwnC, ownMapOf, rawMap]
    iintro ⟨%gs, Hm, %Hnd, Hv⟩
    ihave %Hk := valsOwn_keys own gs es $$ Hv
    iexists _, gs
    iframe Hm
    isplitr
    · ipureintro
      refine ⟨rfl, Hnd, ?_⟩
      have := congrArg (List.map goCmdIdC) Hk
      simpa [List.map_map, Function.comp_def] using this
    iapply valsOwn_bigSep own R f hR $$ Hv

/-- A decoded `MSync` at `p` holds its wire value. -/
theorem ownSync_structOwnC (p : Loc) (v : swift.MSync) (sv : SyncVal) :
    (p ↦ v ∗ ownSync v sv : IProp GF) ⊢ structOwnC swift.MSync.ty p (DFrac.own 1) (kitOfSync sv) := by
  iintro ⟨Hp, Hown⟩
  unfold ownSync
  icases Hown with ⟨%Hrb, Hph, Hcm, Hdp⟩
  obtain ⟨vrep, vbal, vph, vcm, vdp⟩ := v
  simp only at Hrb
  obtain ⟨rfl, rfl⟩ := Hrb
  simp only [kitOfSync, structOwnC]
  isplitr
  · ipureintro; trivial
  iexists vph, vcm, vdp
  iframe Hp
  isplitl [Hph]
  · have := optMapOwn_mapOwnC (GF := GF) ownPure (fun v a => iprop(⌜v = a⌝)) id (fun g a => by
      simp only [id]; iintro H; iexact H) vph sv.phases
    simp only [id] at this
    iapply this $$ Hph
  isplitl [Hcm]
  · have := optMapOwn_mapOwnC (GF := GF) ownCmd (fun c x => cmdOwnC c (DFrac.own 1) x) id
      (fun g a => by simp only [id]; unfold ownCmd cmdOwnC; iintro H; iexact H) vcm sv.cmds
    simp only [id] at this
    iapply this $$ Hcm
  · iapply optMapOwn_mapOwnC ownSliceOf
      (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦* ids ∗ ⌜ids.map goCmdIdC = d⌝))
      (List.map goCmdIdC) (fun g a => by
        unfold ownSliceOf; iintro H; iexists a; iframe H; ipureintro; rfl) $$ Hdp

/-- The zero `MSync`. -/
def syncZero : KitVal := .msync ⟨0, 0, none, none, none⟩

theorem mergeC_syncZero (sv : SyncVal) : KitVal.mergeC syncZero (kitOfSync sv) = kitOfSync sv := by
  simp only [syncZero, kitOfSync, KitVal.mergeC, Option.or_none]
  congr 2 <;> split <;> simp_all

theorem wp_rpcMerge_swift_MSync (p : Loc) (v : swift.MSync) (sv : SyncVal) :
    {{ (structOwnC swift.MSync.ty p (DFrac.own 1) syncZero ∗ ownSync v sv : IProp GF) }}
      (App (App (Val (@! rpcMerge_swift_MSync)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC swift.MSync.ty p (DFrac.own 1) (KitVal.mergeC syncZero (kitOfSync sv)) }} := by
  wp_start as ⟨Hp, Hown⟩
  rw [mergeC_syncZero]
  ihave Hp : (p ↦ (⟨0, 0, map.nil, map.nil, map.nil⟩ : swift.MSync) : IProp GF) $$ [Hp]
  · simp only [syncZero, structOwnC, mapOwnC]
    icases Hp with ⟨-, %ph, %cm, %dp, Hp, %Hph, %Hcm, %Hdp⟩
    subst Hph Hcm Hdp
    iexact Hp
  obtain ⟨vrep, vbal, vph, vcm, vdp⟩ := v
  wp_auto
  wp_join iprop(p ↦ (⟨vrep, 0, map.nil, map.nil, map.nil⟩ : swift.MSync) ∗
      v_ptr ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (subst_vars; iframe)
  wp_join iprop(p ↦ (⟨vrep, vbal, map.nil, map.nil, map.nil⟩ : swift.MSync) ∗
      v_ptr ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (subst_vars; iframe)
  wp_join iprop(p ↦ (⟨vrep, vbal, vph, map.nil, map.nil⟩ : swift.MSync) ∗
      v_ptr ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (subst_vars; iframe)
  wp_join iprop(p ↦ (⟨vrep, vbal, vph, vcm, map.nil⟩ : swift.MSync) ∗
      v_ptr ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (subst_vars; iframe)
  wp_join iprop(p ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗
      v_ptr ↦ (⟨vrep, vbal, vph, vcm, vdp⟩ : swift.MSync) ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (subst_vars; iframe)
  iapply HΦ
  iapply ownSync_structOwnC $$ [Hp Hown]
  iframe

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
section wps2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]
open sp

/-- The Go type of the struct a value of each listed type is. -/
def tyOf : KitVal → go.GoType
  | .registerArgs .. => replica.defs.RegisterArgs.ty
  | .registerReply .. => replica.defs.RegisterReply.ty
  | .getLeaderArgs => replica.defs.GetLeaderArgs.ty
  | .getLeaderReply .. => replica.defs.GetLeaderReply.ty
  | .getReplicaListArgs => replica.defs.GetReplicaListArgs.ty
  | .getReplicaListReply .. => replica.defs.GetReplicaListReply.ty
  | .pingArgs .. => replica.defs.PingArgs.ty
  | .pingReply => replica.defs.PingReply.ty
  | .beTheLeaderArgs => replica.defs.BeTheLeaderArgs.ty
  | .beTheLeaderReply .. => replica.defs.BeTheLeaderReply.ty
  | .msync .. => swift.MSync.ty

theorem structOwnC_ty (ty : go.GoType) (p : Loc) (dq : DFrac) (x : KitVal) :
    structOwnC (GF := GF) ty p dq x ⊢ ⌜ty = tyOf x⌝ := by
  cases x <;> simp only [structOwnC, tyOf] <;> iintro ⟨%H, -⟩ <;> ipureintro <;> exact H

theorem ownRR_tag (v : replica.defs.RegisterReply) (x : KitVal) : ownRR (GF := GF) v x ⊢ ⌜x.tag = 2⌝ := by
  cases x <;> simp only [ownRR, KitVal.tag] <;> first | (iintro _; ipureintro; trivial) | (iintro H; iexfalso; iexact H)
theorem ownGRLR_tag (v : replica.defs.GetReplicaListReply) (x : KitVal) :
    ownGRLR (GF := GF) v x ⊢ ⌜x.tag = 6⌝ := by
  cases x <;> simp only [ownGRLR, KitVal.tag] <;> first | (iintro _; ipureintro; trivial) | (iintro H; iexfalso; iexact H)
theorem ownRA_tag (v : replica.defs.RegisterArgs) (x : KitVal) : ownRA (GF := GF) v x ⊢ ⌜x.tag = 1⌝ := by
  unfold ownRA; iintro %H; subst H; ipureintro; rfl
theorem ownGLR_tag (v : replica.defs.GetLeaderReply) (x : KitVal) : ownGLR (GF := GF) v x ⊢ ⌜x.tag = 4⌝ := by
  unfold ownGLR; iintro %H; subst H; ipureintro; rfl
theorem ownPA_tag (v : replica.defs.PingArgs) (x : KitVal) : ownPA (GF := GF) v x ⊢ ⌜x.tag = 7⌝ := by
  unfold ownPA; iintro %H; subst H; ipureintro; rfl
theorem ownBTLR_tag (v : replica.defs.BeTheLeaderReply) (x : KitVal) :
    ownBTLR (GF := GF) v x ⊢ ⌜x.tag = 10⌝ := by
  unfold ownBTLR; iintro %H; subst H; ipureintro; rfl
theorem ownEmpty_tag {T : Type} (c : KitVal) (v : T) (x : KitVal) :
    ownEmpty (GF := GF) c v x ⊢ ⌜x.tag = c.tag⌝ := by
  unfold ownEmpty; iintro %H; subst H; ipureintro; rfl

theorem wp_rpcMerge_defs_GetLeaderArgs (p : Loc) (x0 : KitVal) (v : replica.defs.GetLeaderArgs)
    (x : KitVal) :
    {{ (structOwnC replica.defs.GetLeaderArgs.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 3⌝ ∗
        ownEmpty .getLeaderArgs v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_GetLeaderArgs)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.GetLeaderArgs.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownEmpty; icases Hx with %Hx; subst Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  wp_auto; simp only [KitVal.mergeC]; iapply HΦ; iexact Hp
theorem wp_rpcMerge_defs_GetReplicaListArgs (p : Loc) (x0 : KitVal)
    (v : replica.defs.GetReplicaListArgs) (x : KitVal) :
    {{ (structOwnC replica.defs.GetReplicaListArgs.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 5⌝ ∗
        ownEmpty .getReplicaListArgs v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_GetReplicaListArgs)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.GetReplicaListArgs.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownEmpty; icases Hx with %Hx; subst Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  wp_auto; simp only [KitVal.mergeC]; iapply HΦ; iexact Hp
theorem wp_rpcMerge_defs_PingReply (p : Loc) (x0 : KitVal) (v : replica.defs.PingReply)
    (x : KitVal) :
    {{ (structOwnC replica.defs.PingReply.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 8⌝ ∗
        ownEmpty .pingReply v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_PingReply)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.PingReply.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownEmpty; icases Hx with %Hx; subst Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  wp_auto; simp only [KitVal.mergeC]; iapply HΦ; iexact Hp
theorem wp_rpcMerge_defs_BeTheLeaderArgs (p : Loc) (x0 : KitVal) (v : replica.defs.BeTheLeaderArgs)
    (x : KitVal) :
    {{ (structOwnC replica.defs.BeTheLeaderArgs.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 9⌝ ∗
        ownEmpty .beTheLeaderArgs v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_BeTheLeaderArgs)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.BeTheLeaderArgs.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownEmpty; icases Hx with %Hx; subst Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  wp_auto; simp only [KitVal.mergeC]; iapply HΦ; iexact Hp

/-- The decoding target the code accepts (HUB-REQUEST 2): an `MSync` target is zero. -/
def decTarget : KitVal → Prop
  | .msync m => KitVal.msync m = syncZero
  | _ => True

/-- `rpcDecode`'s postcondition: the input back, the target holding a value of its type: the
merge of the encoded value when the input encodes a well-formed value of the type, or after a
decoding error (the input then encodes no such value). -/
def decodePost (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface) (x0 : KitVal)
    (err : GoInterface) : IProp GF :=
  iprop(data ↦*{dq} bs ∗ ∃ x1 : KitVal, kitValOwnC ptr (DFrac.own 1) x1 ∗ ⌜x1.tag = x0.tag⌝ ∗
    ((⌜err = interface.nil⌝ ∗
        ⌜∀ y : KitVal, y.tag = x0.tag → kitWf y → bs = y.encode → x1 = KitVal.mergeC x0 y⌝) ∨
      (decErr err ∗ ⌜∀ y : KitVal, y.tag = x0.tag → kitWf y → bs ≠ y.encode⌝)))

theorem wp_rpcDecode (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface) (x0 : KitVal) :
    {{ (data ↦*{dq} bs ∗ kitValOwnC ptr (DFrac.own 1) x0 ∗ ⌜decTarget x0⌝ : IProp GF) }}
      (App (App (Val (@! rpcDecode)) (Val #data)) (Val #ptr))
    {{ (err : GoInterface), RET #err; decodePost data dq bs ptr x0 err }} := by
  wp_start as ⟨Hb, Hown, %Ht⟩
  unfold kitValOwnC
  icases Hown with ⟨%ty, %p, %Hptr, Hs⟩
  obtain ⟨rfl, Hnn⟩ := Hptr
  cases x0
  case registerArgs =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_RegisterArgs $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownRA_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_RegisterArgs p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case registerReply =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_RegisterReply $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownRR_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_RegisterReply p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case getLeaderArgs =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_GetLeaderArgs $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownEmpty_tag .getLeaderArgs v x $$ Hx
      wp_apply wp_rpcMerge_defs_GetLeaderArgs p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case getLeaderReply =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_GetLeaderReply $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownGLR_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_GetLeaderReply p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case getReplicaListArgs =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_GetReplicaListArgs $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownEmpty_tag .getReplicaListArgs v x $$ Hx
      wp_apply wp_rpcMerge_defs_GetReplicaListArgs p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case getReplicaListReply =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_GetReplicaListReply $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownGRLR_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_GetReplicaListReply p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case pingArgs =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_PingArgs $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownPA_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_PingArgs p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case pingReply =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_PingReply $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownEmpty_tag .pingReply v x $$ Hx
      wp_apply wp_rpcMerge_defs_PingReply p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case beTheLeaderArgs =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_BeTheLeaderArgs $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownEmpty_tag .beTheLeaderArgs v x $$ Hx
      wp_apply wp_rpcMerge_defs_BeTheLeaderArgs p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case beTheLeaderReply =>
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDecodeAs_defs_BeTheLeaderReply $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      ihave %Hxt := ownBTLR_tag v x $$ Hx
      wp_apply wp_rpcMerge_defs_BeTheLeaderReply p _ v x $$ [Hs Hx] as Hs
      · iframe; ipureintro; rfl
      iapply HΦ; unfold decodePost; iframe Hb
      iexists KitVal.mergeC _ x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; cases x <;> simp_all [KitVal.mergeC, KitVal.tag]
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb; rw [Hok y hy hwf hb]; rfl
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists _
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          iexact Hs
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1
  case msync m =>
    have hz : KitVal.msync m = syncZero := Ht
    ihave %Hty := structOwnC_ty _ p _ _ $$ Hs
    simp only [tyOf] at Hty
    subst Hty
    rw [hz]
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    ihave Hs : (p ↦ (⟨0, 0, map.nil, map.nil, map.nil⟩ : swift.MSync) : IProp GF) $$ [Hs]
    · simp only [syncZero, structOwnC, mapOwnC]
      icases Hs with ⟨-, %ph, %cm, %dp, Hs, %Hph, %Hcm, %Hdp⟩
      subst Hph Hcm Hdp
      iexact Hs
    wp_auto
    wp_func_call; wp_call
    wp_auto
    wp_apply wp_rpcDecodeAs_swift_MSync $$ Hb as %v %err Hpost
    unfold decAsPost
    icases Hpost with ⟨Hb, (⟨%Herr, %x, Hx, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
    · subst Herr
      wp_auto
      wp_apply wp_rpcMerge_swift_MSync p v x $$ [Hs Hx] as Hs
      · iframe Hx
        simp only [syncZero, structOwnC, mapOwnC]
        isplitr
        · ipureintro; trivial
        iexists map.nil, map.nil, map.nil
        iframe
        ipureintro; exact ⟨rfl, rfl, rfl⟩
      rw [mergeC_syncZero]
      iapply HΦ; unfold decodePost; iframe Hb
      iexists kitOfSync x
      isplitl [Hs]
      · unfold kitValOwnC; iexists _, p; iframe Hs; ipureintro; exact ⟨rfl, Hnn⟩
      isplitr
      · ipureintro; rfl
      ileft; isplitr
      · ipureintro; rfl
      ipureintro; intro y hy hwf hb
      rw [Hok y hy hwf hb]
      cases y <;> simp [KitVal.tag, syncZero] at hy
      rename_i m'
      simp only [syncOf, kitOfSync_goSync]
      have := mergeC_syncZero (goSync m')
      rw [kitOfSync_goSync] at this
      exact this.symm
    · unfold decErr
      icases Herr with ⟨%Hne', #Hm⟩
      rcases err with e | _
      · wp_auto
        iapply HΦ; unfold decodePost; iframe Hb
        iexists syncZero
        isplitl [Hs]
        · unfold kitValOwnC; iexists _, p
          isplitr
          · ipureintro; exact ⟨rfl, Hnn⟩
          simp only [syncZero, structOwnC, mapOwnC]
          isplitr
          · ipureintro; trivial
          iexists map.nil, map.nil, map.nil
          iframe
          ipureintro; exact ⟨rfl, rfl, rfl⟩
        isplitr
        · ipureintro; rfl
        iright; unfold decErr; iframe Hm; ipureintro; exact ⟨Hne', Hne⟩
      · exact absurd rfl Hne'.1

end wps2
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
