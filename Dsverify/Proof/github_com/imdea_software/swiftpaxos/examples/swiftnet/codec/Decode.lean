/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Decode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's `rpcMerge_*` (storing a decoded value into the target as gob does) and `rpcDecode`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecodeAs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Own

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

theorem wp_rpcMerge_defs_RegisterArgs (p : Loc) (x0 : KitVal) (v : replica.defs.RegisterArgs)
    (x : KitVal) :
    {{ (structOwnC replica.defs.RegisterArgs.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 1⌝ ∗ ownRA v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_RegisterArgs)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.RegisterArgs.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownRA
  icases Hx with %Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  subst Hx
  unfold structOwnC
  icases Hp with ⟨%Hty, Hp⟩
  rename_i a pt
  wp_auto
  wp_join iprop(p ↦ (⟨if v.Addr' = [] then a else v.Addr', pt⟩ : replica.defs.RegisterArgs) ∗
      v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  wp_join iprop(p ↦ (⟨if v.Addr' = [] then a else v.Addr', if v.Port' = W64 0 then pt else v.Port'⟩ :
      replica.defs.RegisterArgs) ∗ v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  iapply HΦ
  simp only [KitVal.mergeC]
  iframe

theorem wp_rpcMerge_defs_GetLeaderReply (p : Loc) (x0 : KitVal) (v : replica.defs.GetLeaderReply)
    (x : KitVal) :
    {{ (structOwnC replica.defs.GetLeaderReply.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 4⌝ ∗ ownGLR v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_GetLeaderReply)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.GetLeaderReply.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownGLR
  icases Hx with %Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  subst Hx
  unfold structOwnC
  icases Hp with ⟨%Hty, Hp⟩
  rename_i i
  wp_auto
  wp_join iprop(p ↦ (⟨if v.LeaderId' = W64 0 then i else v.LeaderId'⟩ : replica.defs.GetLeaderReply) ∗
      v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  iapply HΦ
  simp only [KitVal.mergeC]
  iframe

theorem wp_rpcMerge_defs_PingArgs (p : Loc) (x0 : KitVal) (v : replica.defs.PingArgs)
    (x : KitVal) :
    {{ (structOwnC replica.defs.PingArgs.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 7⌝ ∗ ownPA v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_PingArgs)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.PingArgs.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownPA
  icases Hx with %Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  subst Hx
  unfold structOwnC
  icases Hp with ⟨%Hty, Hp⟩
  rename_i i
  wp_auto
  wp_join iprop(p ↦ (⟨if v.ActAsLeader' = W8 0 then i else v.ActAsLeader'⟩ : replica.defs.PingArgs) ∗
      v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  iapply HΦ
  simp only [KitVal.mergeC]
  iframe

theorem wp_rpcMerge_defs_BeTheLeaderReply (p : Loc) (x0 : KitVal) (v : replica.defs.BeTheLeaderReply)
    (x : KitVal) :
    {{ (structOwnC replica.defs.BeTheLeaderReply.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 10⌝ ∗ ownBTLR v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_BeTheLeaderReply)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.BeTheLeaderReply.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  unfold ownBTLR
  icases Hx with %Hx
  cases x0 <;> simp [KitVal.tag] at Ht
  subst Hx
  unfold structOwnC
  icases Hp with ⟨%Hty, Hp⟩
  rename_i l n
  wp_auto
  wp_join iprop(p ↦ (⟨if v.Leader' = W32 0 then l else v.Leader', n⟩ : replica.defs.BeTheLeaderReply) ∗
      v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  wp_join iprop(p ↦ (⟨if v.Leader' = W32 0 then l else v.Leader',
      if v.NextLeader' = W32 0 then n else v.NextLeader'⟩ : replica.defs.BeTheLeaderReply) ∗
      v_ptr ↦ v ∗ p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  iapply HΦ
  simp only [KitVal.mergeC]
  iframe

theorem wp_rpcMerge_defs_RegisterReply (p : Loc) (x0 : KitVal) (v : replica.defs.RegisterReply)
    (x : KitVal) :
    {{ (structOwnC replica.defs.RegisterReply.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 2⌝ ∗ ownRR v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_RegisterReply)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.RegisterReply.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  cases x0 <;> simp [KitVal.tag] at Ht
  cases x <;> simp only [ownRR] <;> try (iexfalso; iexact Hx)
  rename_i i ns rd il i' ns' rd' il'
  icases Hx with ⟨%Hx, Hns'⟩
  obtain ⟨h1, h2, h3⟩ := Hx
  obtain ⟨vi, vns, vrd, vil⟩ := v
  simp only at h1 h2 h3
  subst h1 h2 h3
  unfold structOwnC
  icases Hp with ⟨%Hty, %sl, Hp, Hns⟩
  ihave %Hl' := ownSlice_len _ _ _ $$ Hns'
  wp_auto
  wp_join iprop(p ↦ (⟨if vi = W64 0 then i else vi, sl, rd, il⟩ :
      replica.defs.RegisterReply) ∗ v_ptr ↦ (⟨vi, vns, vrd, vil⟩ : replica.defs.RegisterReply) ∗
      p_ptr ↦ p) with [Hp v p] as ⟨Hp, v, p⟩
  all_goals try (simp only [Hif, ↓reduceIte]; iframe)
  wp_join iprop(∃ sl2 : GoSlice, p ↦ (⟨if vi = W64 0 then i else vi, sl2, rd, il⟩ :
      replica.defs.RegisterReply) ∗ v_ptr ↦ (⟨vi, vns, vrd, vil⟩ : replica.defs.RegisterReply) ∗
      p_ptr ↦ p ∗ sl2 ↦* (if ns' = [] then ns else ns'))
    with [Hp v p Hns Hns'] as ⟨%sl2, Hp, v, p, Hsl2⟩
  · have : ns' = [] := by
      have : sint.nat vns.len = 0 := by rw [Hif]; rfl
      rw [this] at Hl'; exact List.eq_nil_of_length_eq_zero Hl'.1
    subst this
    iexists sl
    simp only [↓reduceIte]
    iframe
  · have : ¬ ns' = [] := by
      intro h; subst h; apply Hif; simp at Hl'; word
    iexists vns
    simp only [this, ↓reduceIte]
    iframe
  cases vrd <;> cases vil <;> wp_auto <;> iapply HΦ <;>
    simp only [KitVal.mergeC, Bool.or_true, Bool.or_false, show (W64 0 : w64) = 0 from rfl] <;> iframe

theorem wp_rpcMerge_defs_GetReplicaListReply (p : Loc) (x0 : KitVal)
    (v : replica.defs.GetReplicaListReply) (x : KitVal) :
    {{ (structOwnC replica.defs.GetReplicaListReply.ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = 6⌝ ∗
        ownGRLR v x : IProp GF) }}
      (App (App (Val (@! rpcMerge_defs_GetReplicaListReply)) (Val #p)) (Val #v))
    {{ RET #(); structOwnC replica.defs.GetReplicaListReply.ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  wp_start as ⟨Hp, %Ht, Hx⟩
  cases x0 <;> simp [KitVal.tag] at Ht
  cases x <;> simp only [ownGRLR] <;> try (iexfalso; iexact Hx)
  rename_i rs al rd rs' al' rd'
  icases Hx with ⟨%h3, Hrs', Hal'⟩
  obtain ⟨vrs, val, vrd⟩ := v
  simp only at h3
  subst h3
  unfold structOwnC
  icases Hp with ⟨%Hty, %s1, %s2, Hp, Hrs, Hal⟩
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hrs'
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hal'
  wp_auto
  wp_join iprop(∃ s1' : GoSlice, p ↦ (⟨s1', s2, rd⟩ : replica.defs.GetReplicaListReply) ∗
      v_ptr ↦ (⟨vrs, val, vrd⟩ : replica.defs.GetReplicaListReply) ∗
      p_ptr ↦ p ∗ s1' ↦* (if rs' = [] then rs else rs'))
    with [Hp v p Hrs Hrs'] as ⟨%s1', Hp, v, p, Hs1⟩
  · have : rs' = [] := by
      have : sint.nat vrs.len = 0 := by rw [Hif]; rfl
      rw [this] at Hl1; exact List.eq_nil_of_length_eq_zero Hl1.1
    subst this
    iexists s1
    simp only [↓reduceIte]
    iframe
  · have : ¬ rs' = [] := by
      intro h; subst h; apply Hif; simp at Hl1; word
    iexists vrs
    simp only [this, ↓reduceIte]
    iframe
  wp_join iprop(∃ s2' : GoSlice, p ↦ (⟨s1', s2', rd⟩ : replica.defs.GetReplicaListReply) ∗
      v_ptr ↦ (⟨vrs, val, vrd⟩ : replica.defs.GetReplicaListReply) ∗
      p_ptr ↦ p ∗ s2' ↦* (if al' = [] then al else al'))
    with [Hp v p Hal Hal'] as ⟨%s2', Hp, v, p, Hs2⟩
  · have : al' = [] := by
      have : sint.nat val.len = 0 := by rw [Hif]; rfl
      rw [this] at Hl2; exact List.eq_nil_of_length_eq_zero Hl2.1
    subst this
    iexists s2
    simp only [↓reduceIte]
    iframe
  · have : ¬ al' = [] := by
      intro h; subst h; apply Hif; simp at Hl2; word
    iexists val
    simp only [this, ↓reduceIte]
    iframe
  cases vrd <;> wp_auto <;> iapply HΦ <;>
    simp only [KitVal.mergeC, Bool.or_true, Bool.or_false] <;> iframe

theorem wp_rpcMerge_empty {T : Type} (fn : GoString) (c : KitVal) (ty : go.GoType) (p : Loc)
    (x0 : KitVal) (v : T) (x : KitVal)
    (hfn : ∀ Φ : val → IProp GF, ▷ Φ #() ⊢ WP (App (App (Val #(functions fn [])) (Val #p)) (Val #v)) {{ Φ }})
    (hc : ∀ y : KitVal, y.tag = c.tag → y = c) :
    {{ (structOwnC ty p (DFrac.own 1) x0 ∗ ⌜x0.tag = c.tag⌝ ∗ ownEmpty c v x : IProp GF) }}
      (App (App (Val #(functions fn [])) (Val #p)) (Val #v))
    {{ RET #(); structOwnC ty p (DFrac.own 1) (KitVal.mergeC x0 x) }} := by
  iintro %Φ ⟨Hp, %Ht, Hx⟩ HΦ
  unfold ownEmpty
  icases Hx with %Hx
  subst Hx
  have := hc x0 Ht
  subst this
  iapply hfn
  inext
  iapply HΦ
  cases x0 <;> simp [KitVal.mergeC] <;> iexact Hp

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
