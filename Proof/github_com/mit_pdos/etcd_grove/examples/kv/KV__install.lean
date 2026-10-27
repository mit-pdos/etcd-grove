/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__install.lean`. Lean-first (no
Rocq counterpart).

Under the lock, the maps replace `runOwn`'s, and the loop over the snapshot's table `A` answers
each of this replica's waiters it finds: an operation `o` of `A` decoding to this replica's
`(id, seq)` with a waiter at `seq` is the waiter's operation (`kv_deposited_minted`: `o` is in
`D`'s data, so deposited, `ods_deposited`, and both are minted at `(id, seq)`), and its answer
`v` is the key's value after its first occurrence in `D` (`AppliedOk`'s `AnsOk`,
`ansOk_firstOcc`), what `waitP` asks -- the same as `apply`'s answer.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decode
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem KV.install.wp_proof (wp_decode : kv.decode.spec (GF := GF) (hG := hG)) :
    KV.install.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st ap D odsD mK' mA' K' A' HvalD HAD
  wp_start as ⟨#Hrep, Hrun, HK', HA', #HD, #HodsD⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold runOwn at Hrun
  iNamed Hrun
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  try wp_auto
  -- the waiters the snapshot's operations answer
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) =>
      iprop(∃ (W' : GMap w64 Loc) (x y : GoString),
        "HmW" ∷ r.[RKV, go!"waiters"] ↦ mW ∗ "HW" ∷ mW ↦$ W' ∗
        "Hwaiters" ∷ ([∗map] s ↦ ch ∈ W', waiterOk γr id s ch) ∗
        "%HWdom" ∷ ⌜∀ s ch, W' !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
        "o" ∷ o_ptr ↦ x ∗ "v" ∷ v_ptr ↦ y ∗ "r" ∷ r_ptr ↦ r)) $$ HA'
  iintro %opk -
  isplitl [HmW HW Hwaiters o v r]
  · iexists W, _, _
    iframe
    ipureintro; exact HWdom
  isplitr
  · imodintro
    iintro %i %o %v ⟨-, %Hov⟩ HP
    iNamed HP
    try wp_auto
    wp_apply wp_string_to_bytes o as %ob ⟨Hob, -⟩
    wp_apply wp_decode ob o (DFrac.own 1) $$ [$Hob]
    iintro -
    -- what continues the loop: the waiters as they are
    ihave Hcont : iprop(∀ (Ψ : val → IProp GF) (W'' : GMap w64 Loc),
        r.[RKV, go!"waiters"] ↦ mW -∗ mW ↦$ W'' -∗ ([∗map] s ↦ ch ∈ W'', waiterOk γr id s ch) -∗
        ⌜∀ s ch, W'' !! s = some ch → uint.Z s ≤ uint.Z ns⌝ -∗ (∃ x y : GoString,
          o_ptr ↦ x ∗ v_ptr ↦ y ∗ r_ptr ↦ r) -∗
        forMapPostcondition iprop(∃ (W' : GMap w64 Loc) (x y : GoString),
          "HmW" ∷ r.[RKV, go!"waiters"] ↦ mW ∗ "HW" ∷ mW ↦$ W' ∗
          "Hwaiters" ∷ ([∗map] s ↦ ch ∈ W', waiterOk γr id s ch) ∗
          "%HWdom" ∷ ⌜∀ s ch, W' !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
          "o" ∷ o_ptr ↦ x ∗ "v" ∷ v_ptr ↦ y ∗ "r" ∷ r_ptr ↦ r)
          Ψ executeVal) $$ []
    · iintro %Ψ %W'' HmW HW Hwaiters %HWdom ⟨%x, %y, Ho, Hv, Hr⟩
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists W'', x, y
      iframe
      ipureintro; exact HWdom
    cases Hdec : decodeOp o with
    | none =>
      simp only [decodeRet, Hdec]
      try wp_auto
      iapply Hcont $$ %_ %W' HmW HW Hwaiters %HWdom [o v r]
      iexists _, _; iframe
    | some x =>
      obtain ⟨rep, sq, kd, key, val⟩ := x
      simp only [decodeRet, Hdec]
      try wp_auto
      wp_if_destruct
      · -- this replica's operation: its waiter, if any
        wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW
          W' sq (DFrac.own 1) $$ [$HW] as HW
        cases HWs : W' !! sq with
        | none =>
          simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
          try wp_auto
          iapply Hcont $$ %_ %W' HmW HW Hwaiters %HWdom [o v r]
          iexists _, _; iframe
        | some ch =>
          simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
          try wp_auto
          wp_apply wp_mapDelete mW W' sq go.uint64
            (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HW] as HW
          icases (BigSepM.bigSepM_delete (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWs).1
            $$ Hwaiters with ⟨Hw, Hwaiters⟩
          iunfold waiterOk at Hw
          icases Hw with ⟨%d0, %γh, #Hmint, #Hho, Hprod⟩
          -- `o` is in `D`'s data, so deposited; the waiter's operation is `o`: both are minted at
          -- `(id, sq)`
          have Hmem : o ∈ firstOcc odsD :=
            ((HAD.1 o).1 (by show (A' !! o).isSome = true; rw [Hov]; rfl)).1
          ihave #Hdep := ods_deposited γr.raft D odsD o ((mem_firstOcc odsD o).1 Hmem) $$ HodsD
          have Hkey : opKey o = some (rep, sq) := by simp [opKey, Hdec]
          imod kv_deposited_minted γr o d0 (rep, sq) ⊤ CoPset.subseteq_top
            (by rw [show (⊤ : CoPset) \ ↑rkvN = ⊤ \ ↑rkvN from rfl]; exact raftN_regN) Hkey
            $$ Hinv [] [] [] with %Hd0
          · rw [← Hraft]; iapply isNode_commitInv $$ HisNode
          · iexact Hdep
          · rw [Hif]; iexact Hmint
          subst Hd0
          try wp_auto
          wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr d0) iprop(True) iprop(False)
            v $$ [$Hho $Hprod]
          · isplitl
            · -- its answer: the key's value after its first occurrence in `D`
              obtain ⟨m, Hm, Hnm, Hvm⟩ := ansOk_firstOcc odsD d0 v (HAD.2 d0 v Hov)
              unfold waitP
              iexists D, odsD, m
              iframe HD HodsD
              ipureintro; exact ⟨Hm, Hnm, Hvm⟩
            · itrivial
          iintro -
          try wp_auto
          iapply Hcont $$ %_ %(GMap.delete sq W') HmW HW Hwaiters [] [o v r]
          · ipureintro
            refine fun s ch' Hs => HWdom s ch' ?_
            by_cases Hss : s = sq
            · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
            · rwa [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs
          iexists _, _; iframe
      · -- another replica's operation
        try wp_auto
        iapply Hcont $$ %_ %W' HmW HW Hwaiters %HWdom [o v r]
        iexists _, _; iframe
  iintro HP HA'
  iNamed HP
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters Hrds]
  · inext
    unfold lockInv
    iexists ns, mW, W'
    iframe
    ipureintro; exact HWdom
  try wp_auto
  iapply HΦ
  unfold runOwn
  iexists mK', K', mA', A', odsD
  iframe HmK HK' HmA HA' HD HodsD
  ipureintro; exact ⟨HvalD, HAD⟩

end proof

end kv
end EtcdGrove
end Perennial
