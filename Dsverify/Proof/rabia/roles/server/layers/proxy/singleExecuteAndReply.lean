/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/singleExecuteAndReply.lean`, run `rabia-r1wake-1`.)

`(*Proxy).singleExecuteAndReply` (stage 2): the decided object's requests `rs` (commands `bc`)
executed in order on the store (request `i` on `stateOfCmds (cmds ++ bc.take i)`), each one's
reply sent to its client if connected here (`repOk`: `rs[i]` of the object decided at slot `s`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.naiveExecuteCmd

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions]

/-- The facts the replies to the requests `rs` (commands `bc`) of object `id`, decided at slot
`s`, carry (`repOk`'s), on the store of the commands `cmds` of the slots before. -/
def replyFacts (γ : Names) (s : Nat) (id : ObjId) (rs : List ReqId) (bc : List GoString)
    (cmds : List GoString) : IProp GF :=
  iprop(fact γ.rab (.dec s) (.dval (.obj id)) ∗ fact γ.rab (.pobj id) (.reqs rs) ∗
    regFacts γ.rab rs bc ∗ prefixFacts γ.rab s cmds)

instance replyFacts_persistent (γ : Names) (s : Nat) (id : ObjId) (rs : List ReqId)
    (bc : List GoString) (cmds : List GoString) :
    Persistent (replyFacts (GF := GF) γ s id rs bc cmds) := by
  unfold replyFacts; infer_instance

theorem take_succ_getElem {α : Type} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) :
    l.take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, h]; rfl

/-- `singleExecuteAndReply`: the decided object's requests `rs` (commands `bc`), executed in
order on the store, each one's reply (`repOk`) sent to its client if connected here. -/
theorem Proxy.wp_singleExecuteAndReply
    (hCSC : ProxyTCP.ClientSendChan.spec (GF := GF))
    (γ : Names) (cf : RCfg) (k : Nat) (p t : Loc) (kv : GoMap) (m : GMap GoString GoString)
    (cmds : List GoString) (dec : Loc) (v : ConsensusObj) (o : ObjV) (s : Nat) (id : ObjId)
    (rs : List ReqId) (bc : List GoString)
    (ho : o.cliIds = rs.map (fun r => BitVec.ofNat 32 r.1) ∧
      o.cliSeqs = rs.map (fun r => BitVec.ofNat 32 r.2) ∧ o.commands = bc)
    (hrs : ∀ r ∈ rs, r.1 < nC ∧ r.2 < 2 ^ 32) (hlen : ∀ cmd ∈ bc, 1 + keyLen ≤ cmd.length) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗
      structFieldRef Proxy go!"TCP" p ↦□ t ∗ structFieldRef Proxy go!"KVStore" p ↦□ kv ∗
      structFieldRef Proxy go!"executeCmdFunc" p ↦□
        methods (go.GoType.PointerType Proxy.ty) go!"naiveExecuteCmd" #p ∗
      proxyTcpRO γ k t ∗
      structFieldRef Proxy go!"CurrDec" p ↦ dec ∗ dec ↦ v ∗ objRep v o ∗
      ownMap kv (DFrac.own 1) m ∗ ⌜StoreRel m (stateOfCmds cmds)⌝ ∗
      replyFacts γ s id rs bc cmds }}
    (App (Val (p @!! go.GoType.PointerType Proxy.ty @!! go!"singleExecuteAndReply")) (Val #()))
  {{ (m' : GMap GoString GoString), RET #();
      structFieldRef Proxy go!"CurrDec" p ↦ dec ∗ dec ↦ v ∗
      ownMap kv (DFrac.own 1) m' ∗ ⌜StoreRel m' (stateOfCmds (cmds ++ bc))⌝ }} := by
  wp_start as ⟨#Hconf, #HTCP, #HKV, #HExec, #Htcp, HCD, Hdec, #Hrep, Hm, %Hrel, #Hfacts⟩
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  obtain ⟨hids, hseqs, hcmds⟩ := ho
  unfold objRep
  icases Hrep with ⟨%hv, #Hids, #Hseqs, #Hcmds⟩
  rw [hids, hseqs, hcmds]
  ihave %hrsbc : ⌜rs.length = bc.length⌝ $$ [Hfacts]
  · unfold replyFacts; icases Hfacts with ⟨-, -, Hr, -⟩; iapply regFacts_length $$ Hr
  ihave %Hidl := ownSlice_len _ _ _ $$ Hids
  ihave %Hcml := ownSlice_len _ _ _ $$ Hcmds
  ihave %Hcmw := ownSlice_wf _ _ _ $$ Hcmds
  ihave %Hsql := ownSlice_len _ _ _ $$ Hseqs
  simp only [List.length_map] at Hidl Hsql
  wp_auto
  ihave IH : iprop(∃ (i : Nat) (cv : w32) (iv : w64) (m' : GMap GoString GoString),
      "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "cid" ∷ cid_ptr ↦ cv ∗ "idx" ∷ idx_ptr ↦ iv ∗
      "Hm" ∷ ownMap kv (DFrac.own 1) m' ∗
      "HCD" ∷ structFieldRef Proxy go!"CurrDec" p ↦ dec ∗ "Hdec" ∷ dec ↦ v ∗
      "%Hst" ∷ ⌜i ≤ rs.length ∧ StoreRel m' (stateOfCmds (cmds ++ bc.take i))⌝)
      $$ [i cid idx Hm HCD Hdec]
  · iexists 0, _, _, m
    iframe
    ipureintro; exact ⟨Nat.zero_le _, by simpa using Hrel⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hile, Hst⟩ := Hst
    irename i => Hio
    have hlenZ : sint.Z v.CliIds'.len = rs.length := by obtain ⟨h1, h2⟩ := Hidl; word
    have hiZ : sint.Z (W64 (i : Int)) = i := by obtain ⟨h1, h2⟩ := Hidl; word
    have hi : i < rs.length := by rw [hiZ, hlenZ] at Hif; omega
    obtain ⟨r, hr⟩ : ∃ r, rs[i]? = some r := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨cmd, hcmd⟩ : ∃ cmd, bc[i]? = some cmd :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hrc, hrn⟩ := hrs r (List.mem_of_getElem? hr)
    have hcl := hlen cmd (List.mem_of_getElem? hcmd)
    rw [ite_eq_left (by rw [hiZ, hlenZ]; omega)]
    wp_apply wp_load_slice_index _ _ _ _ (BitVec.ofNat 32 r.1) (by rw [hiZ]; omega) $$ [$Hids] as -
    · ipureintro; rw [hiZ]; simp [hr]
    simp only [confVal]
    wp_apply wp_slice_make2 (V := GoString) _ as %res ⟨Hres, Hrescap⟩
    · ipureintro; decide
    ihave %Hresl := ownSlice_len _ _ _ $$ Hres
    have hres1 : sint.Z res.len = 1 := by
      obtain ⟨h1, h2⟩ := Hresl; simp only [List.length_replicate] at h1
      word
    have hcmZ : sint.Z v.Commands'.len = bc.length := by obtain ⟨h1, h2⟩ := Hcml; word
    have hm1 : W64 (i : Int) * W64 1 = W64 (i : Int) := by word
    have hp1 : W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) := by word
    have hi1Z : sint.Z (W64 ((i + 1 : Nat) : Int)) = i + 1 := by obtain ⟨h1, h2⟩ := Hcml; word
    rw [hm1, hp1]
    rw [ite_eq_left (by rw [hiZ, hi1Z]; omega)]
    icases (ownSlice_slice (W64 (i : Int)) (W64 ((i + 1 : Nat) : Int)) v.Commands' _ _
      ⟨by rw [hiZ]; omega, by rw [hiZ, hi1Z]; omega, by rw [hi1Z]; omega⟩).1 $$ Hcmds
      with ⟨-, #Hsub, -⟩
    have hsubl : subslice (sint.nat (W64 (i : Int))) (sint.nat (W64 ((i + 1 : Nat) : Int))) bc =
        [cmd] := by
      have e1 : sint.nat (W64 (i : Int)) = i := by obtain ⟨h1, h2⟩ := Hcml; word
      have e2 : sint.nat (W64 ((i + 1 : Nat) : Int)) = i + 1 := by obtain ⟨h1, h2⟩ := Hcml; word
      rw [e1, e2, subslice, take_succ_getElem _ _ _ hcmd, List.drop_append_of_le_length (by simp; omega)]
      simp
    rw [hsubl]
    ihave %Hsubl := ownSlice_len _ _ _ $$ Hsub
    have hsub1 : sint.Z (slice.slice v.Commands' GoString (W64 (i : Int)) (W64 ((i + 1 : Nat) : Int))).len = 1 := by
      obtain ⟨h1, h2⟩ := Hsubl; simp only [List.length_singleton] at h1; word
    have hd1 : sint.Z (W64 ((i + 1 : Nat) : Int) - W64 (i : Int)) = 1 := by
      obtain ⟨h1, h2⟩ := Hcml; word
    wp_auto
    ihave IH2 : iprop(∃ (jj : w64) (cv : GoString) (jv : w64) (rsl : List GoString)
        (m'' : GMap GoString GoString),
        "i" ∷ i_ptr ↦ jj ∗ "cmd" ∷ cmd_ptr ↦ cv ∗ "j" ∷ j_ptr ↦ jv ∗ "Hres" ∷ res ↦* rsl ∗
        "Hm" ∷ ownMap kv (DFrac.own 1) m'' ∗
        "%Hst2" ∷ ⌜(jj = W64 0 ∧ m'' = m' ∧ rsl = [[]]) ∨
          (jj = W64 1 ∧ rsl = [(execCmd (stateOfCmds (cmds ++ bc.take i)) cmd).2] ∧
            StoreRel m'' (execCmd (stateOfCmds (cmds ++ bc.take i)) cmd).1)⌝)
        $$ [i cmd j Hres Hm]
    · iexists _, _, _, _, m'
      iframe
      ipureintro; left; exact ⟨rfl, rfl, rfl⟩
    wp_for IH2
    wp_if_destruct
    · rcases Hst2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, Hst2⟩
      · rw [ite_eq_left (by rw [hd1]; decide)]
        wp_apply wp_load_slice_index _ _ _ _ cmd (by decide) $$ [$Hsub] as -
        · ipureintro; rfl
        wp_apply Proxy.wp_naiveExecuteCmd cf p kv _ (stateOfCmds (cmds ++ bc.take i)) cmd hcl
          $$ [$Hm] as %m2 ⟨Hm, %Hm2⟩
        · iframe Hconf HKV; ipureintro; exact Hst
        rw [ite_eq_left (by rw [hres1]; decide)]
        wp_apply wp_store_slice_index $$ [$Hres] as Hres
        · ipureintro; decide
        wp_for_post
        iframe
        iexists _, _, _, _, m2
        iframe
        ipureintro; right; exact ⟨rfl, rfl, Hm2⟩
      · exfalso; revert Hif; rw [hd1]; decide
    · rcases Hst2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, Hst2⟩
      · exfalso; revert Hif; rw [hd1]; decide
      have hnext : StoreRel m'' (stateOfCmds (cmds ++ bc.take (i + 1))) := by
        rw [take_succ_getElem _ _ _ hcmd, ← List.append_assoc, stateOfCmds_snoc]; exact Hst2
      wp_apply hCSC γ k t (BitVec.ofNat 32 r.1) (by simp [nC] at hrc ⊢; omega) $$ [$Htcp] as %ch Hch
      imod ownSlice_persist _ _ _ $$ Hres with #Hres
      wp_if_destruct
      · wp_for_post
        iframe
        iexists i + 1, _, _, m''
        rw [hp1]
        iframe
        ipureintro; exact ⟨hi, hnext⟩
      · icases Hch with (%Hnil | ⟨%γch, #Hbag⟩)
        · exact absurd Hnil Hif
        have hseqZ : sint.Z v.CliSeqs'.len = rs.length := by obtain ⟨h1, h2⟩ := Hsql; word
        rw [ite_eq_left (by rw [hiZ, hseqZ]; omega)]
        wp_apply wp_load_slice_index _ _ _ _ (BitVec.ofNat 32 r.2) (by rw [hiZ]; omega) $$ [$Hseqs] as -
        · ipureintro; rw [hiZ]; simp [hr]
        have hcn : (BitVec.ofNat 32 r.1).toNat = r.1 := by simp [nC] at hrc ⊢; omega
        have hnn : (BitVec.ofNat 32 r.2).toNat = r.2 := by simp; omega
        wp_apply wp_bag_send γch ch _ (repP γ (BitVec.ofNat 32 r.1).toNat) $$ [$Hbag]
        · unfold repP
          iexists (⟨BitVec.ofNat 32 r.1, BitVec.ofNat 32 r.2, v.SvrSeq',
            [(execCmd (stateOfCmds (cmds ++ bc.take i)) cmd).snd]⟩ : CmdV)
          unfold cmdRep repOk replyFacts
          icases Hfacts with ⟨#Hd, #Hp, #Hr, #Hpf⟩
          isplitr
          · iframe Hres; ipureintro; exact ⟨rfl, rfl, rfl⟩
          iexists s, id, rs, bc, i, (execCmd (stateOfCmds (cmds ++ bc.take i)) cmd).snd, cmds, cmd
          rw [hcn]
          iframe Hd Hp Hr Hpf
          ipureintro
          refine ⟨rfl, rfl, ?_, hcmd, rfl⟩
          dsimp only; rw [hnn, hr]
        wp_for_post
        iframe
        iexists i + 1, _, _, m''
        rw [hp1]
        iframe
        ipureintro; exact ⟨hi, hnext⟩
  · obtain ⟨hile, Hst⟩ := Hst
    have hlenZ : sint.Z v.CliIds'.len = rs.length := by obtain ⟨h1, h2⟩ := Hidl; word
    have hiZ : sint.Z (W64 (i : Int)) = i := by obtain ⟨h1, h2⟩ := Hidl; word
    have hi : i = rs.length := by rw [hiZ, hlenZ] at Hif; omega
    iapply HΦ
    iframe
    ipureintro
    rw [hi, hrsbc, List.take_length] at Hst
    exact Hst

end proof
end Perennial.rabia.roles.server.layers.proxy
