/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ServeShare.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A server node's share (`serverShare`), split as `serve` uses it: the configuration port's
token, the shared parts (`common`), and the master's (server node 1, node 7) or a replica
node's (server node `k + 2`, node `8 + k`) addresses and ghost tokens; the configuration ports'
protocols (server nodes' and client nodes') from `common`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem digitChar_vals : Nat.digitChar 0 = '0' ∧ Nat.digitChar 1 = '1' ∧ Nat.digitChar 2 = '2' ∧
    Nat.digitChar 3 = '3' ∧ Nat.digitChar 4 = '4' ∧ Nat.digitChar 5 = '5' ∧
    Nat.digitChar 6 = '6' ∧ Nat.digitChar 7 = '7' ∧ Nat.digitChar 8 = '8' ∧ Nat.digitChar 9 = '9' :=
  ⟨Nat.digitChar_eq_zero.2 rfl, Nat.digitChar_eq_one.2 rfl, Nat.digitChar_eq_two.2 rfl,
    Nat.digitChar_eq_three.2 rfl, Nat.digitChar_eq_four.2 rfl, Nat.digitChar_eq_five.2 rfl,
    Nat.digitChar_eq_six.2 rfl, Nat.digitChar_eq_seven.2 rfl, Nat.digitChar_eq_eight.2 rfl,
    Nat.digitChar_eq_nine.2 rfl⟩

/-- Replica node `k`'s peer and client address (server node `k + 2`, node `8 + k`), as
`register` names it. -/
theorem replicaAddrs_addrPort : ∀ k, k < 5 →
    replicaAddrs[k]? = some (sp.addrPort (nodeHost (8 + k)) (W64 (nodePort (8 + k) : Int))) := by
  intro k hk
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [replicaAddrs, sp.addrPort, nodeHost, nodePort, Nat.toDigits_eq_ite, digitChar_vals]

/-- The master's addresses (node 7). -/
theorem nodeAddrs_master : nodeAddrs.getD 7 [] = [masterAddr, atStr 7 (W64 2000)] := by
  have hc := atStr_conf 0 (by omega)
  simp only [confAddrs, List.getElem?_cons_zero, Option.some.injEq] at hc
  simp only [nodeAddrs, List.getD_cons_succ, List.getD_cons_zero, ← hc, masterAddr]

/-- Replica node `k`'s addresses (node `8 + k`), as `serve` computes them. -/
theorem nodeAddrs_replica (k : Nat) (hk : k < 5) :
    nodeAddrs.getD (8 + k) [] = [sp.addrPort (nodeHost (8 + k)) (W64 (nodePort (8 + k) : Int)),
      atStr (8 + k) (W64 1000), atStr (8 + k) (W64 2000)] := by
  have hc := atStr_conf (k + 1) (by omega)
  have hr := atStr_rpc k hk
  have hp := replicaAddrs_addrPort k hk
  rw [show 7 + (k + 1) = 8 + k from by omega] at hc
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp only [confAddrs, replicaRpcAddrs, replicaAddrs, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at hc hr hp
    simp only [nodeAddrs, List.getD_cons_succ, List.getD_cons_zero, ← hc, ← hr, ← hp]

section share
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

instance srv_rpcAddr_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr W a) := by
  unfold net.rpc.rpcAddr; infer_instance

instance srv_common_persistent (γ : SwiftNames netDistGF) : Persistent (common γ) := by
  unfold common; infer_instance

/-- Server node `i + 1`'s share (node `7 + i`), split. -/
theorem serverShare_split (γ : SwiftNames netDistGF) (i : Nat) (hi : i < 6) :
    serverShare γ i ⊢ addrTok (atStr (7 + i) (W64 2000)) ∗ common γ ∗
      (if i = 0 then iprop(True) else sp.predTok γ.sp (sp.PNode.rep (i - 1))) ∗
      ((⌜i = 0⌝ ∗ addrTok masterAddr ∗ mem.writer γ) ∨
       (⌜0 < i⌝ ∗
          addrTok (sp.addrPort (nodeHost (7 + i)) (W64 (nodePort (7 + i) : Int))) ∗
          addrTok (atStr (7 + i) (W64 1000)) ∗ sp.replicaStart γ.sp (i - 1))) := by
  unfold serverShare
  match i, hi with
  | 0, _ =>
    rw [nodeAddrs_master]
    iintro ⟨Hts, Hw, #Hc⟩
    simp only [↓reduceIte]
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨H1, Hts⟩
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨H2, -⟩
    iframe H2 Hc
    isplitl []
    · itrivial
    ileft
    iframe H1 Hw
  | k + 1, hi =>
    rw [show 7 + (k + 1) = 8 + k from by omega, nodeAddrs_replica k (by omega)]
    simp only [show k + 1 ≠ 0 from by omega, ↓reduceIte, Nat.add_sub_cancel]
    iintro ⟨Hts, ⟨Hw, Hp⟩, #Hc⟩
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨H1, Hts⟩
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨H2, Hts⟩
    icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨H3, -⟩
    iframe H3 Hc Hp
    iright
    iframe H1 H2 Hw
    ipureintro; omega

/-- A plain address's protocols, from the shared part. -/
theorem common_proto (γ : SwiftNames netDistGF) (a : GoString) (P Q : Proto netDistGF)
    (ha : a ∈ plainAddrs) (hP : protoP γ a = P) (hQ : protoQ γ a = Q) :
    common γ ⊢ addrProto a P Q := by
  subst hP hQ
  unfold common
  iintro ⟨Hps, -⟩
  iapply (BigSepL.bigSepL_mem (Φ := fun a => addrProto a (protoP γ a) (protoQ γ a))
    ha) $$ Hps

/-- The master's configuration port's protocols (server node 1, node 7). -/
theorem common_confProto_master (γ : SwiftNames netDistGF) :
    common γ ⊢ addrProto (atStr 7 (W64 2000)) (conf.dialP γ) conf.ackQ := by
  have hc := atStr_conf 0 (by omega)
  simp only [confAddrs, List.getElem?_cons_zero, Option.some.injEq] at hc
  rw [← hc]
  have h1 : protoP γ go!"10.77.0.17:9001" = conf.dialP γ := by
    unfold protoP; rw [if_pos (by decide)]
  have h2 : protoQ γ go!"10.77.0.17:9001" = conf.ackQ := by
    unfold protoQ
    rw [show clientConfAddrs.idxOf? go!"10.77.0.17:9001" = none by decide,
      show confAddrs.idxOf? go!"10.77.0.17:9001" = some 0 by decide]
  exact common_proto γ _ _ _ (by decide) h1 h2

/-- Replica node `k`'s configuration port's protocols (server node `k + 2`, node `8 + k`): its
acknowledgment says that replica node `k` registered its prediction. -/
theorem common_confProto_replica (γ : SwiftNames netDistGF) (k : Nat) (hk : k < 5) :
    common γ ⊢ addrProto (atStr (8 + k) (W64 2000)) (conf.dialP γ)
      (conf.ackQP γ (sp.PNode.rep k)) := by
  have hc := atStr_conf (k + 1) (by omega)
  rw [show 7 + (k + 1) = 8 + k from by omega] at hc
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp only [confAddrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hc
    rw [← hc]
    refine common_proto γ _ _ _ (by decide) ?_ ?_
    · unfold protoP; rw [if_pos (by decide)]
    · rfl

/-- Client node `c`'s configuration port's protocols (port 9000 of node `1 + c`): what group B's
`newClient` gives `awaitConf`. -/
theorem common_confProto_client (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    common γ ⊢ addrProto (atStr (1 + c) (W64 2000)) (conf.dialPC γ)
      (conf.ackQP γ (sp.PNode.cl c)) := by
  have ha := atStr_cconf c hc
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp only [clientConfAddrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at ha
    rw [← ha]
    refine common_proto γ _ _ _ (by decide) ?_ ?_
    · unfold protoP; rw [if_neg (by decide), if_pos (by decide)]
    · rfl

/-- The replicas' ports' protocols, from the shared part. -/
theorem common_replicaProtos (γ : SwiftNames netDistGF) :
    common γ ⊢ [∗list] a ∈ replicaAddrs,
      addrProto a (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem) := by
  unfold common
  iintro ⟨Hps, -⟩
  have hsub : plainAddrs =
      (orchAddr :: clientNodeAddrs ++ clientConfAddrs ++ confAddrs) ++ replicaAddrs := rfl
  rw [hsub]
  icases BigSepL.bigSepL_append.1 $$ Hps with ⟨-, Hps⟩
  have hP : ∀ a ∈ replicaAddrs, protoP γ a = sp.inP γ.sp γ.conf γ.mem ∧
      protoQ γ a = sp.outQ γ.sp γ.conf γ.mem := by
    have hd : ∀ a ∈ replicaAddrs, (replicaAddrs.idxOf? a).isSome ∧ a ∉ confAddrs ∧
        a ∉ clientConfAddrs ∧ clientConfAddrs.idxOf? a = none ∧ confAddrs.idxOf? a = none := by
      decide
    intro a ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd a ha
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
    unfold protoP protoQ
    rw [_root_.if_neg h2, _root_.if_neg h3, hk, h4, h5]
    exact ⟨rfl, rfl⟩
  iapply BigSepL.bigSepL_mono ?_ $$ Hps
  intro k x hx
  obtain ⟨h1, h2⟩ := hP x (List.mem_of_getElem? hx)
  rw [h1, h2]

/-- The rest of the shared part: the rpc world's services and addresses, the protocol's
invariant. -/
theorem common_rest (γ : SwiftNames netDistGF) :
    common γ ⊢ ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
      ([∗list] a ∈ rpcAddrs, net.rpc.rpcAddr (GF := netDistGF) γ.W a) ∗
      sp.inv γ.sp γ.conf γ.mem γ.lin := by
  unfold common
  iintro ⟨-, $⟩

end share

end Perennial.github_com.imdea_software.swiftpaxos
