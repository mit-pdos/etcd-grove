/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeShare.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).

Client node `c`'s share (`clientNodeShare γ c`), split as `newClient` uses it: the configuration
port's protocols (`conf.dialPC γ`, `conf.ackQP γ (cl c)`), the start port's (`conf.startP γ`,
`conf.ackQ`), the client's protocol share (sequence number 0 of the id `c + 1`), the registration
token, and the run's facts the node's operations need (the rpc listeners' protocols, the
services, the replicas' ports' protocols, `sp.inv`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

/-- Client node `c`'s configuration port. -/
abbrev confAddrC (c : Nat) : GoString := clientConfAddrs.getD c go!""

/-- Client node `c`'s start port. -/
abbrev startAddrC (c : Nat) : GoString := clientStartAddrs.getD c go!""

theorem confAddrC_mem (c : Nat) (hc : c < 6) : confAddrC c ∈ clientConfAddrs := by
  unfold confAddrC
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [clientConfAddrs]; omega)]
  exact List.getElem_mem _

theorem startAddrC_mem (c : Nat) (hc : c < 6) : startAddrC c ∈ clientStartAddrs := by
  unfold startAddrC
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [clientStartAddrs]; omega)]
  exact List.getElem_mem _

/-- The master's address is one the master's wildcard listener takes. -/
theorem masterAddr_lis : lisAccepts go!":7001" masterAddr := lisAcceptsB_iff.1 (by decide)

theorem masterAddr_ok : addrOk masterAddr = true := by decide

theorem replicaRpcAddrs_ok : ∀ a ∈ replicaRpcAddrs, addrOk a = true := by decide

/-- Replica node `k`'s peer address is one its wildcard listener takes. -/
theorem replicaLis_acc : ∀ (k : Nat) (a : GoString), replicaAddrs[k]? = some a →
    ∃ la, replicaLis[k]? = some la ∧ addrOk a = true ∧ lisAccepts la a := by
  intro k a h
  match k, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h =>
    simp only [replicaAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, by decide, lisAcceptsB_iff.1 (by decide)⟩
  | _ + 5, h => simp [replicaAddrs] at h

section share
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

/-- The replicas' peer addresses' protocols, from their wildcard listeners'. -/
theorem lis_replicaAddrs (P Q : Proto netDistGF) :
    (□ [∗list] la ∈ replicaLis, lisProto la P Q) ⊢ [∗list] a ∈ replicaAddrs, addrProto a P Q :=
  BigSepL.bigSepL_intro (P := iprop(□ [∗list] la ∈ replicaLis, lisProto la P Q))
    (fun k a ha => by
      obtain ⟨la, hla, hok, hacc⟩ := replicaLis_acc k a ha
      exact BI.intuitionistically_elim.trans
        ((BigSepL.bigSepL_lookup (Φ := fun _ la => lisProto la P Q) hla).trans
          (lisProto_addr la a P Q hok hacc)))

theorem protoP_confAddrC (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    protoP γ (confAddrC c) = conf.dialPC γ := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [protoP, confAddrC, clientConfAddrs, confAddrs]

theorem protoQ_confAddrC (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    protoQ γ (confAddrC c) = conf.ackQP γ (sp.PNode.cl c) := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [protoQ, confAddrC, clientConfAddrs, List.idxOf?, List.findIdx?, List.findIdx?.go]

theorem protoP_startAddrC (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    protoP γ (startAddrC c) = conf.startP γ := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [protoP, startAddrC, clientStartAddrs, clientConfAddrs, confAddrs]

theorem protoQ_startAddrC (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    protoQ γ (startAddrC c) = conf.ackQ := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [protoQ, startAddrC, clientStartAddrs, clientConfAddrs, List.idxOf?, List.findIdx?,
      List.findIdx?.go]

theorem protos_replica (γ : SwiftNames netDistGF) :
    ∀ a ∈ replicaAddrs, protoP γ a = sp.inP γ.sp γ.conf γ.mem ∧
      protoQ γ a = sp.outQ γ.sp γ.conf γ.mem := by
  have hd : ∀ a ∈ replicaAddrs, (replicaAddrs.idxOf? a).isSome ∧ a ∉ confAddrs ∧
      a ∉ clientConfAddrs ∧ a ∉ clientStartAddrs ∧ clientConfAddrs.idxOf? a = none ∧
      confAddrs.idxOf? a = none := by
    decide
  intro a ha
  obtain ⟨h1, h2, h3, h3', h4, h5⟩ := hd a ha
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
  unfold protoP protoQ
  rw [_root_.if_neg h2, _root_.if_neg h3, _root_.if_neg h3', hk, h4, _root_.if_neg h3', h5]
  exact ⟨rfl, rfl⟩

variable [RpcHttpAddr netDistGF]

/-- Client node `c`'s share, split. -/
theorem clientNodeShare_split (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    clientNodeShare γ c ⊢
      addrProto (confAddrC c) (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c)) ∗
      addrProto (startAddrC c) (conf.startP γ) conf.ackQ ∗
      sp.clientSeq γ.sp (W32 (((c : Nat) + 1 : Nat) : Int)) 0 ∗ sp.predTok γ.sp (sp.PNode.cl c) ∗
      RpcHttpAddr.rpcAddrP γ.W masterAddr (connectReq defaultRPCPath) connectAns ∗
      ([∗list] a ∈ replicaRpcAddrs,
        RpcHttpAddr.rpcAddrP γ.W a (connectReq defaultRPCPath) connectAns) ∗
      ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
      ([∗list] a ∈ replicaAddrs,
        addrProto a (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem)) ∗
      sp.inv γ.sp γ.conf γ.mem γ.lin := by
  unfold clientNodeShare
  iintro ⟨-, -, -, Hst, Hpt, Hcom⟩
  ihave Hseq := sp.clientStart_elim (γ := γ.sp) c $$ Hst
  unfold common
  icases Hcom with ⟨#Hps, #Hlis, %HSS, #Hrpc, #Hinv⟩
  have hp : confAddrC c ∈ plainAddrs := by
    have := confAddrC_mem c hc
    unfold plainAddrs; simp only [List.cons_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inl (Or.inr this)))
  have hs : startAddrC c ∈ plainAddrs := by
    have := startAddrC_mem c hc
    unfold plainAddrs; simp only [List.cons_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inr this))
  ihave #Hcp : addrProto (confAddrC c) (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c))
    $$ [Hps]
  · rw [← protoP_confAddrC γ c hc, ← protoQ_confAddrC γ c hc]
    iapply BigSepL.bigSepL_mem (Φ := fun a => addrProto a (protoP γ a) (protoQ γ a))
      hp $$ Hps
  ihave #Hsp : addrProto (startAddrC c) (conf.startP γ) conf.ackQ $$ [Hps]
  · rw [← protoP_startAddrC γ c hc, ← protoQ_startAddrC γ c hc]
    iapply BigSepL.bigSepL_mem (Φ := fun a => addrProto a (protoP γ a) (protoQ γ a))
      hs $$ Hps
  iframe Hcp Hsp Hseq Hpt Hinv
  unfold rpcLis
  icases BigSepL.bigSepL_cons.1 $$ Hrpc with ⟨#Hm, #Hr⟩
  isplitr
  · iapply RpcHttpAddr.rpcLisP_addr γ.W go!":7001" _ _ masterAddr masterAddr_ok masterAddr_lis $$ Hm
  isplitr
  · iapply BigSepL.bigSepL_mono ?_ $$ Hr
    intro k x hx
    iintro #H
    iapply RpcHttpAddr.rpcLisP_addr γ.W x _ _ x
      (replicaRpcAddrs_ok x (List.mem_of_getElem? hx))
      ((lisAccepts_addrOk (replicaRpcAddrs_ok x (List.mem_of_getElem? hx))).2 rfl) $$ H
  isplitr
  · ipureintro; exact HSS
  iapply lis_replicaAddrs $$ Hlis

end share

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
