/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeShare.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Client node `c`'s share (`clientNodeShare γ c`), split as `NewClient` uses it: the configuration
port's token and protocols (`conf.dialPC γ`, `conf.ackQP γ (cl c)`), the client's protocol share
(sequence number 0 of the id `c + 1`), the registration token, and the run's facts the node's
operations need (`nodeEnv`, less the codec's).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

/-- Client node `c`'s configuration port. -/
abbrev confAddrC (c : Nat) : GoString := clientConfAddrs.getD c go!""

theorem confAddrC_mem (c : Nat) (hc : c < 6) : confAddrC c ∈ clientConfAddrs := by
  unfold confAddrC
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [clientConfAddrs]; omega)]
  exact List.getElem_mem _

section share
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

instance rpcAddrG_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr W a) := by
  unfold net.rpc.rpcAddr; infer_instance

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

theorem protos_replica (γ : SwiftNames netDistGF) :
    ∀ a ∈ replicaAddrs, protoP γ a = sp.inP γ.sp γ.conf γ.mem ∧
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


/-- Client node `c`'s share, split. -/
theorem clientNodeShare_split (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6) :
    clientNodeShare γ c ⊢ addrTokG netDistGS (clientNodeAddrs.getD c go!"") ∗
      addrTokG netDistGS (confAddrC c) ∗
      addrProtoG netDistGS (confAddrC c) (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c)) ∗
      sp.clientSeq γ.sp (W32 (((c : Nat) + 1 : Nat) : Int)) 0 ∗ sp.predTok γ.sp (sp.PNode.cl c) ∗
      net.rpc.rpcAddr (GF := netDistGF) γ.W masterAddr ∗
      ([∗list] a ∈ replicaRpcAddrs, net.rpc.rpcAddr (GF := netDistGF) γ.W a) ∗
      ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
      ([∗list] a ∈ replicaAddrs,
        addrProtoG netDistGS a (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem)) ∗
      sp.inv γ.sp γ.conf γ.mem γ.lin := by
  unfold clientNodeShare
  iintro ⟨Hkey, Hct, Hst, Hpt, Hcom⟩
  ihave Hseq := sp.clientStart_elim (γ := γ.sp) c $$ Hst
  unfold common
  icases Hcom with ⟨#Hps, %HSS, #Hrpc, #Hinv⟩
  have hp : confAddrC c ∈ plainAddrs := by
    unfold plainAddrs; simp only [List.cons_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inl (Or.inr (confAddrC_mem c hc))))
  ihave #Hcp : addrProtoG netDistGS (confAddrC c) (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl c))
    $$ [Hps]
  · rw [← protoP_confAddrC γ c hc, ← protoQ_confAddrC γ c hc]
    iapply BigSepL.bigSepL_mem (Φ := fun a => addrProtoG netDistGS a (protoP γ a) (protoQ γ a))
      hp $$ Hps
  iframe Hkey Hct Hcp Hseq Hpt Hinv
  unfold rpcAddrs
  icases BigSepL.bigSepL_cons.1 $$ Hrpc with ⟨#Hm, #Hr⟩
  iframe Hm Hr
  isplitr
  · ipureintro; exact HSS
  have hsub : plainAddrs = (orchAddr :: clientNodeAddrs ++ clientConfAddrs ++ confAddrs) ++
      replicaAddrs := rfl
  rw [hsub]
  icases BigSepL.bigSepL_append.1 $$ Hps with ⟨-, Hps2⟩
  iapply BigSepL.bigSepL_mono ?_ $$ Hps2
  intro k x hx
  obtain ⟨h1, h2⟩ := protos_replica γ x (List.mem_of_getElem? hx)
  rw [h1, h2]

end share

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
