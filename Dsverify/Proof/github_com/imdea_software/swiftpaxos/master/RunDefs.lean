/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/RunDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Facts the run goroutine uses: the replicas' rpc addresses from the registrations, the decoded
`BeTheLeader` reply, `rpcAddr`'s persistence.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- Registration `i`'s rpc address: `addrList[i]:portList[i]+1000` is replica node `k`'s rpc
address. -/
theorem master.rpc_of_reg {N : Nat} {nodes addrs : List GoString} {ports : List w64} {i : Nat}
    (h : master.regOk N nodes addrs ports) (hi : i < nodes.length) :
    ∃ (k : Nat) (ip : GoString), addrs[i]? = some ip ∧ ports[i]? = some (W64 (7002 + k)) ∧
      replicaRpcAddrs[k]? =
        some (ip ++ go!":" ++ decimal (sint.Z (W64 (7002 + k) + W64 1000))) := by
  obtain ⟨h1, h2, -, h4, -, h6⟩ := h
  have hai : i < addrs.length := by omega
  have hpi : i < ports.length := by omega
  have hn : nodes[i]? = some (sp.addrPort addrs[i] ports[i]) := by
    rw [h4]; simp [List.getElem?_zipWith, List.getElem?_eq_getElem hai, List.getElem?_eq_getElem hpi]
  have hmem : sp.addrPort addrs[i] ports[i] ∈ replicaAddrs :=
    List.mem_of_mem_take (h6 _ (List.mem_of_getElem? hn))
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hk5, hip, hport⟩ := master.addrPort_replica hk
  refine ⟨k, addrs[i], List.getElem?_eq_getElem hai, by rw [List.getElem?_eq_getElem hpi, hport], ?_⟩
  rw [master.replicaRpcAddrs_eq k hk5, hip]
  simp only [Option.map_some]
  congr 1
  have : sint.Z (W64 (7002 + ↑k) + W64 1000) = ((8002 + k : Nat) : Int) := by
    have := hk5; word
  rw [this, decimal_natCast]
  simp [List.append_assoc]

theorem master.signExtend_inj {x y : w32} (h : BitVec.signExtend 64 x = BitVec.signExtend 64 y) :
    x = y := by
  ext i hi
  have := congrArg (fun z => z[i]'(by omega)) h
  simpa [BitVec.getElem_signExtend, hi] using this

/-- A decoded `BeTheLeaderReply` of the encoding of `beTheLeaderReply l n` is that value. -/
theorem master.btl_decode {l n : w32} {y : sp.KitVal}
    (h : (sp.KitVal.beTheLeaderReply l n).encode = y.encode) (ht : y.tag = 10) :
    y = sp.KitVal.beTheLeaderReply l n := by
  cases y <;> simp [sp.KitVal.tag] at ht
  rename_i l' n'
  simp only [sp.KitVal.encode, sp.KitVal.tag, sp.cI32, sp.cU64] at h
  have h1 := List.append_inj' h (by simp [u64Le_length])
  have h2 := List.append_inj' h1.2 (by simp [u64Le_length])
  rw [master.signExtend_inj (u64Le_inj h2.1), master.signExtend_inj (u64Le_inj h2.2)]

end Perennial.github_com.imdea_software.swiftpaxos
