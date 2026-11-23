/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnAddr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replicas' addresses split at `':'` (pure): `PeerAddrList[Id]` is `ip ++ ":" ++ port` for the
node's IP, so `strings.Split(a, ":")[1]` is the port and `"0.0.0.0:" + port` the wildcard
address `net.ListenWild` takes for `a`'s token.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

/-- A replica address, its node's IP before the colon, and its port after. -/
theorem addr_split (a ip : GoString) (ha : a ∈ replicaAddrs) (hip : ip ++ [W8 58] <+: a) :
    ∃ port : GoString, strings.split a [W8 58] = [ip, port] ∧ ip ++ [W8 58] ++ port = a := by
  have key : ∀ (a : GoString), a.length = 15 → (∀ i < 15, a[i]? = some (W8 58) → i = 10) →
      ip ++ [W8 58] <+: a → ip = a.take 10 := by
    intro a hl hc h
    obtain ⟨u, hu⟩ := h
    have hlen : ip.length < 15 := by
      have := congrArg List.length hu; simp at this; omega
    have h58 : a[ip.length]? = some (W8 58) := by rw [← hu]; simp
    have h10 := hc _ hlen h58
    rw [← hu, List.append_assoc, List.take_append_of_le_length (by omega), ← h10,
      List.take_length]
  simp only [replicaAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  refine ⟨a.drop 11, ?_⟩
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    (rw [key _ (by decide) (by decide) hip]; exact ⟨by simp [strings.split, strings.splitAux], by decide⟩)

end Perennial.github_com.imdea_software.swiftpaxos
