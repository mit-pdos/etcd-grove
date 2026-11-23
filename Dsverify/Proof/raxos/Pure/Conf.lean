/-
The deployment's configuration, as the client node chooses it (`kit.go`'s `Conf`, `choose`,
`encode`, `decode`; interface of stage 2, `notes/stage2-plan.md`): a pure record, its validity
(exactly the configurations `decode` accepts and `choose` can pick), its five bytes on the wire.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial.raxos.pure

/-- A configuration (`kit.go`'s `Conf`): the number of replicas `n`, the server mode `se`, the
pipeline length `pipe`, the epoch size `ep` (slots) and the leader timeout `tmo` (µs). -/
structure QConf where
  n : Nat
  se : Nat
  pipe : Nat
  ep : Nat
  tmo : Nat
deriving DecidableEq, Inhabited

/-- A configuration `choose` can pick and `decode` accepts: 3 or 5 replicas, server mode 0 or 1,
a pipeline of 1 to 5 slots, epochs of 1 to 5 slots, a leader timeout of 5 to 40 ms in steps of 5. -/
def QConf.ok (c : QConf) : Prop :=
  (c.n = 3 ∨ c.n = 5) ∧ c.se ≤ 1 ∧ 1 ≤ c.pipe ∧ c.pipe ≤ 5 ∧ 1 ≤ c.ep ∧ c.ep ≤ 5 ∧
    5000 ≤ c.tmo ∧ c.tmo ≤ 40000 ∧ c.tmo % 5000 = 0

instance (c : QConf) : Decidable c.ok := by unfold QConf.ok; infer_instance

/-- `c.encode()`: five bytes, `N`, `ServerMode`, `Pipeline`, `Epoch`, `TimeoutUs / 5000`. -/
def encConf (c : QConf) : List w8 :=
  [W8 c.n, W8 c.se, W8 c.pipe, W8 c.ep, W8 (c.tmo / 5000)]

/-- A byte determines an integer in `[0, 256)` (package `pure`). -/
theorem encConf_w8_inj {a b : Int} (ha : 0 ≤ a ∧ a < 256) (hb : 0 ≤ b ∧ b < 256)
    (h : W8 a = W8 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp at this
  omega

/-- Five bytes of a valid configuration are its encoding only (`decode`'s inverse). -/
theorem encConf_inj {c1 c2 : QConf} (h1 : c1.ok) (h2 : c2.ok) (h : encConf c1 = encConf c2) :
    c1 = c2 := by
  obtain ⟨n1, s1, p1, e1, t1⟩ := c1
  obtain ⟨n2, s2, p2, e2, t2⟩ := c2
  unfold QConf.ok at h1 h2
  simp only [encConf, List.cons.injEq, and_true] at h
  obtain ⟨a, b, c, d, f⟩ := h
  simp only at h1 h2
  have a' := encConf_w8_inj (by omega) (by omega) a
  have b' := encConf_w8_inj (by omega) (by omega) b
  have c' := encConf_w8_inj (by omega) (by omega) c
  have d' := encConf_w8_inj (by omega) (by omega) d
  have f' := encConf_w8_inj (by omega) (by omega) f
  simp only [QConf.mk.injEq]
  omega

end Perennial.raxos.pure
