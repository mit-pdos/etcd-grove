/-
The logical tree as a finite tree (U8b, `notes/bbolt-proof-plan.md`): the walks of `Model/LTree`
and `Model/WOps` (`lleaves`, `ldepthsF`, `lposF`) are bounded by a fuel, which `rebalance`'s root
collapse changes the depth against. A finite tree `t : RTree` the walk from a position follows
(`ltIs L bl t`: each node's kind and entries are `L`'s at its position, its children its
entries' positions) gives the walks' values once the fuel exceeds its height (`lleaves_ltIs`,
`lposF_ltIs`, `ldepthsF_ltIs`), so that the steps of `rebalance` are tree surgeries.
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Model.RTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lt
variable [GooseExts]

/-! ## The walks follow the tree -/

mutual
theorem lleaves_ltIs (L : LTree) (bl : Loc) : ∀ (t : RTree) (n : Nat), ltIs L bl t → t.ht < n →
    lleaves L bl n t.pid = t.lvs
  | .mk p true ws cs, n + 1, h, _ => by
    simp only [ltIs] at h
    simp only [RTree.pid, lleaves, h.1, RTree.lvs]
  | .mk p false ws cs, n + 1, h, hn => by
    simp only [ltIs] at h
    simp only [RTree.pid, lleaves, h.1, RTree.lvs]
    simp only [RTree.ht] at hn
    exact lleavesL_ltIsL L bl ws cs n h.2 (by omega)
  | .mk _ _ _ _, 0, _, hn => absurd hn (Nat.not_lt_zero _)
theorem lleavesL_ltIsL (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (n : Nat),
    ltIsL L bl ws cs → RTree.htL cs ≤ n → ws.flatMap (fun w => lleaves L bl n w.pgid) = RTree.lvsL cs
  | [], [], _, _, _ => rfl
  | w :: ws, t :: ts, n, h, hn => by
    simp only [ltIsL] at h
    simp only [RTree.htL] at hn
    rw [List.flatMap_cons, RTree.lvsL, ← h.1, lleaves_ltIs L bl t n h.2.1 (by omega),
      lleavesL_ltIsL L bl ws ts n h.2.2 (by omega)]
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

mutual
theorem lposF_ltIs (L : LTree) (bl : Loc) : ∀ (t : RTree) (n : Nat), ltIs L bl t → t.ht < n →
    lposF L bl n t.pid = t.pos
  | .mk p true ws cs, n + 1, h, _ => by
    simp only [ltIs] at h
    simp only [RTree.pid, lposF, h.1, RTree.pos]
  | .mk p false ws cs, n + 1, h, hn => by
    simp only [ltIs] at h
    simp only [RTree.pid, lposF, h.1, RTree.pos]
    simp only [RTree.ht] at hn
    rw [lposFL_ltIsL L bl ws cs n h.2 (by omega)]
  | .mk _ _ _ _, 0, _, hn => absurd hn (Nat.not_lt_zero _)
theorem lposFL_ltIsL (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (n : Nat),
    ltIsL L bl ws cs → RTree.htL cs ≤ n → ws.flatMap (fun w => lposF L bl n w.pgid) = RTree.posL cs
  | [], [], _, _, _ => rfl
  | w :: ws, t :: ts, n, h, hn => by
    simp only [ltIsL] at h
    simp only [RTree.htL] at hn
    rw [List.flatMap_cons, RTree.posL, ← h.1, lposF_ltIs L bl t n h.2.1 (by omega),
      lposFL_ltIsL L bl ws ts n h.2.2 (by omega)]
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

mutual
theorem ldepthsF_ltIs (L : LTree) (bl : Loc) : ∀ (t : RTree) (n d : Nat), ltIs L bl t → t.ht < n →
    ldepthsF L bl n d t.pid = t.dps d
  | .mk p true ws cs, n + 1, d, h, _ => by
    simp only [ltIs] at h
    simp only [RTree.pid, ldepthsF, h.1, RTree.dps]
  | .mk p false ws cs, n + 1, d, h, hn => by
    simp only [ltIs] at h
    simp only [RTree.pid, ldepthsF, h.1, RTree.dps]
    simp only [RTree.ht] at hn
    exact ldepthsFL_ltIsL L bl ws cs n (d + 1) h.2 (by omega)
  | .mk _ _ _ _, 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
theorem ldepthsFL_ltIsL (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (n d : Nat),
    ltIsL L bl ws cs → RTree.htL cs ≤ n →
    ws.flatMap (fun w => ldepthsF L bl n d w.pgid) = RTree.dpsL d cs
  | [], [], _, _, _, _ => rfl
  | w :: ws, t :: ts, n, d, h, hn => by
    simp only [ltIsL] at h
    simp only [RTree.htL] at hn
    rw [List.flatMap_cons, RTree.dpsL, ← h.1, ldepthsF_ltIs L bl t n d h.2.1 (by omega),
      ldepthsFL_ltIsL L bl ws ts n d h.2.2 (by omega)]
  | [], _ :: _, _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, _, h, _ => by simp only [ltIsL] at h
end

end lt

end bbolt
end EtcdGrove
end Perennial
