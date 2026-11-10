/- Lean-first (no Rocq counterpart).

`hashing(w)` (`examples/mvccfull/config.go`): whether a reader's pick over the read weights `w`
(`readOne`'s six reads, `pick(w, 6)`) can choose the hashes (the last): `true` iff no weight of the
first six is positive (a uniform pick) or the hashes' weight (`w[5]`, `0` past the slice's end) is
positive (`hashingM`, of the weights as integers; the weights read only). Under F1's scope premise
on the read mix (`readMixOk`, `Readers.lean`) it is `false` (`hashingM_of_readMixOk`): `Run` then
skips the corruption checker (`x.hashes()`, F2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section model

/-- **`hashing`'s result** at the weights `w` (as integers): no positive weight among the first six,
or the sixth (the hashes') positive. -/
def hashingM (w : List Int) : Bool :=
  Bool.or (!((List.range 6).any fun i => decide (0 < w.getD i 0))) (decide (0 < w.getD 5 0))

/-- **No hashes under F1's scope**: `readMixOk` makes `hashing` false. (Pure; proved.) -/
theorem hashingM_of_readMixOk {w : List Int} (h : readMixOk w) : hashingM w = false := by
  obtain ⟨h5, ⟨i, hi, hpos⟩, -⟩ := h
  have hany : (List.range 6).any (fun i => decide (0 < w.getD i 0)) = true :=
    List.any_eq_true.2 ⟨i, List.mem_range.2 hi, by simpa using hpos⟩
  unfold hashingM
  rw [hany]
  simp only [Bool.not_true, Bool.false_or, decide_eq_false_iff_not, Int.not_lt]
  exact h5

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev hashing.spec : Prop :=
  ∀ (w : GoSlice) (ws : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ w ↦*{dq} ws }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing)) (Val #w))
  {{ (b : Bool), RET #b; w ↦*{dq} ws ∗ ⌜b = hashingM (ws.map sint.Z)⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
