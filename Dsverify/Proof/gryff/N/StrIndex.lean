/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/StrIndex.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md).

**Hypothesis** `StringsIndexHyp GF`: `strings.Index(s, sep)` for a one-byte `sep` (the only use,
`waitForPeerConnections`'s `strings.Index(addr, ":")`). Perennial `7b2259a12` translates
`strings.Index` names only (`Perennial/Code/strings.toml`'s `translate` lacks it); the lab proved
`wp_Index` over its own hand translation (`Harness/Code/strings_extra`, trusted code, not allowed
here). Go's `strings.Index` has no precondition and returns the index of the first `sep` in `s`,
`-1` if there is none: the class states exactly that for one-byte separators (true of Go's
`stringslite.Index` → `IndexByteString`). A premise of `gryff_remote_robust`. Since Perennial
`fce59af75` `strings.Index` is translated with its body and proved; the class has an axiom-free
instance (`NonVacuityLinked.lean`, `stringsIndexHyp_holds`), so the premise can be discharged.
-/
module

public import Dsverify.Proof.gryff.N.ConnLaws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-- Where `strings.Index(s, string(c))` points: the first `c`'s index, `-1` if none. -/
def indexOfByte (s : GoString) (c : w8) : Int :=
  if c ∈ s then (s.idxOf c : Int) else -1

/-- See the file header. -/
class StringsIndexHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  index : ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.strings.Index')) (Val #s)) (Val #([c] : GoString)))
    {{ RET #(W64 (indexOfByte s c)); True }}

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]
variable [strA : StringsIndexHyp GF]

/-- The lab's `wp_Index`: `s = pre ++ [c] ++ post` with no `c` in `pre` gives `pre`'s length. -/
theorem wp_Index (s : GoString) (c : w8) (pre post : GoString) (hs : s = pre ++ [c] ++ post)
    (hc : c ∉ pre) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.strings.Index')) (Val #s)) (Val #([c] : GoString)))
    {{ RET #(W64 pre.length); True }} := by
  have hidx : indexOfByte s c = pre.length := by
    unfold indexOfByte
    have hm : c ∈ s := by rw [hs]; simp
    rw [if_pos hm, hs, List.append_assoc, List.idxOf_append, if_neg hc]
    simp
  have := strA.index s c
  rw [hidx] at this
  exact this

end

end Perennial.gryff.netN
