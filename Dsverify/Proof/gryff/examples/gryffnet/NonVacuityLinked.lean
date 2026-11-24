/-
**Test only** (the NON-VACUITY rule; dsv-gryff, 2026-11-24): the hypothesis-class premises of
`gryff_remote_robust.spec` (`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`) that
have an instance built **without a new axiom**, as `theorem`s (no `instance` of an `InitHyp`
anywhere):
* `lib.MathPowHyp`: the main tree's interim axiom `EtcdGrove.math.Pow.wp_proof` (an existing axiom
  of the trust base, not a new one).
* `netN.StringsIndexHyp`: Perennial's `strings.Index` (with its body since Perennial `fce59af75`)
  and `stringslite.IndexByte`'s proof, on `stringslite.Index`'s one-byte path (pin-bump-fce59af75).
(`math.rand.InitHyp` was a premise until math-rand-isinit, 2026-11-24: now discharged in the statement
by Perennial's proved `math.rand.wp_initialize'`.) The other classes have no axiom-free instance at the pin b3f2fc485 (notes/dsv-gryff.md, "Session
11"): `net.rpc.InitHyp`/`net.http.InitHyp` (their closure reaches names-only initializers),
`replica2.SortSliceHyp`, `lib.RandSeedHyp` (`sort.Slice`, `math/rand.Seed` names only), `RpcHttpHyp` (net/http's server, `rpc.HandleHTTP`: not in Net),
`RpcBootHyp` (net/rpc's and net/http's owned initializations). The ninth agent's instances of
those over local axioms are in history (a5f91c8e46). No statement or proof imports this module.
-/
module

public import Dsverify.Spec.gryff.examples.gryffnet.TopLevelRobustness
public import Proof.math.Pow
public import Net.Proof.runtime.PkgInitExt
public import Perennial.Proof.internal.stringslite.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace gryff.examples.gryffnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Perennial.gryff Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### `lib.MathPowHyp`: the main tree's `math.Pow` -/

section libs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

theorem mathPow_holds : lib.MathPowHyp GF := ⟨EtcdGrove.math.Pow.wp_proof⟩

end libs

/-! ### `netN.StringsIndexHyp`: Perennial's `strings.Index` (translated with its body since
Perennial `fce59af75`), on the one-byte path of `stringslite.Index`, which reads no package
variable (so it holds with the class's `True` precondition, without `isPkgInit`) -/

section strindex
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [_root_.Perennial.strings.Assumptions]

theorem getElem?_ne_of_lt_idxOf {c : w8} :
    ∀ (s : List w8) (j : Nat), j < s.idxOf c → s[j]? ≠ some c
  | [], j, h => by simp at h
  | a :: t, j, h => by
    rw [List.idxOf_cons] at h
    cases j with
    | zero =>
      intro he
      simp only [List.getElem?_cons_zero, Option.some_inj] at he
      subst he
      simp at h
    | succ j =>
      simp only [List.getElem?_cons_succ]
      have h' : j < t.idxOf c := by
        cases hb : (a == c) <;> simp [hb] at h
        omega
      exact getElem?_ne_of_lt_idxOf t j h'

theorem indexByte_eq_indexOfByte (s : GoString) (c : w8) :
    internal.bytealg.indexByte s c = netN.indexOfByte s c := by
  unfold netN.indexOfByte
  split
  · rename_i hm
    have hlt : s.idxOf c < s.length := List.idxOf_lt_length_iff.2 hm
    refine internal.bytealg.indexByte_eq_of s c _ ?_ ?_
    · rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
    · exact fun j hj => getElem?_ne_of_lt_idxOf s j hj
  · rename_i hm
    exact internal.bytealg.indexByte_eq_neg s c (fun j hj => hm (List.mem_of_getElem? hj))

/-- `stringslite.Index(s, string(c))`: its `n == 1` case, `IndexByte(s, c)`; no package variable is
read before it. -/
theorem wp_stringslite_Index_byte (s : GoString) (c : w8) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.internal.stringslite.Index')) (Val #s))
        (Val #([c] : GoString)))
    {{ RET #(W64 (internal.bytealg.indexByte s c)); True }} := by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hn
  wp_if_destruct
  · exfalso; simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; revert Hif; simp
  wp_if_destruct
  · try wp_auto
    wp_apply internal.stringslite.wp_IndexByte as %Hsl
    iapply HΦ
    itrivial
  · exfalso; simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; revert Hif; simp

theorem stringsIndexHyp_holds : netN.StringsIndexHyp GF := by
  constructor
  intro s c
  wp_start
  wp_auto
  wp_apply wp_stringslite_Index_byte
  rw [indexByte_eq_indexOfByte]
  iapply HΦ
  itrivial

end strindex

/-! ### At the statement's heaps -/

section statement
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
variable [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
variable [cmd.server1.Assumptions]
variable [net.FieldAssumptions] [go.BasicIntoValInj] [net.rpc.Assumptions]

/-- **The non-vacuity instances** (the NON-VACUITY rule) of the classes that have one without a new
axiom (the file header), in the statement's own form (at `remoteGF` and every machine's heap). -/
theorem nonvacuous_premises :
    (∀ G L, letI := heapAt G L; lib.MathPowHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; netN.StringsIndexHyp remoteGF) :=
  ⟨fun G L => mathPow_holds (hG := heapAt G L),
    fun G L => stringsIndexHyp_holds (hG := heapAt G L)⟩

end statement

end gryff.examples.gryffnet.instances
end Perennial
