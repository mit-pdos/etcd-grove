/-
Lean-first (no Rocq counterpart).

# lintest: the specs' vocabulary and the proof's ghost log (2026-10-14)

## The closures

- `clockSpec clockVal Eclk f`: the clock `f` (a `Clock`) is logically atomic (TaDa,
  Perennial's `<<{ … }>>` notation, `ProgramLogic/AtomicFupd.lean`) over its abstract value
  `clockVal t`, with its own invariants in `Eclk`, and monotone: a reading returns the new
  value `t'`, and `t ≤ t'` (signed: the clock is an `int64`).
- `applySpec S libState Eapp f`: the library `f` is logically atomic against porcupine's
  sequential model `S.M` over the library's abstract state `libState s`: at its linearization
  point it takes the state from `s` to `s'` with the output `o` it then returns, and
  `S.M.step s (i, o) = some s'`; it returns what porcupine's `Step` needs of the input and
  output (`S.ioOk i o`).
- `genSpec f`: the input generator returns some value (any: the result holds for whatever
  inputs it generates, e.g. at random).

All three are persistent: every client calls them concurrently.

## The ghost log

`Run`'s invariant (`linInv`, at `lintestN`) holds the library's state `libState s`, the clock's
value `clockVal t`, and the log `L` of the operations linearized so far, in their order, each
with the clock's value at its linearization point (`LinRec`, `LinTheory.lean`). Each client
`c` owns the fragment `c ↪[γ] (Lc, lr)` of a ghost map whose authority is in the invariant:
its records `Lc` (the `io` and `τ` of its linearized operations, in order) and the last value
`lr` it read from the clock. `InvOk` relates them: the log's entries of client `c` are its
records (`filt`), every `τ` and every `lr` is at most the clock's current value, `τ` is sorted
along the log, and the model runs the log to `s`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.LinTheory
public import Perennial.ProgramLogic.AtomicFupd

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

/-- The invariant's namespace. -/
abbrev lintestN : Namespace := nroot.@"lintest"

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- A monotone, logically atomic clock (see the file header). -/
def clockSpec (clockVal : w64 → IProp GF) (Eclk : CoPset) (f : GoFunc) : IProp GF :=
  iprop(<<{ ∀∀ t, clockVal t }>> (App (Val #f) (Val #())) @@ Eclk
    <<{ ∃∃ t', clockVal t' ∗ ⌜sint.Z t ≤ sint.Z t'⌝ }>> {{ RET #t'; True }})

/-- A library operation, logically atomic against the model (see the file header). -/
def applySpec (S : ModelSpec GF σ) (libState : σ → IProp GF) (Eapp : CoPset) (f : GoFunc) :
    IProp GF :=
  iprop(∀ i : GoInterface, <<{ ∀∀ s, libState s }>> (App (Val #f) (Val #i)) @@ Eapp
    <<{ ∃∃ s' o, libState s' ∗ ⌜S.M.step s (i, o) = some s'⌝ }>> {{ RET #o; S.ioOk i o }})

/-- The input generator (see the file header). -/
def genSpec (f : GoFunc) : IProp GF :=
  iprop(∀ id : w64,
    {{ True }} (App (Val #f) (Val #id)) {{ (i : GoInterface), RET #i; True }})

instance clockSpec_persistent (clockVal : w64 → IProp GF) (Eclk : CoPset) (f : GoFunc) :
    Persistent (clockSpec clockVal Eclk f) := by unfold clockSpec; infer_instance
instance applySpec_persistent (S : ModelSpec GF σ) (libState : σ → IProp GF) (Eapp : CoPset)
    (f : GoFunc) : Persistent (applySpec S libState Eapp f) := by
  unfold applySpec; infer_instance
instance genSpec_persistent (f : GoFunc) : Persistent (genSpec (GF := GF) f) := by
  unfold genSpec; infer_instance

end defs

/-! ## The ghost log -/

section ghost
variable [ext : FfiSyntax]

/-- A client's ghost value: its records (an operation's input and output, and the clock's
value at its linearization point) and the last value it read from the clock. -/
abbrev ClientV := List (OpV × w64) × w64

/-- Client `c`'s records as log entries. -/
def toRecs (c : Nat) (Lc : List (OpV × w64)) : List (LinRec OpV) :=
  clientRecs c (Lc.map fun p => (p.1, sint.Z p.2))

/-- Client `c`'s records in the ghost map (none if `c` is not there). -/
def recsOf (Ls : GMap Nat ClientV) (c : Nat) : List (OpV × w64) :=
  ((Ls.lookup c).map Prod.fst).getD []

/-- What the invariant knows of the library's state `s`, the clock's value `t`, the log `L`
and the clients' ghost values `Ls`, for `n` clients (see the file header). -/
structure InvOk {σ : Type} (M : SeqModel σ OpV) (n : Nat) (s : σ) (t : w64)
    (L : List (LinRec OpV)) (Ls : GMap Nat ClientV) : Prop where
  runs : run M M.init (L.map LinRec.io) = some s
  sorted : L.Pairwise fun a b => a.τ ≤ b.τ
  le_t : ∀ e ∈ L, e.τ ≤ sint.Z t
  lr_le : ∀ c v, Ls.lookup c = some v → sint.Z v.2 ≤ sint.Z t
  dom : ∀ c v, Ls.lookup c = some v → c < n
  filt : ∀ c, L.filter (fun e => e.c == c) = toRecs c (recsOf Ls c)

/-- Client `id`'s trace `hc` matches its records `Lc`: one operation per record, of client
`id`, with the record's input and output, called before the record's linearization point and
returned after it. -/
def ClientOk (id : w64) (hc : List Operation) (Lc : List (OpV × w64)) : Prop :=
  hc.length = Lc.length ∧ ∀ (j : Nat) (o : Operation) (p : OpV × w64),
    hc[j]? = some o → Lc[j]? = some p →
    o.ClientId' = id ∧ (o.Input', o.Output') = p.1 ∧ sint.Z o.Call' ≤ sint.Z p.2 ∧
      sint.Z p.2 ≤ sint.Z o.Return'

end ghost

section inv
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable {σ : Type}

/-- `Run`'s invariant (see the file header). -/
abbrev linInv (M : SeqModel σ OpV) (libState : σ → IProp GF) (clockVal : w64 → IProp GF)
    (n : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (s : σ) (t : w64) (L : List (LinRec OpV)) (Ls : GMap Nat ClientV),
    libState s ∗ clockVal t ∗ ghostMapAuth γ 1 Ls ∗ ⌜InvOk M n s t L Ls⌝)

/-- Client `c`'s ghost value. -/
abbrev clientTok (γ : GName) (c : Nat) (v : ClientV) : IProp GF :=
  ghostMapElem γ c (DFrac.own 1) v

end inv

end lintest
end EtcdGrove
end Perennial
