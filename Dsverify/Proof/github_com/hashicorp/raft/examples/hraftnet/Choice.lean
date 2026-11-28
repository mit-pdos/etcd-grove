/-
The hraft kit's choice of the first configuration (notes/dsv-hraft.md, S5d; coordinator-E, #48
7233410712). The genesis of raft's protocol (`gprot.GNames.g`) is the first configuration, whose size
`n0` the orchestrator draws at run time, while the rpc world's service specs are fixed at the
deployment's start. So the start allocates one protocol per size (`gprot.alloc_names`), and the
orchestrator fixes its draw once, persistently (`chosen γc n`, a `ghost_map Nat Nat`'s element at key
`0`). A service spec the world fixes is then the wrap `svcK γc Sn`: the deposit of the spec `Sn n` of
the size `n` drawn. Whoever knows the draw (`chosen γc n`) converts between the two (`svcK_intro`,
`svcK_elim`).

Here: the choice and the wrap (`ChoiceRcv.lean`: their laws for the transport and its receiver).
-/
module

public import Net.Proof.net.rpc.Proto
public import Perennial.Ghost.GhostMap
public import Perennial.Golang.Theory

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

section choice
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- The orchestrator drew `n` as the first configuration's size (persistent; at most one `n`). -/
def chosen (γc : GName) (n : Nat) : IProp GF := ghostMapElem (K := Nat) (V := Nat) γc 0 .discard n

instance chosen_persistent (γc : GName) (n : Nat) : Persistent (chosen (GF := GF) γc n) := by
  unfold chosen; infer_instance

instance chosen_timeless (γc : GName) (n : Nat) : Timeless (chosen (GF := GF) γc n) := by
  unfold chosen; infer_instance

theorem chosen_agree (γc : GName) (n m : Nat) : chosen (GF := GF) γc n ∗ chosen γc m ⊢ ⌜n = m⌝ := by
  iintro ⟨H1, H2⟩
  unfold chosen
  iapply ghostMapElem_agree (GF := GF) (K := Nat) (V := Nat) 0 γc _ _ n m $$ H1 H2

/-- The service spec the world fixes: the deposit of `Sn n`, `n` the drawn size. -/
def svcK (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) : net.rpc.MethodSpec GF :=
  fun M bs Φ => iprop(∃ n, chosen γc n ∗ Sn n M bs Φ)

theorem svcK_intro (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) (n : Nat) (M : GoString)
    (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    chosen (GF := GF) γc n ∗ Sn n M bs Φ ⊢ svcK γc Sn M bs Φ := by
  iintro ⟨#Hc, H⟩
  unfold svcK
  iexists n
  isplitr
  · iexact Hc
  iexact H

theorem svcK_elim (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) (n : Nat) (M : GoString)
    (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    chosen (GF := GF) γc n ∗ svcK γc Sn M bs Φ ⊢ Sn n M bs Φ := by
  iintro ⟨#Hc, H⟩
  unfold svcK
  icases H with ⟨%m, #Hm, H⟩
  ihave %He := chosen_agree γc n m $$ [Hc Hm]
  · iframe Hc Hm
  subst He
  iexact H

end choice


section choiceE
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The service spec the world fixes, for callers that may not know the draw: the argument bytes
are well formed (`ok`, which the receiver checks before it knows anything else), and the deposit is
one the server, which knows the draw `n`, turns into `Sn n`'s (coordinator-E's (e1)). -/
def svcKE (γc : GName) (ok : GoString → List w8 → Prop) (Sn : Nat → net.rpc.MethodSpec GF) :
    net.rpc.MethodSpec GF :=
  fun M bs Φ => iprop(⌜ok M bs⌝ ∗ ∀ n, chosen γc n -∗ |={⊤}=> Sn n M bs Φ)

/-- Who knows the draw deposits for its spec. -/
theorem svcKE_intro (γc : GName) (ok : GoString → List w8 → Prop) (Sn : Nat → net.rpc.MethodSpec GF)
    (n : Nat) (M : GoString) (bs : List w8) (Φ : List w8 → GoString → IProp GF) (h : ok M bs) :
    chosen (GF := GF) γc n ∗ Sn n M bs Φ ⊢ svcKE γc ok Sn M bs Φ := by
  iintro ⟨#Hc, H⟩
  unfold svcKE
  isplitr; · ipureintro; exact h
  iintro %m #Hm
  ihave %He := chosen_agree γc n m $$ [Hc Hm]
  · iframe Hc Hm
  subst He
  imodintro
  iexact H

theorem svcKE_elim (γc : GName) (ok : GoString → List w8 → Prop) (Sn : Nat → net.rpc.MethodSpec GF)
    (n : Nat) (M : GoString) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    chosen (GF := GF) γc n ∗ svcKE γc ok Sn M bs Φ ⊢ |={⊤}=> Sn n M bs Φ := by
  iintro ⟨#Hc, H⟩
  unfold svcKE
  icases H with ⟨-, H⟩
  iapply H $$ Hc

end choiceE

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
