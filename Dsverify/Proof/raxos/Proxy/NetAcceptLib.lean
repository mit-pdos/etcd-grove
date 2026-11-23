/-
Package `proxy`: lemmas of the accept routine (`waitForConnections`): the proxy's address, the
listener's invariant, the client's handshake.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

theorem proxyAddr_eq (k : Nat) : proxyAddr k = ipOf k ++ go!":" ++ go!"7000" := by
  unfold proxyAddr ipOf
  simp only [List.append_assoc]
  rfl

theorem serverAddr_eq : go!"0.0.0.0:7000" = go!"0.0.0.0" ++ go!":" ++ go!"7000" := rfl

theorem wild_0000 : go!"0.0.0.0" ∈ wildcardHosts := by
  unfold wildcardHosts; simp

/-- The first four bytes of a stream the proxy's port's protocol allows are the client's
handshake. -/
theorem hs_of_prefix (n : Nat) (data ext rest : List w8) (h1 : data <+: ext)
    (h2 : ext <+: hs n ++ rest) (hl : data.length = 4) : data = hs n := by
  have h3 : data <+: hs n ++ rest := h1.trans h2
  have h4 : hs n <+: hs n ++ rest := List.prefix_append _ _
  rcases List.prefix_of_prefix_length_le h3 h4 (by simp [hl, hs]) with h
  exact List.IsPrefix.eq_of_length h (by simp [hl, hs])

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

instance netOwn_timeless (pr rm : Loc) : Timeless (netOwn (GF := GF) pr rm) := by
  unfold netOwn; infer_instance

instance addrTok_timeless' (a : GoString) : Timeless (addrTok (G := hG.goose_globalGS) (GF := GF) a) := by
  unfold addrTok addrTokG; infer_instance

/-- The accept routine, having listened on `a` with `a`'s token, takes the listener's state. -/
theorem net_claim (pr rm : Loc) (a : GoString) :
    ⊢ inv netN iprop(netOwn (GF := GF) pr rm ∨ addrTok a) -∗ addrTok a ={⊤}=∗ netOwn pr rm := by
  iintro #Hi Htok
  iinv Hi with (>Hown | >Htok') Hclose
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro; iexact Hown
  · unfold addrTok addrTokG
    icases Htok with ⟨-, Ht⟩
    icases Htok' with ⟨-, Ht'⟩
    iexfalso
    iapply (@token_exclusive GF (netGS (G := hG.goose_globalGS)).allG) $$ Ht Ht'

end lemmas

end Perennial.raxos
