/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client group's internal predicates (notes/prove-clientpkg.md).

`readyI`, `replyPI` are what `client.ready`, `client.replyP` (`Spec/client/Defs.lean`) must be
for `Write`/`Read` to be provable (notes/hub-requests.md, HUB-REQUEST 1 and 2): `ready` lacks the
fields `SendProposal` reads (`LeaderId`, `servers`, `Logger`), fixes the writers at "no error,
nothing buffered" (false after a network fault), and lacks `cid ≥ 1`; `replyP` lacks a bound on
the sequence number.

* `wrOk γ γc γm cid w`: one of the client's writers: none, or over a connection of kind
  `client cid`, with a sticky error, or (no error) everything written being whole frames of the
  client's registered proposals, nothing buffered.
* `sendSt γ γc γm cl cid N`: the client struct's fields `SendProposal` reads (persistent
  fields) and its `N` writers.
* `replyPI`: `replyP` with `n < 2 ^ 31`.
* `readyI`: `ready` with the above.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-! Persistence of the slot's facts (unfolds of `Spec/swift/Inv.lean`'s definitions: missing
laws, notes/prove-clientpkg.md). -/

instance cmdIs_persistent (γ : sp.Names) (x : sp.CmdId) (c : sp.Cmd) :
    Persistent (sp.cmdIs γ x c : IProp netDistGF) := by
  unfold sp.cmdIs; infer_instance
instance connKind_persistent (γ : sp.Names) (c : Nat) (k : sp.ConnKind) :
    Persistent (sp.connKind γ c k : IProp netDistGF) := by
  unfold sp.connKind; infer_instance
instance doneRes_persistent (γ : sp.Names) (x : sp.CmdId) (o : List w8) :
    Persistent (sp.doneRes γ x o : IProp netDistGF) := by
  unfold sp.doneRes; infer_instance

instance msgOk_persistent' (γ : sp.Names) (γc γm : GName) (m : sp.Msg) :
    Persistent (sp.msgOk γ γc γm m : IProp netDistGF) := sp.msgOk_persistent m

instance wrAligned_persistent (γ : sp.Names) (γc γm : GName) (cid : w32) (sent : List w8) :
    Persistent (wrAligned γ γc γm cid sent) := by
  unfold wrAligned
  have := fun m => sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm) m
  infer_instance

/-- A delivery token not among those held is of a later reply. -/
theorem toks_fresh (γd : GName) (s n : Nat) :
    toks γd s ∗ ghostMapElem (K := Nat) (V := Unit) γd n (DFrac.own 1) () ⊢ ⌜s ≤ n⌝ := by
  unfold toks
  iintro ⟨Hts, Hn⟩
  by_cases h : s ≤ n
  · ipureintro; exact h
  have hl : (List.range s)[n]? = some n := by rw [List.getElem?_range]; omega
  ihave Hm := (BigSepL.bigSepL_lookup_acc hl).1 $$ Hts
  icases Hm with ⟨Hm, -⟩
  ihave %Hne := ghostMapElem_ne γd n n (DFrac.own 1) () () $$ Hn Hm
  exact absurd rfl Hne

/-- One more token. -/
theorem toks_snoc (γd : GName) (s : Nat) :
    toks γd s ∗ ghostMapElem (K := Nat) (V := Unit) γd s (DFrac.own 1) () ⊢ toks γd (s + 1) := by
  unfold toks
  rw [List.range_succ]
  iintro ⟨Hts, Hn⟩
  iapply BigSepL.bigSepL_snoc.2
  iframe

end defs

end client

end Perennial.github_com.imdea_software.swiftpaxos
