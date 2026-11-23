/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/Decide.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The handler's decision (`handleFastAndSlowAcks`), its ghost core: what the message sets hold
when `MsgSet.Add` calls back (notes/prove-clientpkg.md, "The handler's design") gives the
registered value's `doneRes` through the slot's laws, and the handler mints the reply's delivery
token. Proved over the frozen laws `sp.accept_fast`, `sp.accept_slow`, `sp.reply_agree`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The fast path's certificate: the leader's `MReply` of ballot `b` (checksum `csL`) and
`MFastAckClient`s of `b` of `N / 2` distinct non-leader replicas with checksums `SHashesEq`
the leader's (`fastPathH[x]`'s state when its quorum is reached). -/
def fastCert (γ : sp.Names) (γc γm : GName) (N : Nat) (b : w32) (x : sp.CmdId) : IProp netDistGF :=
  iprop(∃ (rL : w32) (csL : List sp.Hash) (vL : List w8) (acks : List (w32 × List sp.Hash)),
    ⌜(acks.map Prod.fst).Nodup ∧ N / 2 ≤ acks.length ∧
      ∀ a ∈ acks, sp.shashesEq csL a.2 ∧ sp.rid a.1 ≠ sp.leaderOf N (sp.bal b)⌝ ∗
    sp.msgOk γ γc γm (.reply rL b x csL vL) ∗
    [∗list] a ∈ acks, sp.msgOk γ γc γm (.fastAckClient a.1 b x a.2))

/-- The slow path's certificate (`slowPathH[x]`): the leader's `MReply` of `b` and
`MLightSlowAck`s of `b` of `N / 2` distinct non-leader replicas. -/
def slowCert (γ : sp.Names) (γc γm : GName) (N : Nat) (b : w32) (x : sp.CmdId) : IProp netDistGF :=
  iprop(∃ (rL : w32) (csL : List sp.Hash) (vL : List w8) (rs : List w32),
    ⌜rs.Nodup ∧ N / 2 ≤ rs.length ∧ ∀ r ∈ rs, sp.rid r ≠ sp.leaderOf N (sp.bal b)⌝ ∗
    sp.msgOk γ γc γm (.reply rL b x csL vL) ∗
    [∗list] r ∈ rs, sp.msgOk γ γc γm (.lightSlowAck ⟨r, b, x⟩))

/-- **The decision**: either certificate for ballot `b`, and the result `v` the handler stored
for `x` and `b` (`reps[x][b]`, from an `MReply` of `b`): `v` is `x`'s decided result. -/
theorem decide (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName) (N : Nat)
    (fr : Bool) (l : List GoString) (b : w32) (x : sp.CmdId) (rL' : w32) (cs' : List sp.Hash)
    (v : List w8) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
      (fastCert γ γc γm N b x ∨ slowCert γ γc γm N b x) ∗
      sp.msgOk γ γc γm (.reply rL' b x cs' v) ⊢
    |={E}=> sp.doneRes γ x v := by
  iintro ⟨#Hinv, #Hcfg, Hc, #Hrep⟩
  unfold fastCert slowCert
  icases Hc with (⟨%rL, %csL, %vL, %acks, %Hacks, #HL, #Hacks⟩ |
    ⟨%rL, %csL, %vL, %rs, %Hrs, #HL, #Hrs⟩)
  · ihave %Hv := sp.reply_agree rL rL' b x csL cs' vL v $$ [HL Hrep]
    · iframe #
    subst Hv
    iapply sp.accept_fast E hE N fr l rL b x csL vL acks
    iframe #
    ipureintro; exact Hacks
  · ihave %Hv := sp.reply_agree rL rL' b x csL cs' vL v $$ [HL Hrep]
    · iframe #
    subst Hv
    iapply sp.accept_slow E hE N fr l rL b x csL vL rs
    iframe #
    ipureintro; exact Hrs

/-- The handler's delivery tokens: a command not yet delivered (its sequence number not in the
authority's domain) gets its token, once. -/
theorem mint (γd : GName) (D : GMap Nat Unit) (n : Nat) (hn : D.lookup n = none) :
    ⊢ (ghostMapAuth γd 1 D : IProp netDistGF) ==∗
      ghostMapAuth γd 1 (D.insert n ()) ∗ ghostMapElem (K := Nat) (V := Unit) γd n (DFrac.own 1) () :=
  ghost_map_insert n () hn

end lemmas

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
