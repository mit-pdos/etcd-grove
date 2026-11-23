/-
The network callees of the kit's own code (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `net`'s
`Dial`, `Listen`, `Listener.Accept`, `Conn.{Read,Write,Close}` (`Net/Spec/net/*`) and `io.ReadFull`
over a connection (`io.ReadFull.specLt`, dsv-rabia's `ConnRead.lean`: the condition asked only of
the reads `io.ReadAtLeast` makes), as hypotheses of the kit's proofs (`SwNetDeps`), linked in
`Link.lean` (CLAUDE.md, "Import tiers": a proof sees its callees through their specs), as
dsv-rabia's `KitNetDeps`; and the kit's own specs its proofs share (`awaitConf.spec`). Also the configuration protocol's address facts the proofs share
(`ownLis`, the start port's protocol laws).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersDefs
public import Dsverify.Proof.rabia.examples.rabianet.ConnRead
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Proof.net.AtAddr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section deps
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions] [io.Assumptions] [π : NetProtoGS]

/-- The network callees of the kit's code (see the file header). -/
structure SwNetDeps : Prop where
  dial : net.Dial.spec (GF := netDistGF) (hG := hG)
  listen : net.Listen.spec (GF := netDistGF) (hG := hG)
  accept : net.Listener.Accept.spec (GF := netDistGF) (hG := hG)
  read : net.Conn.Read.spec (GF := netDistGF) (hG := hG)
  write : net.Conn.Write.spec (GF := netDistGF) (hG := hG)
  close : net.Conn.Close.spec (GF := netDistGF) (hG := hG)
  readFullLt : rabia.examples.rabianet.io.ReadFull.specLt (GF := netDistGF) (hG := hG)

/-- The listener `li` (`l`) at `a`, open, with its address (what `Listen` gives at a valid
address). -/
def ownLis (li : GoInterface) (l : w64) (a : GoString) : IProp netDistGF :=
  iprop(net.isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a)

end deps

section conf
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable [SwiftNetPkgState netDistGF]

/-- `conf.startP` is prefix-closed. -/
theorem conf.startP_closed (γ : SwiftNames netDistGF) : ProtoPrefixClosed (conf.startP γ) where
  nil cid := by
    unfold conf.startP
    iintro !>
    ileft; ipureintro; rfl
  pre cid a b h := by
    unfold conf.startP
    iintro #(%Hb | ⟨%c, #Hc, #Hr, %Hb⟩)
    · iintro !>; ileft; ipureintro; subst Hb; exact List.prefix_nil.mp h
    · iintro !>; iright; iexists c; iframe Hc Hr; ipureintro; exact h.trans Hb

/-- What a client node's start port's reader has read, `confLen` bytes of it: a configuration's
encoding with no change, and every predicted node's registration. -/
theorem conf.startP_full (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.startP γ cid bs ⊢ ∃ c cs, conf.is γ c ∗ sp.allPredsReg γ.sp γ.conf ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ cs = []⌝ := by
  unfold conf.startP
  iintro (%Hb | ⟨%c, #Hc, #Hr, %Hb⟩)
  · subst Hb; simp [confLen, maxChanges] at hl
  · ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    iexists c, []
    iframe Hc Hr
    ipureintro
    refine ⟨?_, Hv, ⟨by simp [maxChanges], by simp⟩, rfl⟩
    exact Hb.eq_of_length (by rw [hl]; exact (Conf.encodeC_length c []).symm)

end conf

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]

/-- `awaitConf(a, ch)` on a configuration port `a` (its protocols `P`, `Q`), with the future
`ch` and the promise to fulfill it with `confMsg γ Ok R`, and `Pre`, which the node turns, with
the first message's `X`, into the acknowledgments' `A` and the caller's `R` (`hclaim`) before the
first acknowledgment: it never returns. -/
abbrev awaitConf.spec : Prop :=
  ∀ (γ : SwiftNames netDistGF) (a : GoString) (ch : Loc) (γf : FutureNames)
    (P Q : Proto netDistGF) (Ok : Conf → List Change → Prop) (Pre A R X : IProp netDistGF),
  ProtoPrefixClosed P →
  (∀ cid bs, bs.length = confLen → P cid bs ⊢ ∃ c cs, conf.is γ c ∗ X ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ Ok c cs⌝) →
  (∀ cid, A ⊢ Q cid [confAck]) →
  (⊢ isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet -∗ Pre -∗ X ={⊤}=∗ □ A ∗ R) →
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      addrProto (Gg := hG.goose_globalGS) a P Q ∗
      isFuture examples.swiftnet.msg γf ch ∗ Fulfill γf (confMsg γ Ok R) ∗ Pre }}
    (App (App (Val (@! examples.swiftnet.awaitConf)) (Val #a)) (Val #ch))
  {{ RET #(); False }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
