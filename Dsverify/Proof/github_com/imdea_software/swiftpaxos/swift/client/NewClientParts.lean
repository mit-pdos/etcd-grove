/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/NewClientParts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Parts of `swift.NewClient`'s proof (the change log C6 record of package-state facts on the
client node is in `Proof/client/PkgFacts.lean`): the local form of `sp.clientSeq_pos`, and the split of a connected
replica end into the reader's part (`rdEnd`) and the writer's part (`wrOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleMsgs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.InitCs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Quorum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.PkgFacts

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

open swift.rd


section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-- A client whose sequence number is tracked (`clientSeq`) has an id of at least 1: the law
`sp.clientSeq_pos` (change log C13, HUB-REQUEST 10). -/
theorem clientSeq_pos (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (cl : w32) (s : Nat) :
    sp.inv γ γc γm γl ∗ sp.clientSeq γ cl s ⊢ |={E}=> ⌜1 ≤ cl.toInt⌝ ∗ sp.clientSeq γ cl s := by
  exact sp.clientSeq_pos E hE cl s

end laws

section split
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [net.Assumptions] [net.FieldAssumptions]

/-- A connected replica end: the reader's part and the writer's part. -/
theorem replicaEnd_split (H : HC) (srv : GoInterface) (rd wr : Loc) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      client.replicaEnd H.γ H.γc H.γm H.cid srv rd wr ⊢
      rdEnd H rd ∗ client.wrOk H.γ H.γc H.γm H.cid wr := by
  iintro ⟨#Hnet, Hend⟩
  icases (client.replicaEnd_unfold _ _ _ _ _ _ _).1 $$ Hend with (⟨%Hr, %Hw⟩ | ⟨%c, #Hc, #Hk, Hrd, Hwr⟩)
  · isplitl
    · unfold rdEnd; ileft; ipureintro; exact Hr
    · unfold client.wrOk; ileft; ipureintro; exact Hw
  isplitl [Hrd]
  · unfold rdEnd
    iright
    iexists srv, c
    iframe Hk Hrd
    iapply bufio.readerOk_conn $$ [$Hnet $Hc]
  · unfold client.wrOk
    iright
    iexists srv, c, [], [], interface.nil
    iframe Hc Hk Hwr
    iright
    isplitr
    · ipureintro; rfl
    unfold client.wrAligned
    iexists []
    isplitr
    · ipureintro; simp [sp.framesOf]
    iapply BigSepL.bigSepL_nil.2; iempintro

/-- The replica ends, split. -/
theorem ends_split (H : HC) (srvs : List GoInterface) (rds wrs : List Loc)
    (h1 : rds.length = srvs.length) (h2 : wrs.length = srvs.length) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      ([∗list] i ↦ s ∈ srvs, client.replicaEnd H.γ H.γc H.γm H.cid s (rds.getD i null)
        (wrs.getD i null)) ⊢
      ([∗list] rd ∈ rds, rdEnd H rd) ∗ [∗list] w ∈ wrs, client.wrOk H.γ H.γc H.γm H.cid w := by
  induction srvs generalizing rds wrs with
  | nil =>
    cases rds with
    | cons _ _ => simp at h1
    | nil =>
      cases wrs with
      | cons _ _ => simp at h2
      | nil =>
        iintro -
        isplitl <;> (iapply BigSepL.bigSepL_nil.2; iempintro)
  | cons s srvs ih =>
    cases rds with
    | nil => simp at h1
    | cons r rds =>
      cases wrs with
      | nil => simp at h2
      | cons w wrs =>
        iintro ⟨#Hnet, H⟩
        icases (BigSepL.bigSepL_cons).1 $$ H with ⟨H0, H⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        icases replicaEnd_split H s r w $$ [$Hnet $H0] with ⟨Hr, Hw⟩
        icases ih rds wrs (by simpa using h1) (by simpa using h2) $$ [$Hnet $H] with ⟨Hrs, Hws⟩
        isplitl [Hr Hrs]
        · iapply (BigSepL.bigSepL_cons).2; iframe
        · iapply (BigSepL.bigSepL_cons).2; iframe

end split

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
