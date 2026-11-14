/-
`wire.ReadFull` on an end the calling thread owns (`ReadFull.owned`): its spec
(`NetTcp/Spec/.../wire/ReadFull.lean`) with the reader predicate `P r := ∃ st, tcpEnd .. st r` and the
trivial accessor. A corollary of the spec, for the callers that own their end.
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions] [field_sem : net.FieldAssumptions]

/-- `ReadFull` on an end the calling thread owns: the end's state is the caller's before and
after (`P r := ∃ st, tcpEnd .. st r`). -/
theorem ReadFull.owned (wp_ReadFull : ReadFull.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (buf : GoSlice) (bs0 : List w8)
    (st : TcpEnd) (r : Nat) (sent0 : GoString) (eof : GoInterface) (hsent0 : sent0.length = r) :
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
      tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent0 }}
    (App (App (Val (@! wire.ReadFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (st' : TcpEnd) (r' : Nat) (bs' : List w8),
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r' ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length⌝ ∗
      if ok then ∃ sent : GoString,
        tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent ∗
        ⌜r' = r + bs0.length ∧ sent.length = r' ∧ sent.drop r = bs'⌝
      else True }} := by
  iintro %Φ ⟨#Hc, Hbuf, #Heof, Hend, #Hlb0⟩ HΦ
  iapply wp_ReadFull c cn s a buf bs0
      (fun r => iprop(∃ st, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r)) r
      sent0 eof hsent0 $$ [Hbuf Hend]
  · iframe Hc Hbuf Heof Hlb0
    isplitl [Hend]
    · iexists st
      iexact Hend
    imodintro
    iintro %r0 ⟨%st0, HE⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    iexists st0
    iframe HE
    iintro %st' %r' HE
    imod Hcl
    imodintro
    iexists st'
    iexact HE
  inext
  iintro %ok ⟨%r', %bs', ⟨%st', HE⟩, Hbuf, Hrest⟩
  iapply HΦ
  iexists st', r', bs'
  iframe HE Hbuf Hrest

end proof

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
