/-
`service.API.Read`'s spec (the hraft kit's API service, notes/dsv-hraft.md, S6).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.ApiDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `a.Read(args, reply)` (S6): a read of the FSM's state outside the log, in the way `args.Way`
(`WayBarrier`: after a `Barrier`; otherwise `WayVerify`: after a barrier of the current term, then
`VerifyLeader`, the term unchanged), for a read that began after the gprot snapshot `sc`, which covers
the read's registration frontier (of length `n0`), with the read's claim `rdClaim`: `reply.Ok` only
with `Ψ` of the reply's found and value (the register after a committed prefix at least as long as the
registration frontier, `rdClaim`'s premise). Returns nil. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.API.Read.spec : Prop :=
  ∀ (a args reply : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName)
    (way : w64) (n0 : Nat) (sc : Snap) (Ψ : Bool → List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isAPI a γ rc i fc alb ∗ args ↦□ ReadArgs.mk way ∗ reply ↦ (Perennial.zero_val ReadReply) ∗
      histLb γ sc ∗ ⌜n0 ≤ sc.maxDur⌝ ∗ rdClaim γ fc n0 Ψ }}
    (App (App (Val (a @!! go.GoType.PointerType API.ty @!! go!"Read")) (Val #args)) (Val #reply))
  {{ RET #interface.nil; ∃ rep : ReadReply, reply ↦ rep ∗ (⌜rep.Ok' = true⌝ -∗ Ψ rep.Found' rep.V') }}

end spec

end Perennial
