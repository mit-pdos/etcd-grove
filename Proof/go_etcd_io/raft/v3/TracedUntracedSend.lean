/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 6 (2026-11-09): the untraced instances of the
rest of the send path, one spec for both modes since slice 6 (`notes/decisions.md`, "Q8 stage 1
(slice 6)"), as `TracedUntraced.lean`'s: each `X.untraced : X.spec → X.untracedTriple`, the statement
before slice 6 (`s.gh.tr = none`, no gate), from the one spec with the gates the struct's nil logger
(`ownRaftPhysC_traceLogger`, `hookGateOpt_none`), `G := emp` and `TrNoSnap none` (`trNoSnap_none`),
for the callers that stay untraced.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.maybeSendAppend.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.maybeSendAppend.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (sendIfEmpty : Bool),
  to ≠ id →
  to ∈ domSet s.progress →
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeSendAppend"))
      (Val #to)) (Val #sendIfEmpty))
  {{ (b : Bool) (ms : List Msg) (pvs : GMap w64 Progress), RET #b;
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.maybeSendAppend.spec`'s untraced instance. -/
theorem raft.maybeSendAppend.untraced (h : raft.maybeSendAppend.spec (GF := GF) (hG := hG)) :
    raft.maybeSendAppend.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s to sie Hto Hcfg Hl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s to sie iprop(emp) Hto Hcfg Hl Htz $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · iintro %mm %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iempintro
    rw [htr]
    iapply trNoSnap_none
  inext
  iintro %b %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %b %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

end untraced

end EtcdGrove
end Perennial
