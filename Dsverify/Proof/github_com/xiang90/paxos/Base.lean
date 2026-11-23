/-
The common base of the proofs of `github.com/xiang90/paxos` (the lab's `Paxos/Proof/Prelude.lean`,
notes/dsv-paxos.md): the package's own post-initialization state (`True`: it has no package-level
variables), and `message`'s `Pos.Countable` (channels of messages keep them in ghost state).
-/
module

public import Dsverify.GeneratedProof.github_com.xiang90.paxos
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.github_com.tchajed.marshal
public import Perennial.Proof.log
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Iris.ProgramLogic.Atomic

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.xiang90.paxos

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.xiang90.paxos :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.xiang90.paxos :=
  build_get_is_pkg_init_wf

end def_

/-- `message`'s `Pos.Countable` (channels of messages keep them in ghost state). -/
instance message_countable [GooseExts] : Pos.Countable message :=
  .ofInjective (fun m => Pos.Countable.encode (m.from', m.to', m.typ', m.n', m.prevn', m.value'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      subst h1 h2 h3 h4 h5 h6; rfl)

end github_com.xiang90.paxos

end Perennial
