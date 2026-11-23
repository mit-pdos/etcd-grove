/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/getCodec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`getCodec()` (internal to the gob model; its spec here): with a codec registered, it returns it.
-/
module

public import Dsverify.Proof.encoding.gob.Base

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.rpc.RpcKit]

/-- `getCodec()`: with a codec registered, it returns it. -/
abbrev getCodec.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ codecSet (GF := GF) }}
    (App (Val (@! encoding.gob.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFns c }}

theorem getCodec.wp_proof (hst : pkgState.gob = isInit) : getCodec.spec (GF := GF) := by
  wp_start as #Hset
  unfold codecSet
  icases Hset with ⟨%c, %Hc, #Hcp, #Hfns⟩
  ihave ⟨-, -, #Hsync⟩ := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access hst $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr encoding.gob.codec ↦ (null : Loc) ∨ codecSet : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | #Hset')
  · icombine Hnull Hcp gives %Heq
    exact absurd Heq.symm Hc
  unfold codecSet
  icases Hset' with ⟨%c', %Hc', #Hcp', -⟩
  icombine Hcp' Hcp gives %Heq
  subst Heq
  wp_apply sync.Mutex.Unlock.wp_proof (globalAddr encoding.gob.codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
  · unfold codecInv codecSet; iright; iexists c'; iframe Hcp' Hfns; ipureintro; exact Hc
  rw [decide_eq_false Hc]
  wp_auto
  iapply HΦ
  iexact Hfns

end proof

end Perennial.encoding.gob
