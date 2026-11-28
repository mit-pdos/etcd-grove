/-
`Codec()`'s spec (kit.go, notes/dsv-hraft.md, S5): the far side's store's codec, `codecOk (regR g)`,
and the specs of its helpers `flag`, `encStr`, `decStr` (on the encodings it meets).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : Assumptions]

/-- `Out`'s values are injective (each field is read off by a deterministic step). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hF := (Out.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hF' := (Out.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hU'] at hU
  rw [h, hF'] at hF
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eF : Val #x.Found' = Val #y.Found' := (congrFun hF (Val #y.Found')) ▸ rfl
  injection eV with eV
  injection eU with eU
  injection eF with eF
  have eV' := go.intoVal_inj eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eF' := GoGlobalContext.intoVal_inj_bool eF
  cases x; cases y
  simp only at eV' eU' eF'
  subst eV' eU' eF'
  rfl

theorem outVal_inj {u f v u' f' v'} (h : outVal u f v = outVal u' f' v') :
    u = u' ∧ f = f' ∧ v = v' := by
  simp only [outVal, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

theorem encOutV_outVal (u f : Bool) (v : GoString) (hv : v.length < 256) :
    encOutV (outVal u f v) = encOutB u f v := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := outVal_inj (Classical.choose_spec h).2
    rw [← h1, ← h2, ← h3]
  · rename_i h
    exact absurd ⟨(u, f, v), hv, rfl⟩ h

end dec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

/-- A value the codec meets as an output is a short `Out`. -/
theorem outOk_outVal (g : GName) (x : GoInterface)
    (h : RBase.outOk (regR (GF := GF) (Gg := hG.goose_globalGS) g) x) :
    ∃ u f v, v.length < 256 ∧ x = outVal u f v := by
  rcases h with ⟨o, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, o.1.1, o.1.2, o.2, rfl⟩
  · exact ⟨true, false, [], by simp, rfl⟩

/-- `flag(x)`: 1 for true, 0 for false. -/
abbrev flag.spec : Prop :=
  ∀ x : Bool,
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.flag)) (Val #x))
  {{ RET #(if x then W8 1 else W8 0); True }}

/-- `encStr(b, s)`, `s` shorter than 256 bytes: `b` with `s`'s length (a byte) and its bytes appended. -/
abbrev encStr.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (s : GoString), s.length < 256 →
  {{ (b ↦* bs : IProp GF) ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.encStr)) (Val #b)) (Val #s))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ W8 s.length :: s) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

/-- `decStr(b)` on bytes that start with an encoded string `v` (its length, then its bytes): `v`, the
rest (as long as `r`), `true`; `b`'s bytes back. -/
abbrev decStr.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (v r : List w8), v.length < 256 →
  {{ (b ↦*{dq} (W8 v.length :: (v ++ r)) : IProp GF) }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.decStr)) (Val #b))
  {{ (b' : GoSlice), RET (PairV (PairV #v #b') #true); b ↦*{dq} (W8 v.length :: (v ++ r)) ∗
      ⌜sint.Z b'.len = r.length⌝ }}

/-- **`Codec()`**: the far side's store's codec. -/
abbrev Codec.spec : Prop :=
  ∀ g : GName,
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (regR (GF := GF) (Gg := hG.goose_globalGS) g) cd }}

end spec

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
