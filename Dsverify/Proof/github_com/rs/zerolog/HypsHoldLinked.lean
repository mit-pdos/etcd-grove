/-
zerolog's specs (`Spec.lean`'s class `Hyps`; until dsv-fix4 a premise of rabia's statement)
**hold**, from the per-function proofs and the trust-boundary axioms left (`Logger__*.lean`,
`Event__*.lean`, `ParseLevel.lean`, `SetGlobalLevel.lean`, `New.lean`; since dsv-retire-3 the five
level methods, `Str`, `ParseLevel`, `SetGlobalLevel` and `New` are proved, the level methods over
`Str`'s proof), the event token the fixed `eventTok`
(`EventTok.lean`), the logger fact `loggerOk` (`Spec.lean`, fixed since dsv-fix6). A linking module: rabia's top-level proof discharges the former premise with
`hyps_holds`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Logger__Trace
public import Dsverify.Proof.github_com.rs.zerolog.Logger__Debug
public import Dsverify.Proof.github_com.rs.zerolog.Logger__Info
public import Dsverify.Proof.github_com.rs.zerolog.Logger__Warn
public import Dsverify.Proof.github_com.rs.zerolog.Logger__Error
public import Dsverify.Proof.github_com.rs.zerolog.Event__Str
public import Dsverify.Proof.github_com.rs.zerolog.Event__Int
public import Dsverify.Proof.github_com.rs.zerolog.Event__Ints
public import Dsverify.Proof.github_com.rs.zerolog.Event__Int64
public import Dsverify.Proof.github_com.rs.zerolog.Event__Uint32
public import Dsverify.Proof.github_com.rs.zerolog.Event__Bool
public import Dsverify.Proof.github_com.rs.zerolog.Event__Float64
public import Dsverify.Proof.github_com.rs.zerolog.Event__Msg
public import Dsverify.Proof.github_com.rs.zerolog.ParseLevel
public import Dsverify.Proof.github_com.rs.zerolog.SetGlobalLevel
public import Dsverify.Proof.github_com.rs.zerolog.New
public import Perennial.Proof.unicode.utf8.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- **`zerolog.Hyps` holds** (a theorem, not an instance): the file header. -/
theorem hyps_holds : Hyps GF := by
  refine ⟨⟨eventTok, ?_⟩, ParseLevel.wp_proofWarn, SetGlobalLevel.wp_proof, New.wp_proof⟩
  refine ⟨?_, Event.Str.wp_proof unicode.utf8.wp_DecodeRuneInString, Event.Int.wp_proof, Event.Ints.wp_proof, Event.Int64.wp_proof,
    Event.Uint32.wp_proof, Event.Bool.wp_proof, Event.Float64.wp_proof, Event.Msg.wp_proof⟩
  have wp_Str := Event.Str.wp_proof (GF := GF) unicode.utf8.wp_DecodeRuneInString
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact Logger.Trace.wp_proof wp_Str
  · exact Logger.Debug.wp_proof wp_Str
  · exact Logger.Info.wp_proof wp_Str
  · exact Logger.Warn.wp_proof wp_Str
  · exact Logger.Error.wp_proof wp_Str

end holds

end Perennial.github_com.rs.zerolog
