/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/proxyEnvSet.lean`. Lean-first (no Rocq
counterpart); etcd-dist N5 (`notes/etcd-dist-plan.md` §19). Go's `||` short-circuits: the result is `false` only
when all four reads returned `""`, each read the process's value for the run (`os.Getenv.specEnv`), so the four
`osEnvIs k ""` make `noProxyEnv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.proxyEnvSet
public import Spec.os.GetenvEnv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

theorem proxyEnvSet.wp_proof (wp_Getenv : os.Getenv.specEnv (GF := GF) (hG := hG)) :
    proxyEnvSet.spec (GF := GF) (hG := hG) := by
  wp_start as -
  (try wp_auto)
  wp_apply wp_Getenv as %v1 #H1
  (try wp_auto)
  by_cases h1 : v1 = go!""
  rotate_left
  · rw [decide_eq_false h1]
    (try wp_auto)
    iapply HΦ; (try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]); itrivial
  rw [decide_eq_true h1]
  (try wp_auto)
  wp_apply wp_Getenv as %v2 #H2
  (try wp_auto)
  by_cases h2 : v2 = go!""
  rotate_left
  · rw [decide_eq_false h2]
    (try wp_auto)
    iapply HΦ; (try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]); itrivial
  rw [decide_eq_true h2]
  (try wp_auto)
  wp_apply wp_Getenv as %v3 #H3
  (try wp_auto)
  by_cases h3 : v3 = go!""
  rotate_left
  · rw [decide_eq_false h3]
    (try wp_auto)
    iapply HΦ; (try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]); itrivial
  rw [decide_eq_true h3]
  (try wp_auto)
  wp_apply wp_Getenv as %v4 #H4
  (try wp_auto)
  by_cases h4 : v4 = go!""
  rotate_left
  · rw [decide_eq_false h4]
    (try wp_auto)
    iapply HΦ; (try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]); itrivial
  rw [decide_eq_true h4]
  (try wp_auto)
  subst h1 h2 h3 h4
  iapply HΦ
  try simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  iunfold noProxyEnv
  simp only [proxyEnvKeys]
  iapply BigSepL.bigSepL_cons.2
  isplitr; · iexact H1
  iapply BigSepL.bigSepL_cons.2
  isplitr; · iexact H2
  iapply BigSepL.bigSepL_cons.2
  isplitr; · iexact H3
  iapply BigSepL.bigSepL_cons.2
  isplitr; · iexact H4
  iapply BigSepL.bigSepL_nil.2
  itrivial

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial
