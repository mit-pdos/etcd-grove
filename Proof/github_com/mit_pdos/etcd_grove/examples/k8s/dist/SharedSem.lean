/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: the semantic model of the store on a shared cluster

`notes/k8s-dist-k4.md` §1. The store's history on the shared cluster linearizes in the driver's model
(`kSpec h0`, linkv's `PendSpec` over a store and its history) with one more silent step, **foreign**:
another writer of the cluster takes a revision, the store's items unchanged (`foreignL`). K8 proves the
real history is a run of this model (`SRun`); K4 proves every such run passes `SharedModel`'s full mode
(`SharedSearch.lean`).

A run takes every step from a configuration whose revision has a successor below `2^64` (`NoWrap`): the
model's revisions are 64-bit words, and the cluster's never wrap.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section go
variable [GooseExts]

/-- **A foreign revision**: the cluster's revision advances by one, the store's items unchanged; the
store at the new revision is appended to the history. -/
def foreignL (h : HSt) : HSt :=
  ⟨⟨h.st.items, h.st.rv + W64 1⟩, h.hist ++ [⟨h.st.items, h.st.rv + W64 1⟩]⟩

/-- A configuration whose revision has a successor (no step from it wraps). -/
def NoWrap (c : GCfg) : Prop := uint.nat c.st.st.rv + 1 < 2 ^ 64

/-- **The semantic model's silent steps**: a pending write takes effect or the pending list is
reordered (`kSpec`'s `PSilent`), or a foreign revision passes; each from a configuration that does not
wrap. -/
inductive SSilent (h0 : HSt) : GCfg → GCfg → Prop where
  | pend {c c' : GCfg} : NoWrap c → linkv.PSilent (kSpec h0) c c' → SSilent h0 c c'
  | foreign (c : GCfg) : NoWrap c → SSilent h0 c ⟨foreignL c.st, c.pend⟩

/-- Any number of silent steps. -/
inductive SReach (h0 : HSt) : GCfg → GCfg → Prop where
  | refl (c : GCfg) : SReach h0 c c
  | step {c c₁ c₂ : GCfg} : SSilent h0 c c₁ → SReach h0 c₁ c₂ → SReach h0 c c₂

/-- **A run of the semantic model**: from `c`, each operation `(x, y)` of `ops` in turn, after silent
steps, takes `kSpec`'s step (`PStep`, the answer `ansOf y`) from a configuration that does not wrap;
`c'` is the configuration after the last. -/
inductive SRun (h0 : HSt) : GCfg → List (Input × Output) → GCfg → Prop where
  | nil (c : GCfg) : SRun h0 c [] c
  | cons {c c₁ c₂ c' : GCfg} {x : Input} {y : Output} {ops : List (Input × Output)} :
      SReach h0 c c₁ → NoWrap c₁ → linkv.PStep (kSpec h0) c₁ x (ansOf y) c₂ → SRun h0 c₂ ops c' →
      SRun h0 c ((x, y) :: ops) c'

/-- The foreign step keeps the items. -/
theorem foreignL_items (h : HSt) : (foreignL h).st.items = h.st.items := rfl

/-- The foreign step's revision, in numbers (no wrap). -/
theorem foreignL_rv (h : HSt) (hw : uint.nat h.st.rv + 1 < 2 ^ 64) :
    uint.nat (foreignL h).st.rv = uint.nat h.st.rv + 1 := by
  simp only [foreignL]; word

theorem SReach.trans {h0 : HSt} {c₁ c₂ c₃ : GCfg} (h₁ : SReach h0 c₁ c₂) (h₂ : SReach h0 c₂ c₃) :
    SReach h0 c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

end go

end k8s_dist
end EtcdGrove
end Perennial
